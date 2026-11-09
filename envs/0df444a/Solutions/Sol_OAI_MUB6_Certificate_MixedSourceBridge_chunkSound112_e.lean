-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:37:43.685345+00:00
-- url     : https://prove2.me/submissions/e457219d-43a7-41fa-bc3c-8b684e656914

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1795_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1796_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17738 raw17738Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw17738 raw17738Labels = mixedMoment B raw17738step0 raw17738step0Labels := by
      have hz : ∀ j, raw17738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17738step0 = (fun i j => raw17738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17738step0 raw17738; decide +kernel
      have hl : raw17738step0Labels = raw17738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17738 raw17738Labels permutation346 hz
    mixedMoment B raw17738step0 raw17738step0Labels = mixedMoment B raw17738step1 raw17738step1Labels := by
      have ha : raw17738step1 = (fun i j => raw17738step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17738step1 raw17738step0; decide +kernel
      have hl : raw17738step1Labels = raw17738step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17738step0 raw17738step0Labels permutation44 permutation5
    mixedMoment B raw17738step1 raw17738step1Labels = mixedMoment B raw17738step2 raw17738step2Labels := by
      have ha : raw17738step2 = -raw17738step1 := by apply Matrix.ext; change ∀ i j, raw17738step2 i j = -(raw17738step1 i j); unfold raw17738step2 raw17738step1; decide +kernel
      have hl : raw17738step2Labels = raw17738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17738step2 raw17738step2Labels = mixedMoment B raw17738step3 raw17738step3Labels := by
      have ha : raw17738step3 = raw17738step2 := by apply Matrix.ext; unfold raw17738step3 raw17738step2; decide +kernel
      have hl : raw17738step2Labels = labelEmbedding1 ∘ raw17738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17738step2 raw17738step2Labels raw17738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical17743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17743 raw17743Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw17743 raw17743Labels = mixedMoment B raw17743step0 raw17743step0Labels := by
      have ha : raw17743step0 = (fun i j => raw17743 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17743step0 raw17743; decide +kernel
      have hl : raw17743step0Labels = raw17743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17743 raw17743Labels permutation226 permutation5
    mixedMoment B raw17743step0 raw17743step0Labels = mixedMoment B raw17743step1 raw17743step1Labels := by
      have ha : raw17743step1 = -raw17743step0 := by apply Matrix.ext; change ∀ i j, raw17743step1 i j = -(raw17743step0 i j); unfold raw17743step1 raw17743step0; decide +kernel
      have hl : raw17743step1Labels = raw17743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17743step1 raw17743step1Labels = mixedMoment B raw17743step2 raw17743step2Labels := by
      have ha : raw17743step2 = raw17743step1 := by apply Matrix.ext; unfold raw17743step2 raw17743step1; decide +kernel
      have hl : raw17743step1Labels = labelEmbedding1 ∘ raw17743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17743step1 raw17743step1Labels raw17743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical17748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17748 raw17748Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw17748 raw17748Labels = mixedMoment B raw17748step0 raw17748step0Labels := by
      have hz : ∀ j, raw17748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17748step0 = (fun i j => raw17748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17748step0 raw17748; decide +kernel
      have hl : raw17748step0Labels = raw17748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17748 raw17748Labels permutation346 hz
    mixedMoment B raw17748step0 raw17748step0Labels = mixedMoment B raw17748step1 raw17748step1Labels := by
      have ha : raw17748step1 = (fun i j => raw17748step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17748step1 raw17748step0; decide +kernel
      have hl : raw17748step1Labels = raw17748step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17748step0 raw17748step0Labels permutation45 permutation5
    mixedMoment B raw17748step1 raw17748step1Labels = mixedMoment B raw17748step2 raw17748step2Labels := by
      have ha : raw17748step2 = -raw17748step1 := by apply Matrix.ext; change ∀ i j, raw17748step2 i j = -(raw17748step1 i j); unfold raw17748step2 raw17748step1; decide +kernel
      have hl : raw17748step2Labels = raw17748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17748step2 raw17748step2Labels = mixedMoment B raw17748step3 raw17748step3Labels := by
      have ha : raw17748step3 = raw17748step2 := by apply Matrix.ext; unfold raw17748step3 raw17748step2; decide +kernel
      have hl : raw17748step2Labels = labelEmbedding1 ∘ raw17748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17748step2 raw17748step2Labels raw17748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical17754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17754 raw17754Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw17754 raw17754Labels = mixedMoment B raw17754step0 raw17754step0Labels := by
      have hz : ∀ j, raw17754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17754step0 = (fun i j => raw17754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17754step0 raw17754; decide +kernel
      have hl : raw17754step0Labels = raw17754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17754 raw17754Labels permutation346 hz
    mixedMoment B raw17754step0 raw17754step0Labels = mixedMoment B raw17754step1 raw17754step1Labels := by
      have ha : raw17754step1 = (fun i j => raw17754step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17754step1 raw17754step0; decide +kernel
      have hl : raw17754step1Labels = raw17754step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17754step0 raw17754step0Labels permutation126 permutation7
    mixedMoment B raw17754step1 raw17754step1Labels = mixedMoment B raw17754step2 raw17754step2Labels := by
      have ha : raw17754step2 = raw17754step1 := by apply Matrix.ext; unfold raw17754step2 raw17754step1; decide +kernel
      have hl : raw17754step1Labels = labelEmbedding1 ∘ raw17754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17754step1 raw17754step1Labels raw17754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical17755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17755 raw17755Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw17755 raw17755Labels = mixedMoment B raw17755step0 raw17755step0Labels := by
      have ha : raw17755step0 = (fun i j => raw17755 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17755step0 raw17755; decide +kernel
      have hl : raw17755step0Labels = raw17755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17755 raw17755Labels permutation584 permutation7
    mixedMoment B raw17755step0 raw17755step0Labels = mixedMoment B raw17755step1 raw17755step1Labels := by
      have ha : raw17755step1 = raw17755step0 := by apply Matrix.ext; unfold raw17755step1 raw17755step0; decide +kernel
      have hl : raw17755step0Labels = labelEmbedding1 ∘ raw17755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17755step0 raw17755step0Labels raw17755step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical17756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17756 raw17756Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw17756 raw17756Labels = mixedMoment B raw17756step0 raw17756step0Labels := by
      have hz : ∀ j, raw17756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17756step0 = (fun i j => raw17756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17756step0 raw17756; decide +kernel
      have hl : raw17756step0Labels = raw17756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17756 raw17756Labels permutation346 hz
    mixedMoment B raw17756step0 raw17756step0Labels = mixedMoment B raw17756step1 raw17756step1Labels := by
      have ha : raw17756step1 = (fun i j => raw17756step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17756step1 raw17756step0; decide +kernel
      have hl : raw17756step1Labels = raw17756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17756step0 raw17756step0Labels permutation125 permutation7
    mixedMoment B raw17756step1 raw17756step1Labels = mixedMoment B raw17756step2 raw17756step2Labels := by
      have ha : raw17756step2 = raw17756step1 := by apply Matrix.ext; unfold raw17756step2 raw17756step1; decide +kernel
      have hl : raw17756step1Labels = labelEmbedding1 ∘ raw17756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17756step1 raw17756step1Labels raw17756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

theorem canonical17757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17757 raw17757Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw17757 raw17757Labels = mixedMoment B raw17757step0 raw17757step0Labels := by
      have hz : ∀ j, raw17757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17757step0 = (fun i j => raw17757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17757step0 raw17757; decide +kernel
      have hl : raw17757step0Labels = raw17757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17757 raw17757Labels permutation346 hz
    mixedMoment B raw17757step0 raw17757step0Labels = mixedMoment B raw17757step1 raw17757step1Labels := by
      have ha : raw17757step1 = (fun i j => raw17757step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17757step1 raw17757step0; decide +kernel
      have hl : raw17757step1Labels = raw17757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17757step0 raw17757step0Labels permutation127 permutation7
    mixedMoment B raw17757step1 raw17757step1Labels = mixedMoment B raw17757step2 raw17757step2Labels := by
      have ha : raw17757step2 = raw17757step1 := by apply Matrix.ext; unfold raw17757step2 raw17757step1; decide +kernel
      have hl : raw17757step1Labels = labelEmbedding1 ∘ raw17757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17757step1 raw17757step1Labels raw17757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical17758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17758 raw17758Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw17758 raw17758Labels = mixedMoment B raw17758step0 raw17758step0Labels := by
      have hz : ∀ j, raw17758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17758step0 = (fun i j => raw17758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17758step0 raw17758; decide +kernel
      have hl : raw17758step0Labels = raw17758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17758 raw17758Labels permutation346 hz
    mixedMoment B raw17758step0 raw17758step0Labels = mixedMoment B raw17758step1 raw17758step1Labels := by
      have ha : raw17758step1 = (fun i j => raw17758step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17758step1 raw17758step0; decide +kernel
      have hl : raw17758step1Labels = raw17758step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17758step0 raw17758step0Labels permutation143 permutation5
    mixedMoment B raw17758step1 raw17758step1Labels = mixedMoment B raw17758step2 raw17758step2Labels := by
      have ha : raw17758step2 = raw17758step1 := by apply Matrix.ext; unfold raw17758step2 raw17758step1; decide +kernel
      have hl : raw17758step1Labels = labelEmbedding1 ∘ raw17758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17758step1 raw17758step1Labels raw17758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical24400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24400 raw24400Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24400 raw24400Labels = mixedMoment B raw24400step0 raw24400step0Labels := by
      have hz : ∀ j, raw24400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24400step0 = (fun i j => raw24400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24400step0 raw24400; decide +kernel
      have hl : raw24400step0Labels = raw24400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400 raw24400Labels permutation346 hz
    mixedMoment B raw24400step0 raw24400step0Labels = mixedMoment B raw24400step1 raw24400step1Labels := by
      have hz : ∀ j, raw24400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24400step1 = (fun i j => raw24400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24400step1 raw24400step0; decide +kernel
      have hl : raw24400step1Labels = raw24400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400step0 raw24400step0Labels permutation56 hz
    mixedMoment B raw24400step1 raw24400step1Labels = mixedMoment B raw24400step2 raw24400step2Labels := by
      have ha : raw24400step2 = (fun i j => raw24400step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24400step2 raw24400step1; decide +kernel
      have hl : raw24400step2Labels = raw24400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24400step1 raw24400step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27816 raw27816Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw27816 raw27816Labels = mixedMoment B raw27816step0 raw27816step0Labels := by
      have hz : ∀ j, raw27816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27816step0 = (fun i j => raw27816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27816step0 raw27816; decide +kernel
      have hl : raw27816step0Labels = raw27816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27816 raw27816Labels permutation346 hz
    mixedMoment B raw27816step0 raw27816step0Labels = mixedMoment B raw27816step1 raw27816step1Labels := by
      have ha : raw27816step1 = (fun i j => raw27816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27816step1 raw27816step0; decide +kernel
      have hl : raw27816step1Labels = raw27816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27816step0 raw27816step0Labels permutation34 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical27823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27823 raw27823Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw27823 raw27823Labels = mixedMoment B raw27823step0 raw27823step0Labels := by
      have hz : ∀ j, raw27823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27823step0 = (fun i j => raw27823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27823step0 raw27823; decide +kernel
      have hl : raw27823step0Labels = raw27823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27823 raw27823Labels permutation346 hz
    mixedMoment B raw27823step0 raw27823step0Labels = mixedMoment B raw27823step1 raw27823step1Labels := by
      have ha : raw27823step1 = (fun i j => raw27823step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27823step1 raw27823step0; decide +kernel
      have hl : raw27823step1Labels = raw27823step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27823step0 raw27823step0Labels permutation122 permutation0
    mixedMoment B raw27823step1 raw27823step1Labels = mixedMoment B raw27823step2 raw27823step2Labels := by
      have ha : raw27823step2 = -raw27823step1 := by apply Matrix.ext; change ∀ i j, raw27823step2 i j = -(raw27823step1 i j); unfold raw27823step2 raw27823step1; decide +kernel
      have hl : raw27823step2Labels = raw27823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical27825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27825 raw27825Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw27825 raw27825Labels = mixedMoment B raw27825step0 raw27825step0Labels := by
      have hz : ∀ j, raw27825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27825step0 = (fun i j => raw27825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27825step0 raw27825; decide +kernel
      have hl : raw27825step0Labels = raw27825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27825 raw27825Labels permutation346 hz
    mixedMoment B raw27825step0 raw27825step0Labels = mixedMoment B raw27825step1 raw27825step1Labels := by
      have ha : raw27825step1 = (fun i j => raw27825step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27825step1 raw27825step0; decide +kernel
      have hl : raw27825step1Labels = raw27825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27825step0 raw27825step0Labels permutation151 permutation2
    mixedMoment B raw27825step1 raw27825step1Labels = mixedMoment B raw27825step2 raw27825step2Labels := by
      have ha : raw27825step2 = -raw27825step1 := by apply Matrix.ext; change ∀ i j, raw27825step2 i j = -(raw27825step1 i j); unfold raw27825step2 raw27825step1; decide +kernel
      have hl : raw27825step2Labels = raw27825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2802 node2802Labels := by rfl

theorem canonical27827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27827 raw27827Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw27827 raw27827Labels = mixedMoment B raw27827step0 raw27827step0Labels := by
      have hz : ∀ j, raw27827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27827step0 = (fun i j => raw27827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27827step0 raw27827; decide +kernel
      have hl : raw27827step0Labels = raw27827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27827 raw27827Labels permutation346 hz
    mixedMoment B raw27827step0 raw27827step0Labels = mixedMoment B raw27827step1 raw27827step1Labels := by
      have ha : raw27827step1 = (fun i j => raw27827step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27827step1 raw27827step0; decide +kernel
      have hl : raw27827step1Labels = raw27827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27827step0 raw27827step0Labels permutation33 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29313 raw29313Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29313 raw29313Labels = mixedMoment B raw29313step0 raw29313step0Labels := by
      have hz : ∀ j, raw29313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29313step0 = (fun i j => raw29313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29313step0 raw29313; decide +kernel
      have hl : raw29313step0Labels = raw29313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29313 raw29313Labels permutation346 hz
    mixedMoment B raw29313step0 raw29313step0Labels = mixedMoment B raw29313step1 raw29313step1Labels := by
      have ha : raw29313step1 = (fun i j => raw29313step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29313step1 raw29313step0; decide +kernel
      have hl : raw29313step1Labels = raw29313step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29313step0 raw29313step0Labels permutation34 permutation4
    mixedMoment B raw29313step1 raw29313step1Labels = mixedMoment B raw29313step2 raw29313step2Labels := by
      have ha : raw29313step2 = -raw29313step1 := by apply Matrix.ext; change ∀ i j, raw29313step2 i j = -(raw29313step1 i j); unfold raw29313step2 raw29313step1; decide +kernel
      have hl : raw29313step2Labels = raw29313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical29319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29319 raw29319Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29319 raw29319Labels = mixedMoment B raw29319step0 raw29319step0Labels := by
      have hz : ∀ j, raw29319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29319step0 = (fun i j => raw29319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29319step0 raw29319; decide +kernel
      have hl : raw29319step0Labels = raw29319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319 raw29319Labels permutation434 hz
    mixedMoment B raw29319step0 raw29319step0Labels = mixedMoment B raw29319step1 raw29319step1Labels := by
      have hz : ∀ j, raw29319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29319step1 = (fun i j => raw29319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29319step1 raw29319step0; decide +kernel
      have hl : raw29319step1Labels = raw29319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319step0 raw29319step0Labels permutation80 hz
    mixedMoment B raw29319step1 raw29319step1Labels = mixedMoment B raw29319step2 raw29319step2Labels := by
      have ha : raw29319step2 = -raw29319step1 := by apply Matrix.ext; change ∀ i j, raw29319step2 i j = -(raw29319step1 i j); unfold raw29319step2 raw29319step1; decide +kernel
      have hl : raw29319step2Labels = raw29319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical29330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29330 raw29330Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw29330 raw29330Labels = mixedMoment B raw29330step0 raw29330step0Labels := by
      have ha : raw29330step0 = (fun i j => raw29330 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29330step0 raw29330; decide +kernel
      have hl : raw29330step0Labels = raw29330Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29330 raw29330Labels permutation584 permutation2
    _ = mixedMoment B node2396 node2396Labels := by rfl

theorem canonical29353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29353 raw29353Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw29353 raw29353Labels = mixedMoment B raw29353step0 raw29353step0Labels := by
      have hz : ∀ j, raw29353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29353step0 = (fun i j => raw29353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29353step0 raw29353; decide +kernel
      have hl : raw29353step0Labels = raw29353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29353 raw29353Labels permutation346 hz
    mixedMoment B raw29353step0 raw29353step0Labels = mixedMoment B raw29353step1 raw29353step1Labels := by
      have ha : raw29353step1 = (fun i j => raw29353step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29353step1 raw29353step0; decide +kernel
      have hl : raw29353step1Labels = raw29353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29353step0 raw29353step0Labels permutation126 permutation2
    _ = mixedMoment B node2401 node2401Labels := by rfl

theorem canonical29391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29391 raw29391Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29391 raw29391Labels = mixedMoment B raw29391step0 raw29391step0Labels := by
      have hz : ∀ j, raw29391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29391step0 = (fun i j => raw29391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29391step0 raw29391; decide +kernel
      have hl : raw29391step0Labels = raw29391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29391 raw29391Labels permutation346 hz
    mixedMoment B raw29391step0 raw29391step0Labels = mixedMoment B raw29391step1 raw29391step1Labels := by
      have ha : raw29391step1 = (fun i j => raw29391step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29391step1 raw29391step0; decide +kernel
      have hl : raw29391step1Labels = raw29391step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29391step0 raw29391step0Labels permutation39 permutation2
    mixedMoment B raw29391step1 raw29391step1Labels = mixedMoment B raw29391step2 raw29391step2Labels := by
      have ha : raw29391step2 = -raw29391step1 := by apply Matrix.ext; change ∀ i j, raw29391step2 i j = -(raw29391step1 i j); unfold raw29391step2 raw29391step1; decide +kernel
      have hl : raw29391step2Labels = raw29391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29450 raw29450Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29450 raw29450Labels = mixedMoment B raw29450step0 raw29450step0Labels := by
      have hz : ∀ j, raw29450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29450step0 = (fun i j => raw29450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29450step0 raw29450; decide +kernel
      have hl : raw29450step0Labels = raw29450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29450 raw29450Labels permutation434 hz
    mixedMoment B raw29450step0 raw29450step0Labels = mixedMoment B raw29450step1 raw29450step1Labels := by
      have ha : raw29450step1 = (fun i j => raw29450step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29450step1 raw29450step0; decide +kernel
      have hl : raw29450step1Labels = raw29450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29450step0 raw29450step0Labels permutation36 permutation2
    mixedMoment B raw29450step1 raw29450step1Labels = mixedMoment B raw29450step2 raw29450step2Labels := by
      have ha : raw29450step2 = -raw29450step1 := by apply Matrix.ext; change ∀ i j, raw29450step2 i j = -(raw29450step1 i j); unfold raw29450step2 raw29450step1; decide +kernel
      have hl : raw29450step2Labels = raw29450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical29451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29451 raw29451Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw29451 raw29451Labels = mixedMoment B raw29451step0 raw29451step0Labels := by
      have hz : ∀ j, raw29451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29451step0 = (fun i j => raw29451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29451step0 raw29451; decide +kernel
      have hl : raw29451step0Labels = raw29451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29451 raw29451Labels permutation434 hz
    mixedMoment B raw29451step0 raw29451step0Labels = mixedMoment B raw29451step1 raw29451step1Labels := by
      have ha : raw29451step1 = (fun i j => raw29451step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29451step1 raw29451step0; decide +kernel
      have hl : raw29451step1Labels = raw29451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29451step0 raw29451step0Labels permutation40 permutation4
    mixedMoment B raw29451step1 raw29451step1Labels = mixedMoment B raw29451step2 raw29451step2Labels := by
      have ha : raw29451step2 = -raw29451step1 := by apply Matrix.ext; change ∀ i j, raw29451step2 i j = -(raw29451step1 i j); unfold raw29451step2 raw29451step1; decide +kernel
      have hl : raw29451step2Labels = raw29451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical29454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29454 raw29454Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29454 raw29454Labels = mixedMoment B raw29454step0 raw29454step0Labels := by
      have hz : ∀ j, raw29454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29454step0 = (fun i j => raw29454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29454step0 raw29454; decide +kernel
      have hl : raw29454step0Labels = raw29454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29454 raw29454Labels permutation434 hz
    mixedMoment B raw29454step0 raw29454step0Labels = mixedMoment B raw29454step1 raw29454step1Labels := by
      have ha : raw29454step1 = (fun i j => raw29454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29454step1 raw29454step0; decide +kernel
      have hl : raw29454step1Labels = raw29454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29454step0 raw29454step0Labels permutation38 permutation4
    mixedMoment B raw29454step1 raw29454step1Labels = mixedMoment B raw29454step2 raw29454step2Labels := by
      have ha : raw29454step2 = -raw29454step1 := by apply Matrix.ext; change ∀ i j, raw29454step2 i j = -(raw29454step1 i j); unfold raw29454step2 raw29454step1; decide +kernel
      have hl : raw29454step2Labels = raw29454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical29476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29476 raw29476Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw29476 raw29476Labels = mixedMoment B raw29476step0 raw29476step0Labels := by
      have ha : raw29476step0 = (fun i j => raw29476 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29476step0 raw29476; decide +kernel
      have hl : raw29476step0Labels = raw29476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29476 raw29476Labels permutation159 permutation2
    mixedMoment B raw29476step0 raw29476step0Labels = mixedMoment B raw29476step1 raw29476step1Labels := by
      have ha : raw29476step1 = -raw29476step0 := by apply Matrix.ext; change ∀ i j, raw29476step1 i j = -(raw29476step0 i j); unfold raw29476step1 raw29476step0; decide +kernel
      have hl : raw29476step1Labels = raw29476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

theorem canonical29496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29496 raw29496Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw29496 raw29496Labels = mixedMoment B raw29496step0 raw29496step0Labels := by
      have hz : ∀ j, raw29496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29496step0 = (fun i j => raw29496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29496step0 raw29496; decide +kernel
      have hl : raw29496step0Labels = raw29496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29496 raw29496Labels permutation434 hz
    mixedMoment B raw29496step0 raw29496step0Labels = mixedMoment B raw29496step1 raw29496step1Labels := by
      have ha : raw29496step1 = (fun i j => raw29496step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29496step1 raw29496step0; decide +kernel
      have hl : raw29496step1Labels = raw29496step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29496step0 raw29496step0Labels permutation38 permutation4
    mixedMoment B raw29496step1 raw29496step1Labels = mixedMoment B raw29496step2 raw29496step2Labels := by
      have ha : raw29496step2 = -raw29496step1 := by apply Matrix.ext; change ∀ i j, raw29496step2 i j = -(raw29496step1 i j); unfold raw29496step2 raw29496step1; decide +kernel
      have hl : raw29496step2Labels = raw29496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3542 node3542Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29698 raw29698Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw29698 raw29698Labels = mixedMoment B raw29698step0 raw29698step0Labels := by
      have hz : ∀ j, raw29698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29698step0 = (fun i j => raw29698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29698step0 raw29698; decide +kernel
      have hl : raw29698step0Labels = raw29698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698 raw29698Labels permutation434 hz
    mixedMoment B raw29698step0 raw29698step0Labels = mixedMoment B raw29698step1 raw29698step1Labels := by
      have hz : ∀ j, raw29698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29698step1 = (fun i j => raw29698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29698step1 raw29698step0; decide +kernel
      have hl : raw29698step1Labels = raw29698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698step0 raw29698step0Labels permutation80 hz
    mixedMoment B raw29698step1 raw29698step1Labels = mixedMoment B raw29698step2 raw29698step2Labels := by
      have ha : raw29698step2 = (fun i j => raw29698step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29698step2 raw29698step1; decide +kernel
      have hl : raw29698step2Labels = raw29698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29698step1 raw29698step1Labels permutation9 permutation2
    mixedMoment B raw29698step2 raw29698step2Labels = mixedMoment B raw29698step3 raw29698step3Labels := by
      have ha : raw29698step3 = -raw29698step2 := by apply Matrix.ext; change ∀ i j, raw29698step3 i j = -(raw29698step2 i j); unfold raw29698step3 raw29698step2; decide +kernel
      have hl : raw29698step3Labels = raw29698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical29700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29700 raw29700Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw29700 raw29700Labels = mixedMoment B raw29700step0 raw29700step0Labels := by
      have hz : ∀ j, raw29700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29700step0 = (fun i j => raw29700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29700step0 raw29700; decide +kernel
      have hl : raw29700step0Labels = raw29700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29700 raw29700Labels permutation346 hz
    _ = mixedMoment B node1171 node1171Labels := by rfl

theorem canonical29701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29701 raw29701Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw29701 raw29701Labels = mixedMoment B raw29701step0 raw29701step0Labels := by
      have hz : ∀ j, raw29701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29701step0 = (fun i j => raw29701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29701step0 raw29701; decide +kernel
      have hl : raw29701step0Labels = raw29701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29701 raw29701Labels permutation346 hz
    _ = mixedMoment B node2362 node2362Labels := by rfl

theorem canonical29702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29702 raw29702Labels = mixedMoment B node2529 node2529Labels := by
  calc
    _ = mixedMoment B node2529 node2529Labels := by rfl

theorem canonical29703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29703 raw29703Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw29703 raw29703Labels = mixedMoment B raw29703step0 raw29703step0Labels := by
      have hz : ∀ j, raw29703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29703step0 = (fun i j => raw29703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29703step0 raw29703; decide +kernel
      have hl : raw29703step0Labels = raw29703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29703 raw29703Labels permutation346 hz
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical29704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29704 raw29704Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw29704 raw29704Labels = mixedMoment B raw29704step0 raw29704step0Labels := by
      have hz : ∀ j, raw29704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29704step0 = (fun i j => raw29704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29704step0 raw29704; decide +kernel
      have hl : raw29704step0Labels = raw29704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29704 raw29704Labels permutation346 hz
    mixedMoment B raw29704step0 raw29704step0Labels = mixedMoment B raw29704step1 raw29704step1Labels := by
      have ha : raw29704step1 = (fun i j => raw29704step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29704step1 raw29704step0; decide +kernel
      have hl : raw29704step1Labels = raw29704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29704step0 raw29704step0Labels permutation33 permutation2
    _ = mixedMoment B node2600 node2600Labels := by rfl

theorem canonical29705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29705 raw29705Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw29705 raw29705Labels = mixedMoment B raw29705step0 raw29705step0Labels := by
      have hz : ∀ j, raw29705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29705step0 = (fun i j => raw29705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29705step0 raw29705; decide +kernel
      have hl : raw29705step0Labels = raw29705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29705 raw29705Labels permutation346 hz
    mixedMoment B raw29705step0 raw29705step0Labels = mixedMoment B raw29705step1 raw29705step1Labels := by
      have ha : raw29705step1 = (fun i j => raw29705step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29705step1 raw29705step0; decide +kernel
      have hl : raw29705step1Labels = raw29705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29705step0 raw29705step0Labels permutation125 permutation2
    mixedMoment B raw29705step1 raw29705step1Labels = mixedMoment B raw29705step2 raw29705step2Labels := by
      have ha : raw29705step2 = -raw29705step1 := by apply Matrix.ext; change ∀ i j, raw29705step2 i j = -(raw29705step1 i j); unfold raw29705step2 raw29705step1; decide +kernel
      have hl : raw29705step2Labels = raw29705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

theorem canonical29706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29706 raw29706Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29706 raw29706Labels = mixedMoment B raw29706step0 raw29706step0Labels := by
      have hz : ∀ j, raw29706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29706step0 = (fun i j => raw29706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29706step0 raw29706; decide +kernel
      have hl : raw29706step0Labels = raw29706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29706 raw29706Labels permutation346 hz
    mixedMoment B raw29706step0 raw29706step0Labels = mixedMoment B raw29706step1 raw29706step1Labels := by
      have ha : raw29706step1 = (fun i j => raw29706step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29706step1 raw29706step0; decide +kernel
      have hl : raw29706step1Labels = raw29706step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29706step0 raw29706step0Labels permutation39 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical29707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29707 raw29707Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw29707 raw29707Labels = mixedMoment B raw29707step0 raw29707step0Labels := by
      have ha : raw29707step0 = (fun i j => raw29707 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29707step0 raw29707; decide +kernel
      have hl : raw29707step0Labels = raw29707Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29707 raw29707Labels permutation159 permutation2
    _ = mixedMoment B node2892 node2892Labels := by rfl

theorem canonical29708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29708 raw29708Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29708 raw29708Labels = mixedMoment B raw29708step0 raw29708step0Labels := by
      have hz : ∀ j, raw29708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29708step0 = (fun i j => raw29708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29708step0 raw29708; decide +kernel
      have hl : raw29708step0Labels = raw29708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29708 raw29708Labels permutation346 hz
    mixedMoment B raw29708step0 raw29708step0Labels = mixedMoment B raw29708step1 raw29708step1Labels := by
      have ha : raw29708step1 = (fun i j => raw29708step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29708step1 raw29708step0; decide +kernel
      have hl : raw29708step1Labels = raw29708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29708step0 raw29708step0Labels permutation33 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical29709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29709 raw29709Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw29709 raw29709Labels = mixedMoment B raw29709step0 raw29709step0Labels := by
      have hz : ∀ j, raw29709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29709step0 = (fun i j => raw29709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29709step0 raw29709; decide +kernel
      have hl : raw29709step0Labels = raw29709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29709 raw29709Labels permutation346 hz
    mixedMoment B raw29709step0 raw29709step0Labels = mixedMoment B raw29709step1 raw29709step1Labels := by
      have ha : raw29709step1 = (fun i j => raw29709step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29709step1 raw29709step0; decide +kernel
      have hl : raw29709step1Labels = raw29709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29709step0 raw29709step0Labels permutation125 permutation2
    mixedMoment B raw29709step1 raw29709step1Labels = mixedMoment B raw29709step2 raw29709step2Labels := by
      have ha : raw29709step2 = -raw29709step1 := by apply Matrix.ext; change ∀ i j, raw29709step2 i j = -(raw29709step1 i j); unfold raw29709step2 raw29709step1; decide +kernel
      have hl : raw29709step2Labels = raw29709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical29710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29710 raw29710Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw29710 raw29710Labels = mixedMoment B raw29710step0 raw29710step0Labels := by
      have hz : ∀ j, raw29710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29710step0 = (fun i j => raw29710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29710step0 raw29710; decide +kernel
      have hl : raw29710step0Labels = raw29710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29710 raw29710Labels permutation346 hz
    _ = mixedMoment B node2899 node2899Labels := by rfl

theorem canonical29711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29711 raw29711Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw29711 raw29711Labels = mixedMoment B raw29711step0 raw29711step0Labels := by
      have hz : ∀ j, raw29711 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29711step0 = (fun i j => raw29711 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29711step0 raw29711; decide +kernel
      have hl : raw29711step0Labels = raw29711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29711 raw29711Labels permutation590 hz
    mixedMoment B raw29711step0 raw29711step0Labels = mixedMoment B raw29711step1 raw29711step1Labels := by
      have hz : ∀ j, raw29711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29711step1 = (fun i j => raw29711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29711step1 raw29711step0; decide +kernel
      have hl : raw29711step1Labels = raw29711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29711step0 raw29711step0Labels permutation80 hz
    mixedMoment B raw29711step1 raw29711step1Labels = mixedMoment B raw29711step2 raw29711step2Labels := by
      have ha : raw29711step2 = (fun i j => raw29711step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29711step2 raw29711step1; decide +kernel
      have hl : raw29711step2Labels = raw29711step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29711step1 raw29711step1Labels permutation26 permutation0
    mixedMoment B raw29711step2 raw29711step2Labels = mixedMoment B raw29711step3 raw29711step3Labels := by
      have ha : raw29711step3 = -raw29711step2 := by apply Matrix.ext; change ∀ i j, raw29711step3 i j = -(raw29711step2 i j); unfold raw29711step3 raw29711step2; decide +kernel
      have hl : raw29711step3Labels = raw29711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical29712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29712 raw29712Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw29712 raw29712Labels = mixedMoment B raw29712step0 raw29712step0Labels := by
      have hz : ∀ j, raw29712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29712step0 = (fun i j => raw29712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29712step0 raw29712; decide +kernel
      have hl : raw29712step0Labels = raw29712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29712 raw29712Labels permutation346 hz
    mixedMoment B raw29712step0 raw29712step0Labels = mixedMoment B raw29712step1 raw29712step1Labels := by
      have ha : raw29712step1 = (fun i j => raw29712step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29712step1 raw29712step0; decide +kernel
      have hl : raw29712step1Labels = raw29712step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29712step0 raw29712step0Labels permutation127 permutation2
    _ = mixedMoment B node2399 node2399Labels := by rfl

theorem canonical29713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29713 raw29713Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw29713 raw29713Labels = mixedMoment B raw29713step0 raw29713step0Labels := by
      have hz : ∀ j, raw29713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29713step0 = (fun i j => raw29713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29713step0 raw29713; decide +kernel
      have hl : raw29713step0Labels = raw29713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29713 raw29713Labels permutation346 hz
    mixedMoment B raw29713step0 raw29713step0Labels = mixedMoment B raw29713step1 raw29713step1Labels := by
      have ha : raw29713step1 = (fun i j => raw29713step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29713step1 raw29713step0; decide +kernel
      have hl : raw29713step1Labels = raw29713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29713step0 raw29713step0Labels permutation124 permutation2
    _ = mixedMoment B node2405 node2405Labels := by rfl

theorem canonical29714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29714 raw29714Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw29714 raw29714Labels = mixedMoment B raw29714step0 raw29714step0Labels := by
      have hz : ∀ j, raw29714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29714step0 = (fun i j => raw29714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29714step0 raw29714; decide +kernel
      have hl : raw29714step0Labels = raw29714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29714 raw29714Labels permutation346 hz
    mixedMoment B raw29714step0 raw29714step0Labels = mixedMoment B raw29714step1 raw29714step1Labels := by
      have ha : raw29714step1 = (fun i j => raw29714step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29714step1 raw29714step0; decide +kernel
      have hl : raw29714step1Labels = raw29714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29714step0 raw29714step0Labels permutation127 permutation2
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical29787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29787 raw29787Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw29787 raw29787Labels = mixedMoment B raw29787step0 raw29787step0Labels := by
      have hz : ∀ j, raw29787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29787step0 = (fun i j => raw29787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29787step0 raw29787; decide +kernel
      have hl : raw29787step0Labels = raw29787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29787 raw29787Labels permutation346 hz
    mixedMoment B raw29787step0 raw29787step0Labels = mixedMoment B raw29787step1 raw29787step1Labels := by
      have ha : raw29787step1 = (fun i j => raw29787step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29787step1 raw29787step0; decide +kernel
      have hl : raw29787step1Labels = raw29787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29787step0 raw29787step0Labels permutation127 permutation7
    mixedMoment B raw29787step1 raw29787step1Labels = mixedMoment B raw29787step2 raw29787step2Labels := by
      have ha : raw29787step2 = raw29787step1 := by apply Matrix.ext; unfold raw29787step2 raw29787step1; decide +kernel
      have hl : raw29787step1Labels = labelEmbedding1 ∘ raw29787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29787step1 raw29787step1Labels raw29787step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical29788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29788 raw29788Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw29788 raw29788Labels = mixedMoment B raw29788step0 raw29788step0Labels := by
      have hz : ∀ j, raw29788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29788step0 = (fun i j => raw29788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29788step0 raw29788; decide +kernel
      have hl : raw29788step0Labels = raw29788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29788 raw29788Labels permutation346 hz
    mixedMoment B raw29788step0 raw29788step0Labels = mixedMoment B raw29788step1 raw29788step1Labels := by
      have ha : raw29788step1 = (fun i j => raw29788step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29788step1 raw29788step0; decide +kernel
      have hl : raw29788step1Labels = raw29788step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29788step0 raw29788step0Labels permutation44 permutation5
    mixedMoment B raw29788step1 raw29788step1Labels = mixedMoment B raw29788step2 raw29788step2Labels := by
      have ha : raw29788step2 = -raw29788step1 := by apply Matrix.ext; change ∀ i j, raw29788step2 i j = -(raw29788step1 i j); unfold raw29788step2 raw29788step1; decide +kernel
      have hl : raw29788step2Labels = raw29788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29788step2 raw29788step2Labels = mixedMoment B raw29788step3 raw29788step3Labels := by
      have ha : raw29788step3 = raw29788step2 := by apply Matrix.ext; unfold raw29788step3 raw29788step2; decide +kernel
      have hl : raw29788step2Labels = labelEmbedding1 ∘ raw29788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29788step2 raw29788step2Labels raw29788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical29789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29789 raw29789Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29789 raw29789Labels = mixedMoment B raw29789step0 raw29789step0Labels := by
      have ha : raw29789step0 = (fun i j => raw29789 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29789step0 raw29789; decide +kernel
      have hl : raw29789step0Labels = raw29789Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29789 raw29789Labels permutation188 permutation5
    mixedMoment B raw29789step0 raw29789step0Labels = mixedMoment B raw29789step1 raw29789step1Labels := by
      have ha : raw29789step1 = -raw29789step0 := by apply Matrix.ext; change ∀ i j, raw29789step1 i j = -(raw29789step0 i j); unfold raw29789step1 raw29789step0; decide +kernel
      have hl : raw29789step1Labels = raw29789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29789step1 raw29789step1Labels = mixedMoment B raw29789step2 raw29789step2Labels := by
      have ha : raw29789step2 = raw29789step1 := by apply Matrix.ext; unfold raw29789step2 raw29789step1; decide +kernel
      have hl : raw29789step1Labels = labelEmbedding1 ∘ raw29789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29789step1 raw29789step1Labels raw29789step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical29790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29790 raw29790Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29790 raw29790Labels = mixedMoment B raw29790step0 raw29790step0Labels := by
      have hz : ∀ j, raw29790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29790step0 = (fun i j => raw29790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29790step0 raw29790; decide +kernel
      have hl : raw29790step0Labels = raw29790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29790 raw29790Labels permutation346 hz
    mixedMoment B raw29790step0 raw29790step0Labels = mixedMoment B raw29790step1 raw29790step1Labels := by
      have ha : raw29790step1 = (fun i j => raw29790step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29790step1 raw29790step0; decide +kernel
      have hl : raw29790step1Labels = raw29790step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29790step0 raw29790step0Labels permutation40 permutation5
    mixedMoment B raw29790step1 raw29790step1Labels = mixedMoment B raw29790step2 raw29790step2Labels := by
      have ha : raw29790step2 = -raw29790step1 := by apply Matrix.ext; change ∀ i j, raw29790step2 i j = -(raw29790step1 i j); unfold raw29790step2 raw29790step1; decide +kernel
      have hl : raw29790step2Labels = raw29790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29790step2 raw29790step2Labels = mixedMoment B raw29790step3 raw29790step3Labels := by
      have ha : raw29790step3 = raw29790step2 := by apply Matrix.ext; unfold raw29790step3 raw29790step2; decide +kernel
      have hl : raw29790step2Labels = labelEmbedding1 ∘ raw29790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29790step2 raw29790step2Labels raw29790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical29791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29791 raw29791Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw29791 raw29791Labels = mixedMoment B raw29791step0 raw29791step0Labels := by
      have hz : ∀ j, raw29791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29791step0 = (fun i j => raw29791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29791step0 raw29791; decide +kernel
      have hl : raw29791step0Labels = raw29791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29791 raw29791Labels permutation346 hz
    mixedMoment B raw29791step0 raw29791step0Labels = mixedMoment B raw29791step1 raw29791step1Labels := by
      have ha : raw29791step1 = (fun i j => raw29791step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29791step1 raw29791step0; decide +kernel
      have hl : raw29791step1Labels = raw29791step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29791step0 raw29791step0Labels permutation54 permutation5
    mixedMoment B raw29791step1 raw29791step1Labels = mixedMoment B raw29791step2 raw29791step2Labels := by
      have ha : raw29791step2 = -raw29791step1 := by apply Matrix.ext; change ∀ i j, raw29791step2 i j = -(raw29791step1 i j); unfold raw29791step2 raw29791step1; decide +kernel
      have hl : raw29791step2Labels = raw29791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29791step2 raw29791step2Labels = mixedMoment B raw29791step3 raw29791step3Labels := by
      have ha : raw29791step3 = raw29791step2 := by apply Matrix.ext; unfold raw29791step3 raw29791step2; decide +kernel
      have hl : raw29791step2Labels = labelEmbedding1 ∘ raw29791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29791step2 raw29791step2Labels raw29791step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical29792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29792 raw29792Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw29792 raw29792Labels = mixedMoment B raw29792step0 raw29792step0Labels := by
      have ha : raw29792step0 = (fun i j => raw29792 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29792step0 raw29792; decide +kernel
      have hl : raw29792step0Labels = raw29792Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29792 raw29792Labels permutation166 permutation5
    mixedMoment B raw29792step0 raw29792step0Labels = mixedMoment B raw29792step1 raw29792step1Labels := by
      have ha : raw29792step1 = -raw29792step0 := by apply Matrix.ext; change ∀ i j, raw29792step1 i j = -(raw29792step0 i j); unfold raw29792step1 raw29792step0; decide +kernel
      have hl : raw29792step1Labels = raw29792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29792step1 raw29792step1Labels = mixedMoment B raw29792step2 raw29792step2Labels := by
      have ha : raw29792step2 = raw29792step1 := by apply Matrix.ext; unfold raw29792step2 raw29792step1; decide +kernel
      have hl : raw29792step1Labels = labelEmbedding1 ∘ raw29792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29792step1 raw29792step1Labels raw29792step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical29793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29793 raw29793Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw29793 raw29793Labels = mixedMoment B raw29793step0 raw29793step0Labels := by
      have ha : raw29793step0 = (fun i j => raw29793 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29793step0 raw29793; decide +kernel
      have hl : raw29793step0Labels = raw29793Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29793 raw29793Labels permutation166 permutation5
    mixedMoment B raw29793step0 raw29793step0Labels = mixedMoment B raw29793step1 raw29793step1Labels := by
      have ha : raw29793step1 = -raw29793step0 := by apply Matrix.ext; change ∀ i j, raw29793step1 i j = -(raw29793step0 i j); unfold raw29793step1 raw29793step0; decide +kernel
      have hl : raw29793step1Labels = raw29793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29793step1 raw29793step1Labels = mixedMoment B raw29793step2 raw29793step2Labels := by
      have ha : raw29793step2 = raw29793step1 := by apply Matrix.ext; unfold raw29793step2 raw29793step1; decide +kernel
      have hl : raw29793step1Labels = labelEmbedding1 ∘ raw29793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29793step1 raw29793step1Labels raw29793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical29794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29794 raw29794Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw29794 raw29794Labels = mixedMoment B raw29794step0 raw29794step0Labels := by
      have ha : raw29794step0 = (fun i j => raw29794 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29794step0 raw29794; decide +kernel
      have hl : raw29794step0Labels = raw29794Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29794 raw29794Labels permutation160 permutation5
    mixedMoment B raw29794step0 raw29794step0Labels = mixedMoment B raw29794step1 raw29794step1Labels := by
      have ha : raw29794step1 = -raw29794step0 := by apply Matrix.ext; change ∀ i j, raw29794step1 i j = -(raw29794step0 i j); unfold raw29794step1 raw29794step0; decide +kernel
      have hl : raw29794step1Labels = raw29794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29794step1 raw29794step1Labels = mixedMoment B raw29794step2 raw29794step2Labels := by
      have ha : raw29794step2 = raw29794step1 := by apply Matrix.ext; unfold raw29794step2 raw29794step1; decide +kernel
      have hl : raw29794step1Labels = labelEmbedding1 ∘ raw29794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29794step1 raw29794step1Labels raw29794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

theorem canonical29795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29795 raw29795Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw29795 raw29795Labels = mixedMoment B raw29795step0 raw29795step0Labels := by
      have ha : raw29795step0 = (fun i j => raw29795 (permutation175 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29795step0 raw29795; decide +kernel
      have hl : raw29795step0Labels = raw29795Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29795 raw29795Labels permutation175 permutation5
    mixedMoment B raw29795step0 raw29795step0Labels = mixedMoment B raw29795step1 raw29795step1Labels := by
      have ha : raw29795step1 = -raw29795step0 := by apply Matrix.ext; change ∀ i j, raw29795step1 i j = -(raw29795step0 i j); unfold raw29795step1 raw29795step0; decide +kernel
      have hl : raw29795step1Labels = raw29795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29795step1 raw29795step1Labels = mixedMoment B raw29795step2 raw29795step2Labels := by
      have ha : raw29795step2 = raw29795step1 := by apply Matrix.ext; unfold raw29795step2 raw29795step1; decide +kernel
      have hl : raw29795step1Labels = labelEmbedding1 ∘ raw29795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29795step1 raw29795step1Labels raw29795step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical29796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29796 raw29796Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw29796 raw29796Labels = mixedMoment B raw29796step0 raw29796step0Labels := by
      have hz : ∀ j, raw29796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29796step0 = (fun i j => raw29796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29796step0 raw29796; decide +kernel
      have hl : raw29796step0Labels = raw29796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29796 raw29796Labels permutation346 hz
    mixedMoment B raw29796step0 raw29796step0Labels = mixedMoment B raw29796step1 raw29796step1Labels := by
      have ha : raw29796step1 = (fun i j => raw29796step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29796step1 raw29796step0; decide +kernel
      have hl : raw29796step1Labels = raw29796step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29796step0 raw29796step0Labels permutation35 permutation5
    mixedMoment B raw29796step1 raw29796step1Labels = mixedMoment B raw29796step2 raw29796step2Labels := by
      have ha : raw29796step2 = -raw29796step1 := by apply Matrix.ext; change ∀ i j, raw29796step2 i j = -(raw29796step1 i j); unfold raw29796step2 raw29796step1; decide +kernel
      have hl : raw29796step2Labels = raw29796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29796step2 raw29796step2Labels = mixedMoment B raw29796step3 raw29796step3Labels := by
      have ha : raw29796step3 = raw29796step2 := by apply Matrix.ext; unfold raw29796step3 raw29796step2; decide +kernel
      have hl : raw29796step2Labels = labelEmbedding1 ∘ raw29796step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29796step2 raw29796step2Labels raw29796step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical29797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29797 raw29797Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw29797 raw29797Labels = mixedMoment B raw29797step0 raw29797step0Labels := by
      have hz : ∀ j, raw29797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29797step0 = (fun i j => raw29797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29797step0 raw29797; decide +kernel
      have hl : raw29797step0Labels = raw29797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29797 raw29797Labels permutation346 hz
    mixedMoment B raw29797step0 raw29797step0Labels = mixedMoment B raw29797step1 raw29797step1Labels := by
      have ha : raw29797step1 = (fun i j => raw29797step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29797step1 raw29797step0; decide +kernel
      have hl : raw29797step1Labels = raw29797step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29797step0 raw29797step0Labels permutation35 permutation5
    mixedMoment B raw29797step1 raw29797step1Labels = mixedMoment B raw29797step2 raw29797step2Labels := by
      have ha : raw29797step2 = -raw29797step1 := by apply Matrix.ext; change ∀ i j, raw29797step2 i j = -(raw29797step1 i j); unfold raw29797step2 raw29797step1; decide +kernel
      have hl : raw29797step2Labels = raw29797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29797step2 raw29797step2Labels = mixedMoment B raw29797step3 raw29797step3Labels := by
      have ha : raw29797step3 = raw29797step2 := by apply Matrix.ext; unfold raw29797step3 raw29797step2; decide +kernel
      have hl : raw29797step2Labels = labelEmbedding1 ∘ raw29797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29797step2 raw29797step2Labels raw29797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical29798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29798 raw29798Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw29798 raw29798Labels = mixedMoment B raw29798step0 raw29798step0Labels := by
      have ha : raw29798step0 = (fun i j => raw29798 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29798step0 raw29798; decide +kernel
      have hl : raw29798step0Labels = raw29798Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29798 raw29798Labels permutation179 permutation5
    mixedMoment B raw29798step0 raw29798step0Labels = mixedMoment B raw29798step1 raw29798step1Labels := by
      have ha : raw29798step1 = -raw29798step0 := by apply Matrix.ext; change ∀ i j, raw29798step1 i j = -(raw29798step0 i j); unfold raw29798step1 raw29798step0; decide +kernel
      have hl : raw29798step1Labels = raw29798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29798step1 raw29798step1Labels = mixedMoment B raw29798step2 raw29798step2Labels := by
      have ha : raw29798step2 = raw29798step1 := by apply Matrix.ext; unfold raw29798step2 raw29798step1; decide +kernel
      have hl : raw29798step1Labels = labelEmbedding1 ∘ raw29798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29798step1 raw29798step1Labels raw29798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

theorem canonical29799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29799 raw29799Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw29799 raw29799Labels = mixedMoment B raw29799step0 raw29799step0Labels := by
      have hz : ∀ j, raw29799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29799step0 = (fun i j => raw29799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29799step0 raw29799; decide +kernel
      have hl : raw29799step0Labels = raw29799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29799 raw29799Labels permutation346 hz
    mixedMoment B raw29799step0 raw29799step0Labels = mixedMoment B raw29799step1 raw29799step1Labels := by
      have ha : raw29799step1 = (fun i j => raw29799step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29799step1 raw29799step0; decide +kernel
      have hl : raw29799step1Labels = raw29799step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29799step0 raw29799step0Labels permutation37 permutation5
    mixedMoment B raw29799step1 raw29799step1Labels = mixedMoment B raw29799step2 raw29799step2Labels := by
      have ha : raw29799step2 = -raw29799step1 := by apply Matrix.ext; change ∀ i j, raw29799step2 i j = -(raw29799step1 i j); unfold raw29799step2 raw29799step1; decide +kernel
      have hl : raw29799step2Labels = raw29799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29799step2 raw29799step2Labels = mixedMoment B raw29799step3 raw29799step3Labels := by
      have ha : raw29799step3 = raw29799step2 := by apply Matrix.ext; unfold raw29799step3 raw29799step2; decide +kernel
      have hl : raw29799step2Labels = labelEmbedding1 ∘ raw29799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29799step2 raw29799step2Labels raw29799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical29800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29800 raw29800Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw29800 raw29800Labels = mixedMoment B raw29800step0 raw29800step0Labels := by
      have hz : ∀ j, raw29800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29800step0 = (fun i j => raw29800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29800step0 raw29800; decide +kernel
      have hl : raw29800step0Labels = raw29800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29800 raw29800Labels permutation346 hz
    mixedMoment B raw29800step0 raw29800step0Labels = mixedMoment B raw29800step1 raw29800step1Labels := by
      have ha : raw29800step1 = (fun i j => raw29800step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29800step1 raw29800step0; decide +kernel
      have hl : raw29800step1Labels = raw29800step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29800step0 raw29800step0Labels permutation33 permutation5
    mixedMoment B raw29800step1 raw29800step1Labels = mixedMoment B raw29800step2 raw29800step2Labels := by
      have ha : raw29800step2 = -raw29800step1 := by apply Matrix.ext; change ∀ i j, raw29800step2 i j = -(raw29800step1 i j); unfold raw29800step2 raw29800step1; decide +kernel
      have hl : raw29800step2Labels = raw29800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29800step2 raw29800step2Labels = mixedMoment B raw29800step3 raw29800step3Labels := by
      have ha : raw29800step3 = raw29800step2 := by apply Matrix.ext; unfold raw29800step3 raw29800step2; decide +kernel
      have hl : raw29800step2Labels = labelEmbedding1 ∘ raw29800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29800step2 raw29800step2Labels raw29800step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical29801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29801 raw29801Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw29801 raw29801Labels = mixedMoment B raw29801step0 raw29801step0Labels := by
      have hz : ∀ j, raw29801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29801step0 = (fun i j => raw29801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29801step0 raw29801; decide +kernel
      have hl : raw29801step0Labels = raw29801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29801 raw29801Labels permutation346 hz
    mixedMoment B raw29801step0 raw29801step0Labels = mixedMoment B raw29801step1 raw29801step1Labels := by
      have ha : raw29801step1 = (fun i j => raw29801step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29801step1 raw29801step0; decide +kernel
      have hl : raw29801step1Labels = raw29801step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29801step0 raw29801step0Labels permutation33 permutation5
    mixedMoment B raw29801step1 raw29801step1Labels = mixedMoment B raw29801step2 raw29801step2Labels := by
      have ha : raw29801step2 = -raw29801step1 := by apply Matrix.ext; change ∀ i j, raw29801step2 i j = -(raw29801step1 i j); unfold raw29801step2 raw29801step1; decide +kernel
      have hl : raw29801step2Labels = raw29801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29801step2 raw29801step2Labels = mixedMoment B raw29801step3 raw29801step3Labels := by
      have ha : raw29801step3 = raw29801step2 := by apply Matrix.ext; unfold raw29801step3 raw29801step2; decide +kernel
      have hl : raw29801step2Labels = labelEmbedding1 ∘ raw29801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29801step2 raw29801step2Labels raw29801step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical29802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29802 raw29802Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw29802 raw29802Labels = mixedMoment B raw29802step0 raw29802step0Labels := by
      have ha : raw29802step0 = (fun i j => raw29802 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29802step0 raw29802; decide +kernel
      have hl : raw29802step0Labels = raw29802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29802 raw29802Labels permutation584 permutation7
    mixedMoment B raw29802step0 raw29802step0Labels = mixedMoment B raw29802step1 raw29802step1Labels := by
      have ha : raw29802step1 = raw29802step0 := by apply Matrix.ext; unfold raw29802step1 raw29802step0; decide +kernel
      have hl : raw29802step0Labels = labelEmbedding1 ∘ raw29802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29802step0 raw29802step0Labels raw29802step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical29803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29803 raw29803Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw29803 raw29803Labels = mixedMoment B raw29803step0 raw29803step0Labels := by
      have hz : ∀ j, raw29803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29803step0 = (fun i j => raw29803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29803step0 raw29803; decide +kernel
      have hl : raw29803step0Labels = raw29803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29803 raw29803Labels permutation346 hz
    mixedMoment B raw29803step0 raw29803step0Labels = mixedMoment B raw29803step1 raw29803step1Labels := by
      have ha : raw29803step1 = (fun i j => raw29803step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29803step1 raw29803step0; decide +kernel
      have hl : raw29803step1Labels = raw29803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29803step0 raw29803step0Labels permutation125 permutation7
    mixedMoment B raw29803step1 raw29803step1Labels = mixedMoment B raw29803step2 raw29803step2Labels := by
      have ha : raw29803step2 = raw29803step1 := by apply Matrix.ext; unfold raw29803step2 raw29803step1; decide +kernel
      have hl : raw29803step1Labels = labelEmbedding1 ∘ raw29803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29803step1 raw29803step1Labels raw29803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

theorem canonical29804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29804 raw29804Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw29804 raw29804Labels = mixedMoment B raw29804step0 raw29804step0Labels := by
      have hz : ∀ j, raw29804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29804step0 = (fun i j => raw29804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29804step0 raw29804; decide +kernel
      have hl : raw29804step0Labels = raw29804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29804 raw29804Labels permutation346 hz
    mixedMoment B raw29804step0 raw29804step0Labels = mixedMoment B raw29804step1 raw29804step1Labels := by
      have ha : raw29804step1 = (fun i j => raw29804step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29804step1 raw29804step0; decide +kernel
      have hl : raw29804step1Labels = raw29804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29804step0 raw29804step0Labels permutation127 permutation7
    mixedMoment B raw29804step1 raw29804step1Labels = mixedMoment B raw29804step2 raw29804step2Labels := by
      have ha : raw29804step2 = raw29804step1 := by apply Matrix.ext; unfold raw29804step2 raw29804step1; decide +kernel
      have hl : raw29804step1Labels = labelEmbedding1 ∘ raw29804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29804step1 raw29804step1Labels raw29804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical29805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29805 raw29805Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw29805 raw29805Labels = mixedMoment B raw29805step0 raw29805step0Labels := by
      have hz : ∀ j, raw29805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29805step0 = (fun i j => raw29805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29805step0 raw29805; decide +kernel
      have hl : raw29805step0Labels = raw29805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29805 raw29805Labels permutation346 hz
    mixedMoment B raw29805step0 raw29805step0Labels = mixedMoment B raw29805step1 raw29805step1Labels := by
      have ha : raw29805step1 = (fun i j => raw29805step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29805step1 raw29805step0; decide +kernel
      have hl : raw29805step1Labels = raw29805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29805step0 raw29805step0Labels permutation34 permutation5
    mixedMoment B raw29805step1 raw29805step1Labels = mixedMoment B raw29805step2 raw29805step2Labels := by
      have ha : raw29805step2 = -raw29805step1 := by apply Matrix.ext; change ∀ i j, raw29805step2 i j = -(raw29805step1 i j); unfold raw29805step2 raw29805step1; decide +kernel
      have hl : raw29805step2Labels = raw29805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29805step2 raw29805step2Labels = mixedMoment B raw29805step3 raw29805step3Labels := by
      have ha : raw29805step3 = raw29805step2 := by apply Matrix.ext; unfold raw29805step3 raw29805step2; decide +kernel
      have hl : raw29805step2Labels = labelEmbedding1 ∘ raw29805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29805step2 raw29805step2Labels raw29805step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical29806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29806 raw29806Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw29806 raw29806Labels = mixedMoment B raw29806step0 raw29806step0Labels := by
      have hz : ∀ j, raw29806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29806step0 = (fun i j => raw29806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29806step0 raw29806; decide +kernel
      have hl : raw29806step0Labels = raw29806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29806 raw29806Labels permutation346 hz
    mixedMoment B raw29806step0 raw29806step0Labels = mixedMoment B raw29806step1 raw29806step1Labels := by
      have ha : raw29806step1 = (fun i j => raw29806step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29806step1 raw29806step0; decide +kernel
      have hl : raw29806step1Labels = raw29806step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29806step0 raw29806step0Labels permutation34 permutation5
    mixedMoment B raw29806step1 raw29806step1Labels = mixedMoment B raw29806step2 raw29806step2Labels := by
      have ha : raw29806step2 = -raw29806step1 := by apply Matrix.ext; change ∀ i j, raw29806step2 i j = -(raw29806step1 i j); unfold raw29806step2 raw29806step1; decide +kernel
      have hl : raw29806step2Labels = raw29806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29806step2 raw29806step2Labels = mixedMoment B raw29806step3 raw29806step3Labels := by
      have ha : raw29806step3 = raw29806step2 := by apply Matrix.ext; unfold raw29806step3 raw29806step2; decide +kernel
      have hl : raw29806step2Labels = labelEmbedding1 ∘ raw29806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29806step2 raw29806step2Labels raw29806step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical29807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29807 raw29807Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw29807 raw29807Labels = mixedMoment B raw29807step0 raw29807step0Labels := by
      have ha : raw29807step0 = (fun i j => raw29807 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29807step0 raw29807; decide +kernel
      have hl : raw29807step0Labels = raw29807Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29807 raw29807Labels permutation178 permutation5
    mixedMoment B raw29807step0 raw29807step0Labels = mixedMoment B raw29807step1 raw29807step1Labels := by
      have ha : raw29807step1 = -raw29807step0 := by apply Matrix.ext; change ∀ i j, raw29807step1 i j = -(raw29807step0 i j); unfold raw29807step1 raw29807step0; decide +kernel
      have hl : raw29807step1Labels = raw29807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29807step1 raw29807step1Labels = mixedMoment B raw29807step2 raw29807step2Labels := by
      have ha : raw29807step2 = raw29807step1 := by apply Matrix.ext; unfold raw29807step2 raw29807step1; decide +kernel
      have hl : raw29807step1Labels = labelEmbedding1 ∘ raw29807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29807step1 raw29807step1Labels raw29807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical29808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29808 raw29808Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw29808 raw29808Labels = mixedMoment B raw29808step0 raw29808step0Labels := by
      have hz : ∀ j, raw29808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29808step0 = (fun i j => raw29808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29808step0 raw29808; decide +kernel
      have hl : raw29808step0Labels = raw29808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29808 raw29808Labels permutation346 hz
    mixedMoment B raw29808step0 raw29808step0Labels = mixedMoment B raw29808step1 raw29808step1Labels := by
      have ha : raw29808step1 = (fun i j => raw29808step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29808step1 raw29808step0; decide +kernel
      have hl : raw29808step1Labels = raw29808step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29808step0 raw29808step0Labels permutation149 permutation5
    mixedMoment B raw29808step1 raw29808step1Labels = mixedMoment B raw29808step2 raw29808step2Labels := by
      have ha : raw29808step2 = raw29808step1 := by apply Matrix.ext; unfold raw29808step2 raw29808step1; decide +kernel
      have hl : raw29808step1Labels = labelEmbedding1 ∘ raw29808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29808step1 raw29808step1Labels raw29808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

theorem canonical29809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29809 raw29809Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw29809 raw29809Labels = mixedMoment B raw29809step0 raw29809step0Labels := by
      have hz : ∀ j, raw29809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29809step0 = (fun i j => raw29809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29809step0 raw29809; decide +kernel
      have hl : raw29809step0Labels = raw29809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29809 raw29809Labels permutation346 hz
    mixedMoment B raw29809step0 raw29809step0Labels = mixedMoment B raw29809step1 raw29809step1Labels := by
      have ha : raw29809step1 = (fun i j => raw29809step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29809step1 raw29809step0; decide +kernel
      have hl : raw29809step1Labels = raw29809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29809step0 raw29809step0Labels permutation126 permutation2
    mixedMoment B raw29809step1 raw29809step1Labels = mixedMoment B raw29809step2 raw29809step2Labels := by
      have ha : raw29809step2 = -raw29809step1 := by apply Matrix.ext; change ∀ i j, raw29809step2 i j = -(raw29809step1 i j); unfold raw29809step2 raw29809step1; decide +kernel
      have hl : raw29809step2Labels = raw29809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical29810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29810 raw29810Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw29810 raw29810Labels = mixedMoment B raw29810step0 raw29810step0Labels := by
      have ha : raw29810step0 = (fun i j => raw29810 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29810step0 raw29810; decide +kernel
      have hl : raw29810step0Labels = raw29810Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29810 raw29810Labels permutation159 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

theorem canonical29811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29811 raw29811Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw29811 raw29811Labels = mixedMoment B raw29811step0 raw29811step0Labels := by
      have hz : ∀ j, raw29811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29811step0 = (fun i j => raw29811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29811step0 raw29811; decide +kernel
      have hl : raw29811step0Labels = raw29811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29811 raw29811Labels permutation346 hz
    mixedMoment B raw29811step0 raw29811step0Labels = mixedMoment B raw29811step1 raw29811step1Labels := by
      have ha : raw29811step1 = (fun i j => raw29811step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29811step1 raw29811step0; decide +kernel
      have hl : raw29811step1Labels = raw29811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29811step0 raw29811step0Labels permutation33 permutation2
    _ = mixedMoment B node2827 node2827Labels := by rfl

theorem canonical29812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29812 raw29812Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw29812 raw29812Labels = mixedMoment B raw29812step0 raw29812step0Labels := by
      have hz : ∀ j, raw29812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29812step0 = (fun i j => raw29812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29812step0 raw29812; decide +kernel
      have hl : raw29812step0Labels = raw29812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29812 raw29812Labels permutation346 hz
    mixedMoment B raw29812step0 raw29812step0Labels = mixedMoment B raw29812step1 raw29812step1Labels := by
      have ha : raw29812step1 = (fun i j => raw29812step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29812step1 raw29812step0; decide +kernel
      have hl : raw29812step1Labels = raw29812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29812step0 raw29812step0Labels permutation127 permutation2
    mixedMoment B raw29812step1 raw29812step1Labels = mixedMoment B raw29812step2 raw29812step2Labels := by
      have ha : raw29812step2 = -raw29812step1 := by apply Matrix.ext; change ∀ i j, raw29812step2 i j = -(raw29812step1 i j); unfold raw29812step2 raw29812step1; decide +kernel
      have hl : raw29812step2Labels = raw29812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2326 node2326Labels := by rfl

theorem canonical29813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29813 raw29813Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw29813 raw29813Labels = mixedMoment B raw29813step0 raw29813step0Labels := by
      have ha : raw29813step0 = (fun i j => raw29813 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29813step0 raw29813; decide +kernel
      have hl : raw29813step0Labels = raw29813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29813 raw29813Labels permutation159 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

theorem canonical29814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29814 raw29814Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw29814 raw29814Labels = mixedMoment B raw29814step0 raw29814step0Labels := by
      have ha : raw29814step0 = (fun i j => raw29814 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29814step0 raw29814; decide +kernel
      have hl : raw29814step0Labels = raw29814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29814 raw29814Labels permutation159 permutation2
    _ = mixedMoment B node2893 node2893Labels := by rfl

theorem canonical29815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29815 raw29815Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw29815 raw29815Labels = mixedMoment B raw29815step0 raw29815step0Labels := by
      have ha : raw29815step0 = (fun i j => raw29815 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29815step0 raw29815; decide +kernel
      have hl : raw29815step0Labels = raw29815Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29815 raw29815Labels permutation158 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical29816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29816 raw29816Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw29816 raw29816Labels = mixedMoment B raw29816step0 raw29816step0Labels := by
      have ha : raw29816step0 = (fun i j => raw29816 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29816step0 raw29816; decide +kernel
      have hl : raw29816step0Labels = raw29816Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29816 raw29816Labels permutation159 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical29817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29817 raw29817Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw29817 raw29817Labels = mixedMoment B raw29817step0 raw29817step0Labels := by
      have hz : ∀ j, raw29817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29817step0 = (fun i j => raw29817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29817step0 raw29817; decide +kernel
      have hl : raw29817step0Labels = raw29817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29817 raw29817Labels permutation346 hz
    mixedMoment B raw29817step0 raw29817step0Labels = mixedMoment B raw29817step1 raw29817step1Labels := by
      have ha : raw29817step1 = (fun i j => raw29817step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29817step1 raw29817step0; decide +kernel
      have hl : raw29817step1Labels = raw29817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29817step0 raw29817step0Labels permutation33 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

theorem canonical29818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29818 raw29818Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw29818 raw29818Labels = mixedMoment B raw29818step0 raw29818step0Labels := by
      have ha : raw29818step0 = (fun i j => raw29818 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29818step0 raw29818; decide +kernel
      have hl : raw29818step0Labels = raw29818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29818 raw29818Labels permutation153 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

theorem canonical29819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29819 raw29819Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw29819 raw29819Labels = mixedMoment B raw29819step0 raw29819step0Labels := by
      have hz : ∀ j, raw29819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29819step0 = (fun i j => raw29819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29819step0 raw29819; decide +kernel
      have hl : raw29819step0Labels = raw29819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29819 raw29819Labels permutation346 hz
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical29820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29820 raw29820Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw29820 raw29820Labels = mixedMoment B raw29820step0 raw29820step0Labels := by
      have hz : ∀ j, raw29820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29820step0 = (fun i j => raw29820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29820step0 raw29820; decide +kernel
      have hl : raw29820step0Labels = raw29820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29820 raw29820Labels permutation346 hz
    mixedMoment B raw29820step0 raw29820step0Labels = mixedMoment B raw29820step1 raw29820step1Labels := by
      have ha : raw29820step1 = (fun i j => raw29820step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29820step1 raw29820step0; decide +kernel
      have hl : raw29820step1Labels = raw29820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29820step0 raw29820step0Labels permutation33 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29860 raw29860Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw29860 raw29860Labels = mixedMoment B raw29860step0 raw29860step0Labels := by
      have hz : ∀ j, raw29860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29860step0 = (fun i j => raw29860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29860step0 raw29860; decide +kernel
      have hl : raw29860step0Labels = raw29860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29860 raw29860Labels permutation346 hz
    mixedMoment B raw29860step0 raw29860step0Labels = mixedMoment B raw29860step1 raw29860step1Labels := by
      have ha : raw29860step1 = -raw29860step0 := by apply Matrix.ext; change ∀ i j, raw29860step1 i j = -(raw29860step0 i j); unfold raw29860step1 raw29860step0; decide +kernel
      have hl : raw29860step1Labels = raw29860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3439 node3439Labels := by rfl

theorem canonical29861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29861 raw29861Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw29861 raw29861Labels = mixedMoment B raw29861step0 raw29861step0Labels := by
      have hz : ∀ j, raw29861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29861step0 = (fun i j => raw29861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29861step0 raw29861; decide +kernel
      have hl : raw29861step0Labels = raw29861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29861 raw29861Labels permutation346 hz
    mixedMoment B raw29861step0 raw29861step0Labels = mixedMoment B raw29861step1 raw29861step1Labels := by
      have ha : raw29861step1 = (fun i j => raw29861step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29861step1 raw29861step0; decide +kernel
      have hl : raw29861step1Labels = raw29861step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29861step0 raw29861step0Labels permutation33 permutation2
    _ = mixedMoment B node2910 node2910Labels := by rfl

theorem canonical29862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29862 raw29862Labels = mixedMoment B node3349 node3349Labels := by
  calc
    mixedMoment B raw29862 raw29862Labels = mixedMoment B raw29862step0 raw29862step0Labels := by
      have hz : ∀ j, raw29862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29862step0 = (fun i j => raw29862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29862step0 raw29862; decide +kernel
      have hl : raw29862step0Labels = raw29862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29862 raw29862Labels permutation346 hz
    mixedMoment B raw29862step0 raw29862step0Labels = mixedMoment B raw29862step1 raw29862step1Labels := by
      have ha : raw29862step1 = (fun i j => raw29862step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29862step1 raw29862step0; decide +kernel
      have hl : raw29862step1Labels = raw29862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29862step0 raw29862step0Labels permutation126 permutation2
    mixedMoment B raw29862step1 raw29862step1Labels = mixedMoment B raw29862step2 raw29862step2Labels := by
      have ha : raw29862step2 = -raw29862step1 := by apply Matrix.ext; change ∀ i j, raw29862step2 i j = -(raw29862step1 i j); unfold raw29862step2 raw29862step1; decide +kernel
      have hl : raw29862step2Labels = raw29862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3349 node3349Labels := by rfl

theorem canonical29863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29863 raw29863Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw29863 raw29863Labels = mixedMoment B raw29863step0 raw29863step0Labels := by
      have ha : raw29863step0 = (fun i j => raw29863 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29863step0 raw29863; decide +kernel
      have hl : raw29863step0Labels = raw29863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29863 raw29863Labels permutation589 permutation2
    mixedMoment B raw29863step0 raw29863step0Labels = mixedMoment B raw29863step1 raw29863step1Labels := by
      have ha : raw29863step1 = -raw29863step0 := by apply Matrix.ext; change ∀ i j, raw29863step1 i j = -(raw29863step0 i j); unfold raw29863step1 raw29863step0; decide +kernel
      have hl : raw29863step1Labels = raw29863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3346 node3346Labels := by rfl

theorem canonical29864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29864 raw29864Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw29864 raw29864Labels = mixedMoment B raw29864step0 raw29864step0Labels := by
      have hz : ∀ j, raw29864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29864step0 = (fun i j => raw29864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29864step0 raw29864; decide +kernel
      have hl : raw29864step0Labels = raw29864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29864 raw29864Labels permutation346 hz
    mixedMoment B raw29864step0 raw29864step0Labels = mixedMoment B raw29864step1 raw29864step1Labels := by
      have ha : raw29864step1 = (fun i j => raw29864step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29864step1 raw29864step0; decide +kernel
      have hl : raw29864step1Labels = raw29864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29864step0 raw29864step0Labels permutation125 permutation2
    mixedMoment B raw29864step1 raw29864step1Labels = mixedMoment B raw29864step2 raw29864step2Labels := by
      have ha : raw29864step2 = -raw29864step1 := by apply Matrix.ext; change ∀ i j, raw29864step2 i j = -(raw29864step1 i j); unfold raw29864step2 raw29864step1; decide +kernel
      have hl : raw29864step2Labels = raw29864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3357 node3357Labels := by rfl

theorem canonical29865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29865 raw29865Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw29865 raw29865Labels = mixedMoment B raw29865step0 raw29865step0Labels := by
      have hz : ∀ j, raw29865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29865step0 = (fun i j => raw29865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29865step0 raw29865; decide +kernel
      have hl : raw29865step0Labels = raw29865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29865 raw29865Labels permutation346 hz
    mixedMoment B raw29865step0 raw29865step0Labels = mixedMoment B raw29865step1 raw29865step1Labels := by
      have ha : raw29865step1 = (fun i j => raw29865step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29865step1 raw29865step0; decide +kernel
      have hl : raw29865step1Labels = raw29865step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29865step0 raw29865step0Labels permutation105 permutation4
    mixedMoment B raw29865step1 raw29865step1Labels = mixedMoment B raw29865step2 raw29865step2Labels := by
      have ha : raw29865step2 = -raw29865step1 := by apply Matrix.ext; change ∀ i j, raw29865step2 i j = -(raw29865step1 i j); unfold raw29865step2 raw29865step1; decide +kernel
      have hl : raw29865step2Labels = raw29865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical29866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29866 raw29866Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw29866 raw29866Labels = mixedMoment B raw29866step0 raw29866step0Labels := by
      have hz : ∀ j, raw29866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29866step0 = (fun i j => raw29866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29866step0 raw29866; decide +kernel
      have hl : raw29866step0Labels = raw29866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29866 raw29866Labels permutation346 hz
    mixedMoment B raw29866step0 raw29866step0Labels = mixedMoment B raw29866step1 raw29866step1Labels := by
      have ha : raw29866step1 = (fun i j => raw29866step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29866step1 raw29866step0; decide +kernel
      have hl : raw29866step1Labels = raw29866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29866step0 raw29866step0Labels permutation127 permutation2
    mixedMoment B raw29866step1 raw29866step1Labels = mixedMoment B raw29866step2 raw29866step2Labels := by
      have ha : raw29866step2 = -raw29866step1 := by apply Matrix.ext; change ∀ i j, raw29866step2 i j = -(raw29866step1 i j); unfold raw29866step2 raw29866step1; decide +kernel
      have hl : raw29866step2Labels = raw29866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3479 node3479Labels := by rfl

theorem canonical29867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29867 raw29867Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29867 raw29867Labels = mixedMoment B raw29867step0 raw29867step0Labels := by
      have hz : ∀ j, raw29867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29867step0 = (fun i j => raw29867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29867step0 raw29867; decide +kernel
      have hl : raw29867step0Labels = raw29867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29867 raw29867Labels permutation346 hz
    mixedMoment B raw29867step0 raw29867step0Labels = mixedMoment B raw29867step1 raw29867step1Labels := by
      have ha : raw29867step1 = (fun i j => raw29867step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29867step1 raw29867step0; decide +kernel
      have hl : raw29867step1Labels = raw29867step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29867step0 raw29867step0Labels permutation122 permutation0
    mixedMoment B raw29867step1 raw29867step1Labels = mixedMoment B raw29867step2 raw29867step2Labels := by
      have ha : raw29867step2 = -raw29867step1 := by apply Matrix.ext; change ∀ i j, raw29867step2 i j = -(raw29867step1 i j); unfold raw29867step2 raw29867step1; decide +kernel
      have hl : raw29867step2Labels = raw29867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical29894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29894 raw29894Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw29894 raw29894Labels = mixedMoment B raw29894step0 raw29894step0Labels := by
      have hz : ∀ j, raw29894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29894step0 = (fun i j => raw29894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29894step0 raw29894; decide +kernel
      have hl : raw29894step0Labels = raw29894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29894 raw29894Labels permutation434 hz
    mixedMoment B raw29894step0 raw29894step0Labels = mixedMoment B raw29894step1 raw29894step1Labels := by
      have ha : raw29894step1 = (fun i j => raw29894step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29894step1 raw29894step0; decide +kernel
      have hl : raw29894step1Labels = raw29894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29894step0 raw29894step0Labels permutation149 permutation2
    mixedMoment B raw29894step1 raw29894step1Labels = mixedMoment B raw29894step2 raw29894step2Labels := by
      have ha : raw29894step2 = -raw29894step1 := by apply Matrix.ext; change ∀ i j, raw29894step2 i j = -(raw29894step1 i j); unfold raw29894step2 raw29894step1; decide +kernel
      have hl : raw29894step2Labels = raw29894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical29895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29895 raw29895Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29895 raw29895Labels = mixedMoment B raw29895step0 raw29895step0Labels := by
      have hz : ∀ j, raw29895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29895step0 = (fun i j => raw29895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29895step0 raw29895; decide +kernel
      have hl : raw29895step0Labels = raw29895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29895 raw29895Labels permutation434 hz
    mixedMoment B raw29895step0 raw29895step0Labels = mixedMoment B raw29895step1 raw29895step1Labels := by
      have ha : raw29895step1 = (fun i j => raw29895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29895step1 raw29895step0; decide +kernel
      have hl : raw29895step1Labels = raw29895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29895step0 raw29895step0Labels permutation38 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical29896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29896 raw29896Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw29896 raw29896Labels = mixedMoment B raw29896step0 raw29896step0Labels := by
      have hz : ∀ j, raw29896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29896step0 = (fun i j => raw29896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29896step0 raw29896; decide +kernel
      have hl : raw29896step0Labels = raw29896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29896 raw29896Labels permutation434 hz
    _ = mixedMoment B node2620 node2620Labels := by rfl

theorem canonical29897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29897 raw29897Labels = mixedMoment B node2438 node2438Labels := by
  calc
    mixedMoment B raw29897 raw29897Labels = mixedMoment B raw29897step0 raw29897step0Labels := by
      have ha : raw29897step0 = (fun i j => raw29897 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29897step0 raw29897; decide +kernel
      have hl : raw29897step0Labels = raw29897Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29897 raw29897Labels permutation176 permutation2
    _ = mixedMoment B node2438 node2438Labels := by rfl

theorem canonical29898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29898 raw29898Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw29898 raw29898Labels = mixedMoment B raw29898step0 raw29898step0Labels := by
      have hz : ∀ j, raw29898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29898step0 = (fun i j => raw29898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29898step0 raw29898; decide +kernel
      have hl : raw29898step0Labels = raw29898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29898 raw29898Labels permutation434 hz
    mixedMoment B raw29898step0 raw29898step0Labels = mixedMoment B raw29898step1 raw29898step1Labels := by
      have ha : raw29898step1 = (fun i j => raw29898step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29898step1 raw29898step0; decide +kernel
      have hl : raw29898step1Labels = raw29898step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29898step0 raw29898step0Labels permutation39 permutation2
    _ = mixedMoment B node2443 node2443Labels := by rfl

theorem canonical29899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29899 raw29899Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw29899 raw29899Labels = mixedMoment B raw29899step0 raw29899step0Labels := by
      have hz : ∀ j, raw29899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29899step0 = (fun i j => raw29899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29899step0 raw29899; decide +kernel
      have hl : raw29899step0Labels = raw29899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29899 raw29899Labels permutation434 hz
    mixedMoment B raw29899step0 raw29899step0Labels = mixedMoment B raw29899step1 raw29899step1Labels := by
      have ha : raw29899step1 = (fun i j => raw29899step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29899step1 raw29899step0; decide +kernel
      have hl : raw29899step1Labels = raw29899step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29899step0 raw29899step0Labels permutation149 permutation2
    mixedMoment B raw29899step1 raw29899step1Labels = mixedMoment B raw29899step2 raw29899step2Labels := by
      have ha : raw29899step2 = -raw29899step1 := by apply Matrix.ext; change ∀ i j, raw29899step2 i j = -(raw29899step1 i j); unfold raw29899step2 raw29899step1; decide +kernel
      have hl : raw29899step2Labels = raw29899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2355 node2355Labels := by rfl

theorem canonical29900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29900 raw29900Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw29900 raw29900Labels = mixedMoment B raw29900step0 raw29900step0Labels := by
      have hz : ∀ j, raw29900 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29900step0 = (fun i j => raw29900 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29900step0 raw29900; decide +kernel
      have hl : raw29900step0Labels = raw29900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29900 raw29900Labels permutation520 hz
    mixedMoment B raw29900step0 raw29900step0Labels = mixedMoment B raw29900step1 raw29900step1Labels := by
      have hz : ∀ j, raw29900step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29900step1 = (fun i j => raw29900step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29900step1 raw29900step0; decide +kernel
      have hl : raw29900step1Labels = raw29900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29900step0 raw29900step0Labels permutation104 hz
    mixedMoment B raw29900step1 raw29900step1Labels = mixedMoment B raw29900step2 raw29900step2Labels := by
      have ha : raw29900step2 = (fun i j => raw29900step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29900step2 raw29900step1; decide +kernel
      have hl : raw29900step2Labels = raw29900step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29900step1 raw29900step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical29901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29901 raw29901Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw29901 raw29901Labels = mixedMoment B raw29901step0 raw29901step0Labels := by
      have hz : ∀ j, raw29901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29901step0 = (fun i j => raw29901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29901step0 raw29901; decide +kernel
      have hl : raw29901step0Labels = raw29901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29901 raw29901Labels permutation434 hz
    mixedMoment B raw29901step0 raw29901step0Labels = mixedMoment B raw29901step1 raw29901step1Labels := by
      have ha : raw29901step1 = (fun i j => raw29901step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29901step1 raw29901step0; decide +kernel
      have hl : raw29901step1Labels = raw29901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29901step0 raw29901step0Labels permutation57 permutation2
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical29902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29902 raw29902Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw29902 raw29902Labels = mixedMoment B raw29902step0 raw29902step0Labels := by
      have hz : ∀ j, raw29902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29902step0 = (fun i j => raw29902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29902step0 raw29902; decide +kernel
      have hl : raw29902step0Labels = raw29902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29902 raw29902Labels permutation434 hz
    mixedMoment B raw29902step0 raw29902step0Labels = mixedMoment B raw29902step1 raw29902step1Labels := by
      have ha : raw29902step1 = (fun i j => raw29902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29902step1 raw29902step0; decide +kernel
      have hl : raw29902step1Labels = raw29902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29902step0 raw29902step0Labels permutation33 permutation2
    _ = mixedMoment B node2867 node2867Labels := by rfl

theorem canonical29903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29903 raw29903Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw29903 raw29903Labels = mixedMoment B raw29903step0 raw29903step0Labels := by
      have hz : ∀ j, raw29903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29903step0 = (fun i j => raw29903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29903step0 raw29903; decide +kernel
      have hl : raw29903step0Labels = raw29903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29903 raw29903Labels permutation434 hz
    mixedMoment B raw29903step0 raw29903step0Labels = mixedMoment B raw29903step1 raw29903step1Labels := by
      have ha : raw29903step1 = (fun i j => raw29903step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29903step1 raw29903step0; decide +kernel
      have hl : raw29903step1Labels = raw29903step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29903step0 raw29903step0Labels permutation33 permutation2
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical29904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29904 raw29904Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw29904 raw29904Labels = mixedMoment B raw29904step0 raw29904step0Labels := by
      have ha : raw29904step0 = (fun i j => raw29904 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29904step0 raw29904; decide +kernel
      have hl : raw29904step0Labels = raw29904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29904 raw29904Labels permutation153 permutation2
    _ = mixedMoment B node2798 node2798Labels := by rfl

theorem canonical29905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29905 raw29905Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw29905 raw29905Labels = mixedMoment B raw29905step0 raw29905step0Labels := by
      have hz : ∀ j, raw29905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29905step0 = (fun i j => raw29905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29905step0 raw29905; decide +kernel
      have hl : raw29905step0Labels = raw29905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29905 raw29905Labels permutation434 hz
    mixedMoment B raw29905step0 raw29905step0Labels = mixedMoment B raw29905step1 raw29905step1Labels := by
      have ha : raw29905step1 = (fun i j => raw29905step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29905step1 raw29905step0; decide +kernel
      have hl : raw29905step1Labels = raw29905step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29905step0 raw29905step0Labels permutation127 permutation2
    mixedMoment B raw29905step1 raw29905step1Labels = mixedMoment B raw29905step2 raw29905step2Labels := by
      have ha : raw29905step2 = -raw29905step1 := by apply Matrix.ext; change ∀ i j, raw29905step2 i j = -(raw29905step1 i j); unfold raw29905step2 raw29905step1; decide +kernel
      have hl : raw29905step2Labels = raw29905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

theorem canonical29906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29906 raw29906Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw29906 raw29906Labels = mixedMoment B raw29906step0 raw29906step0Labels := by
      have hz : ∀ j, raw29906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29906step0 = (fun i j => raw29906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29906step0 raw29906; decide +kernel
      have hl : raw29906step0Labels = raw29906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29906 raw29906Labels permutation434 hz
    _ = mixedMoment B node2803 node2803Labels := by rfl

theorem canonical29907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29907 raw29907Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw29907 raw29907Labels = mixedMoment B raw29907step0 raw29907step0Labels := by
      have hz : ∀ j, raw29907 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29907step0 = (fun i j => raw29907 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29907step0 raw29907; decide +kernel
      have hl : raw29907step0Labels = raw29907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29907 raw29907Labels permutation590 hz
    mixedMoment B raw29907step0 raw29907step0Labels = mixedMoment B raw29907step1 raw29907step1Labels := by
      have hz : ∀ j, raw29907step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29907step1 = (fun i j => raw29907step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29907step1 raw29907step0; decide +kernel
      have hl : raw29907step1Labels = raw29907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29907step0 raw29907step0Labels permutation104 hz
    mixedMoment B raw29907step1 raw29907step1Labels = mixedMoment B raw29907step2 raw29907step2Labels := by
      have ha : raw29907step2 = (fun i j => raw29907step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29907step2 raw29907step1; decide +kernel
      have hl : raw29907step2Labels = raw29907step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29907step1 raw29907step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical29908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29908 raw29908Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw29908 raw29908Labels = mixedMoment B raw29908step0 raw29908step0Labels := by
      have hz : ∀ j, raw29908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29908step0 = (fun i j => raw29908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29908step0 raw29908; decide +kernel
      have hl : raw29908step0Labels = raw29908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29908 raw29908Labels permutation434 hz
    mixedMoment B raw29908step0 raw29908step0Labels = mixedMoment B raw29908step1 raw29908step1Labels := by
      have ha : raw29908step1 = (fun i j => raw29908step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29908step1 raw29908step0; decide +kernel
      have hl : raw29908step1Labels = raw29908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29908step0 raw29908step0Labels permutation33 permutation2
    _ = mixedMoment B node1321 node1321Labels := by rfl

theorem canonical29909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29909 raw29909Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw29909 raw29909Labels = mixedMoment B raw29909step0 raw29909step0Labels := by
      have ha : raw29909step0 = (fun i j => raw29909 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29909step0 raw29909; decide +kernel
      have hl : raw29909step0Labels = raw29909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29909 raw29909Labels permutation159 permutation2
    _ = mixedMoment B node2848 node2848Labels := by rfl

theorem canonical29910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29910 raw29910Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw29910 raw29910Labels = mixedMoment B raw29910step0 raw29910step0Labels := by
      have hz : ∀ j, raw29910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29910step0 = (fun i j => raw29910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29910step0 raw29910; decide +kernel
      have hl : raw29910step0Labels = raw29910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29910 raw29910Labels permutation434 hz
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical29911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29911 raw29911Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw29911 raw29911Labels = mixedMoment B raw29911step0 raw29911step0Labels := by
      have hz : ∀ j, raw29911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29911step0 = (fun i j => raw29911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29911step0 raw29911; decide +kernel
      have hl : raw29911step0Labels = raw29911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29911 raw29911Labels permutation434 hz
    mixedMoment B raw29911step0 raw29911step0Labels = mixedMoment B raw29911step1 raw29911step1Labels := by
      have ha : raw29911step1 = (fun i j => raw29911step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29911step1 raw29911step0; decide +kernel
      have hl : raw29911step1Labels = raw29911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29911step0 raw29911step0Labels permutation36 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical29912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29912 raw29912Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw29912 raw29912Labels = mixedMoment B raw29912step0 raw29912step0Labels := by
      have hz : ∀ j, raw29912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29912step0 = (fun i j => raw29912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29912step0 raw29912; decide +kernel
      have hl : raw29912step0Labels = raw29912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29912 raw29912Labels permutation434 hz
    mixedMoment B raw29912step0 raw29912step0Labels = mixedMoment B raw29912step1 raw29912step1Labels := by
      have ha : raw29912step1 = (fun i j => raw29912step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29912step1 raw29912step0; decide +kernel
      have hl : raw29912step1Labels = raw29912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29912step0 raw29912step0Labels permutation36 permutation2
    mixedMoment B raw29912step1 raw29912step1Labels = mixedMoment B raw29912step2 raw29912step2Labels := by
      have ha : raw29912step2 = -raw29912step1 := by apply Matrix.ext; change ∀ i j, raw29912step2 i j = -(raw29912step1 i j); unfold raw29912step2 raw29912step1; decide +kernel
      have hl : raw29912step2Labels = raw29912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3348 node3348Labels := by rfl

theorem canonical29913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29913 raw29913Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw29913 raw29913Labels = mixedMoment B raw29913step0 raw29913step0Labels := by
      have ha : raw29913step0 = (fun i j => raw29913 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29913step0 raw29913; decide +kernel
      have hl : raw29913step0Labels = raw29913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29913 raw29913Labels permutation170 permutation2
    mixedMoment B raw29913step0 raw29913step0Labels = mixedMoment B raw29913step1 raw29913step1Labels := by
      have ha : raw29913step1 = -raw29913step0 := by apply Matrix.ext; change ∀ i j, raw29913step1 i j = -(raw29913step0 i j); unfold raw29913step1 raw29913step0; decide +kernel
      have hl : raw29913step1Labels = raw29913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3345 node3345Labels := by rfl

theorem canonical29914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29914 raw29914Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw29914 raw29914Labels = mixedMoment B raw29914step0 raw29914step0Labels := by
      have hz : ∀ j, raw29914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29914step0 = (fun i j => raw29914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29914step0 raw29914; decide +kernel
      have hl : raw29914step0Labels = raw29914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29914 raw29914Labels permutation434 hz
    mixedMoment B raw29914step0 raw29914step0Labels = mixedMoment B raw29914step1 raw29914step1Labels := by
      have ha : raw29914step1 = (fun i j => raw29914step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29914step1 raw29914step0; decide +kernel
      have hl : raw29914step1Labels = raw29914step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29914step0 raw29914step0Labels permutation121 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

theorem canonical29915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29915 raw29915Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw29915 raw29915Labels = mixedMoment B raw29915step0 raw29915step0Labels := by
      have hz : ∀ j, raw29915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29915step0 = (fun i j => raw29915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29915step0 raw29915; decide +kernel
      have hl : raw29915step0Labels = raw29915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29915 raw29915Labels permutation434 hz
    mixedMoment B raw29915step0 raw29915step0Labels = mixedMoment B raw29915step1 raw29915step1Labels := by
      have ha : raw29915step1 = (fun i j => raw29915step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29915step1 raw29915step0; decide +kernel
      have hl : raw29915step1Labels = raw29915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29915step0 raw29915step0Labels permutation33 permutation2
    mixedMoment B raw29915step1 raw29915step1Labels = mixedMoment B raw29915step2 raw29915step2Labels := by
      have ha : raw29915step2 = -raw29915step1 := by apply Matrix.ext; change ∀ i j, raw29915step2 i j = -(raw29915step1 i j); unfold raw29915step2 raw29915step1; decide +kernel
      have hl : raw29915step2Labels = raw29915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3354 node3354Labels := by rfl

theorem canonical29916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29916 raw29916Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw29916 raw29916Labels = mixedMoment B raw29916step0 raw29916step0Labels := by
      have hz : ∀ j, raw29916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29916step0 = (fun i j => raw29916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29916step0 raw29916; decide +kernel
      have hl : raw29916step0Labels = raw29916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29916 raw29916Labels permutation434 hz
    mixedMoment B raw29916step0 raw29916step0Labels = mixedMoment B raw29916step1 raw29916step1Labels := by
      have ha : raw29916step1 = (fun i j => raw29916step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29916step1 raw29916step0; decide +kernel
      have hl : raw29916step1Labels = raw29916step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29916step0 raw29916step0Labels permutation38 permutation4
    mixedMoment B raw29916step1 raw29916step1Labels = mixedMoment B raw29916step2 raw29916step2Labels := by
      have ha : raw29916step2 = -raw29916step1 := by apply Matrix.ext; change ∀ i j, raw29916step2 i j = -(raw29916step1 i j); unfold raw29916step2 raw29916step1; decide +kernel
      have hl : raw29916step2Labels = raw29916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical29917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29917 raw29917Labels = mixedMoment B node3386 node3386Labels := by
  calc
    mixedMoment B raw29917 raw29917Labels = mixedMoment B raw29917step0 raw29917step0Labels := by
      have hz : ∀ j, raw29917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29917step0 = (fun i j => raw29917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29917step0 raw29917; decide +kernel
      have hl : raw29917step0Labels = raw29917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29917 raw29917Labels permutation434 hz
    mixedMoment B raw29917step0 raw29917step0Labels = mixedMoment B raw29917step1 raw29917step1Labels := by
      have ha : raw29917step1 = (fun i j => raw29917step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29917step1 raw29917step0; decide +kernel
      have hl : raw29917step1Labels = raw29917step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29917step0 raw29917step0Labels permutation38 permutation4
    mixedMoment B raw29917step1 raw29917step1Labels = mixedMoment B raw29917step2 raw29917step2Labels := by
      have ha : raw29917step2 = -raw29917step1 := by apply Matrix.ext; change ∀ i j, raw29917step2 i j = -(raw29917step1 i j); unfold raw29917step2 raw29917step1; decide +kernel
      have hl : raw29917step2Labels = raw29917step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3386 node3386Labels := by rfl

theorem canonical29918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29918 raw29918Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw29918 raw29918Labels = mixedMoment B raw29918step0 raw29918step0Labels := by
      have ha : raw29918step0 = (fun i j => raw29918 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29918step0 raw29918; decide +kernel
      have hl : raw29918step0Labels = raw29918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29918 raw29918Labels permutation182 permutation4
    mixedMoment B raw29918step0 raw29918step0Labels = mixedMoment B raw29918step1 raw29918step1Labels := by
      have ha : raw29918step1 = -raw29918step0 := by apply Matrix.ext; change ∀ i j, raw29918step1 i j = -(raw29918step0 i j); unfold raw29918step1 raw29918step0; decide +kernel
      have hl : raw29918step1Labels = raw29918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3491 node3491Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1171 node1171Labels = Sparse.eval nodeValue1171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1171) = mixedMoment B node1171 node1171Labels := rfl
  simpa [nodeValue1171, Sparse.eval] using hc.symm

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

theorem sound1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1321 node1321Labels = Sparse.eval nodeValue1321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1321) = mixedMoment B node1321 node1321Labels := rfl
  simpa [nodeValue1321, Sparse.eval] using hc.symm

theorem sound1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1328 node1328Labels = Sparse.eval nodeValue1328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1328) = mixedMoment B node1328 node1328Labels := rfl
  simpa [nodeValue1328, Sparse.eval] using hc.symm

theorem sound1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1338 node1338Labels = Sparse.eval nodeValue1338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1338) = mixedMoment B node1338 node1338Labels := rfl
  simpa [nodeValue1338, Sparse.eval] using hc.symm

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

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1682 node1682Labels = Sparse.eval nodeValue1682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1682) = mixedMoment B node1682 node1682Labels := rfl
  simpa [nodeValue1682, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

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

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

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

theorem sound1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1812 node1812Labels = Sparse.eval nodeValue1812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1812) = mixedMoment B node1812 node1812Labels := rfl
  simpa [nodeValue1812, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2326 node2326Labels = Sparse.eval nodeValue2326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2326) = mixedMoment B node2326 node2326Labels := rfl
  simpa [nodeValue2326, Sparse.eval] using hc.symm

theorem sound2352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2352 node2352Labels = Sparse.eval nodeValue2352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2352) = mixedMoment B node2352 node2352Labels := rfl
  simpa [nodeValue2352, Sparse.eval] using hc.symm

theorem sound2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2355 node2355Labels = Sparse.eval nodeValue2355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2355) = mixedMoment B node2355 node2355Labels := rfl
  simpa [nodeValue2355, Sparse.eval] using hc.symm

theorem sound2362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2362 node2362Labels = Sparse.eval nodeValue2362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2362) = mixedMoment B node2362 node2362Labels := rfl
  simpa [nodeValue2362, Sparse.eval] using hc.symm

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

theorem sound2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2396 node2396Labels = Sparse.eval nodeValue2396 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2396) = mixedMoment B node2396 node2396Labels := rfl
  simpa [nodeValue2396, Sparse.eval] using hc.symm

theorem sound2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2399 node2399Labels = Sparse.eval nodeValue2399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2399) = mixedMoment B node2399 node2399Labels := rfl
  simpa [nodeValue2399, Sparse.eval] using hc.symm

theorem sound2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2401 node2401Labels = Sparse.eval nodeValue2401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2401) = mixedMoment B node2401 node2401Labels := rfl
  simpa [nodeValue2401, Sparse.eval] using hc.symm

theorem sound2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2405 node2405Labels = Sparse.eval nodeValue2405 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2405) = mixedMoment B node2405 node2405Labels := rfl
  simpa [nodeValue2405, Sparse.eval] using hc.symm

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

theorem sound2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2438 node2438Labels = Sparse.eval nodeValue2438 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2438) = mixedMoment B node2438 node2438Labels := rfl
  simpa [nodeValue2438, Sparse.eval] using hc.symm

theorem sound2443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2443 node2443Labels = Sparse.eval nodeValue2443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2443) = mixedMoment B node2443 node2443Labels := rfl
  simpa [nodeValue2443, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2529 node2529Labels = Sparse.eval nodeValue2529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2529) = mixedMoment B node2529 node2529Labels := rfl
  simpa [nodeValue2529, Sparse.eval] using hc.symm

theorem sound2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2538 node2538Labels = Sparse.eval nodeValue2538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2538) = mixedMoment B node2538 node2538Labels := rfl
  simpa [nodeValue2538, Sparse.eval] using hc.symm

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

theorem sound2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2575 node2575Labels = Sparse.eval nodeValue2575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2575) = mixedMoment B node2575 node2575Labels := rfl
  simpa [nodeValue2575, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2600 node2600Labels = Sparse.eval nodeValue2600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2600) = mixedMoment B node2600 node2600Labels := rfl
  simpa [nodeValue2600, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

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

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

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

theorem sound2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2798 node2798Labels = Sparse.eval nodeValue2798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2798) = mixedMoment B node2798 node2798Labels := rfl
  simpa [nodeValue2798, Sparse.eval] using hc.symm

theorem sound2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2802 node2802Labels = Sparse.eval nodeValue2802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2802) = mixedMoment B node2802 node2802Labels := rfl
  simpa [nodeValue2802, Sparse.eval] using hc.symm

theorem sound2803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2803 node2803Labels = Sparse.eval nodeValue2803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2803) = mixedMoment B node2803 node2803Labels := rfl
  simpa [nodeValue2803, Sparse.eval] using hc.symm

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

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

theorem sound2822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2822 node2822Labels = Sparse.eval nodeValue2822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2822) = mixedMoment B node2822 node2822Labels := rfl
  simpa [nodeValue2822, Sparse.eval] using hc.symm

theorem sound2827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2827 node2827Labels = Sparse.eval nodeValue2827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2827) = mixedMoment B node2827 node2827Labels := rfl
  simpa [nodeValue2827, Sparse.eval] using hc.symm

theorem sound2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2848 node2848Labels = Sparse.eval nodeValue2848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2848) = mixedMoment B node2848 node2848Labels := rfl
  simpa [nodeValue2848, Sparse.eval] using hc.symm

theorem sound2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2867 node2867Labels = Sparse.eval nodeValue2867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2867) = mixedMoment B node2867 node2867Labels := rfl
  simpa [nodeValue2867, Sparse.eval] using hc.symm

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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2885 node2885Labels = Sparse.eval nodeValue2885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2885) = mixedMoment B node2885 node2885Labels := rfl
  simpa [nodeValue2885, Sparse.eval] using hc.symm

theorem sound2892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2892 node2892Labels = Sparse.eval nodeValue2892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2892) = mixedMoment B node2892 node2892Labels := rfl
  simpa [nodeValue2892, Sparse.eval] using hc.symm

theorem sound2893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2893 node2893Labels = Sparse.eval nodeValue2893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2893) = mixedMoment B node2893 node2893Labels := rfl
  simpa [nodeValue2893, Sparse.eval] using hc.symm

theorem sound2899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2899 node2899Labels = Sparse.eval nodeValue2899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2899) = mixedMoment B node2899 node2899Labels := rfl
  simpa [nodeValue2899, Sparse.eval] using hc.symm

theorem sound2900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2900 node2900Labels = Sparse.eval nodeValue2900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2900) = mixedMoment B node2900 node2900Labels := rfl
  simpa [nodeValue2900, Sparse.eval] using hc.symm

theorem sound2910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2910 node2910Labels = Sparse.eval nodeValue2910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2910) = mixedMoment B node2910 node2910Labels := rfl
  simpa [nodeValue2910, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2925 node2925Labels = Sparse.eval nodeValue2925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2925) = mixedMoment B node2925 node2925Labels := rfl
  simpa [nodeValue2925, Sparse.eval] using hc.symm

theorem sound2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2930 node2930Labels = Sparse.eval nodeValue2930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2930) = mixedMoment B node2930 node2930Labels := rfl
  simpa [nodeValue2930, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3345 node3345Labels = Sparse.eval nodeValue3345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3345) = mixedMoment B node3345 node3345Labels := rfl
  simpa [nodeValue3345, Sparse.eval] using hc.symm

theorem sound3346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3346 node3346Labels = Sparse.eval nodeValue3346 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3346) = mixedMoment B node3346 node3346Labels := rfl
  simpa [nodeValue3346, Sparse.eval] using hc.symm

theorem sound3348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3348 node3348Labels = Sparse.eval nodeValue3348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3348) = mixedMoment B node3348 node3348Labels := rfl
  simpa [nodeValue3348, Sparse.eval] using hc.symm

theorem sound3349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3349 node3349Labels = Sparse.eval nodeValue3349 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3349) = mixedMoment B node3349 node3349Labels := rfl
  simpa [nodeValue3349, Sparse.eval] using hc.symm

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

theorem sound3357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3357 node3357Labels = Sparse.eval nodeValue3357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3357) = mixedMoment B node3357 node3357Labels := rfl
  simpa [nodeValue3357, Sparse.eval] using hc.symm

theorem sound3386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3386 node3386Labels = Sparse.eval nodeValue3386 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3386) = mixedMoment B node3386 node3386Labels := rfl
  simpa [nodeValue3386, Sparse.eval] using hc.symm

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

theorem zero3439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3439 node3439Labels = 0 := by
  exact mixedMoment_order_one B hB node3439 node3439Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

theorem sound3419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3419 node3419Labels = Sparse.eval nodeValue3419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3419) = mixedMoment B node3419 node3419Labels := rfl
  simpa [nodeValue3419, Sparse.eval] using hc.symm

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

theorem sound3439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3439 node3439Labels = Sparse.eval nodeValue3439 (mixedVector B) := by
  simpa only [nodeValue3439, Sparse.eval_nil] using zero3439 B _hB _hF

theorem sound3452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3452 node3452Labels = Sparse.eval nodeValue3452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3452) = mixedMoment B node3452 node3452Labels := rfl
  simpa [nodeValue3452, Sparse.eval] using hc.symm

theorem sound3454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3454 node3454Labels = Sparse.eval nodeValue3454 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3454) = mixedMoment B node3454 node3454Labels := rfl
  simpa [nodeValue3454, Sparse.eval] using hc.symm

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

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

theorem sound3491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3491 node3491Labels = Sparse.eval nodeValue3491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3491) = mixedMoment B node3491 node3491Labels := rfl
  simpa [nodeValue3491, Sparse.eval] using hc.symm

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

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

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

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

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

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3599 node3599Labels = Sparse.eval nodeValue3599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3599) = mixedMoment B node3599 node3599Labels := rfl
  simpa [nodeValue3599, Sparse.eval] using hc.symm

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem zero3774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3774 node3774Labels = 0 := by
  exact mixedMoment_order_one B hB node3774 node3774Labels 1
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

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

theorem sound3774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3774 node3774Labels = Sparse.eval nodeValue3774 (mixedVector B) := by
  simpa only [nodeValue3774, Sparse.eval_nil] using zero3774 B _hB _hF

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

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2147 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 0) (sourceB2147 + difference 0 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 0) (sourceB2147 + difference 0 3) sourceC2147) = raw29700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29700; decide +kernel
    rw [ha]
    exact (canonical29700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 1) (sourceB2147 + difference 1 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 1) (sourceB2147 + difference 1 3) sourceC2147) = raw29701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29701; decide +kernel
    rw [ha]
    exact (canonical29701 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 2) (sourceB2147 + difference 2 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2529) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 2) (sourceB2147 + difference 2 3) sourceC2147) = raw29702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29702; decide +kernel
    rw [ha]
    exact (canonical29702 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 3) (sourceB2147 + difference 3 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 3) (sourceB2147 + difference 3 3) sourceC2147) = raw29703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29703; decide +kernel
    rw [ha]
    exact (canonical29703 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 4) (sourceB2147 + difference 4 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 4) (sourceB2147 + difference 4 3) sourceC2147) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 5) (sourceB2147 + difference 5 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 5) (sourceB2147 + difference 5 3) sourceC2147) = raw29704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29704; decide +kernel
    rw [ha]
    exact (canonical29704 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2147 + sourceB2147) sourceC2147) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2147 + sourceB2147) sourceC2147) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA2147 sourceB2147 sourceC2147 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2147 sourceB2147 sourceC2147
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2147, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2148 + difference 0 3) (sourceB2148 + difference 3 0) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2148 + difference 0 3) (sourceB2148 + difference 3 0) sourceC2148) = raw29705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29705; decide +kernel
    rw [ha]
    exact (canonical29705 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2148 + difference 1 3) (sourceB2148 + difference 3 1) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2148 + difference 1 3) (sourceB2148 + difference 3 1) sourceC2148) = raw29706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29706; decide +kernel
    rw [ha]
    exact (canonical29706 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2148 + difference 2 3) (sourceB2148 + difference 3 2) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2148 + difference 2 3) (sourceB2148 + difference 3 2) sourceC2148) = raw29707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29707; decide +kernel
    rw [ha]
    exact (canonical29707 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2148 + difference 3 3) (sourceB2148 + difference 3 3) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2148 + difference 3 3) (sourceB2148 + difference 3 3) sourceC2148) = raw29708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29708; decide +kernel
    rw [ha]
    exact (canonical29708 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2148 + difference 4 3) (sourceB2148 + difference 3 4) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA2148 + difference 4 3) (sourceB2148 + difference 3 4) sourceC2148) = raw29709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29709; decide +kernel
    rw [ha]
    exact (canonical29709 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2148 + difference 5 3) (sourceB2148 + difference 3 5) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2148 + difference 5 3) (sourceB2148 + difference 3 5) sourceC2148) = raw29710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29710; decide +kernel
    rw [ha]
    exact (canonical29710 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2148 + sourceB2148) sourceC2148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2148 + sourceB2148) sourceC2148) = raw29711 := by
      apply Matrix.ext; unfold doubleCharges sourceA2148 sourceB2148 sourceC2148 raw29711; decide +kernel
    rw [ha]
    exact (canonical29711 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2148 sourceB2148 sourceC2148
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2148, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2149 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2149 + difference 0 5) (sourceB2149 + difference 5 0) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2149 + difference 0 5) (sourceB2149 + difference 5 0) sourceC2149) = raw29712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29712; decide +kernel
    rw [ha]
    exact (canonical29712 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2149 + difference 1 5) (sourceB2149 + difference 5 1) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA2149 + difference 1 5) (sourceB2149 + difference 5 1) sourceC2149) = raw29353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29353; decide +kernel
    rw [ha]
    exact (canonical29353 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2149 + difference 2 5) (sourceB2149 + difference 5 2) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA2149 + difference 2 5) (sourceB2149 + difference 5 2) sourceC2149) = raw29330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29330; decide +kernel
    rw [ha]
    exact (canonical29330 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2149 + difference 3 5) (sourceB2149 + difference 5 3) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA2149 + difference 3 5) (sourceB2149 + difference 5 3) sourceC2149) = raw29713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29713; decide +kernel
    rw [ha]
    exact (canonical29713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2149 + difference 4 5) (sourceB2149 + difference 5 4) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2149 + difference 4 5) (sourceB2149 + difference 5 4) sourceC2149) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2149 + difference 5 5) (sourceB2149 + difference 5 5) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2149 + difference 5 5) (sourceB2149 + difference 5 5) sourceC2149) = raw29714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29714; decide +kernel
    rw [ha]
    exact (canonical29714 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2149 + sourceB2149) sourceC2149) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2149 + sourceB2149) sourceC2149) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2149 sourceB2149 sourceC2149 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2149 sourceB2149 sourceC2149
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2149, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 1) (sourceB2154 + difference 1 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 1) (sourceB2154 + difference 1 0) sourceC2154) = raw17754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17754; decide +kernel
    rw [ha]
    exact (canonical17754 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 2) (sourceB2154 + difference 2 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 2) (sourceB2154 + difference 2 0) sourceC2154) = raw17755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17755; decide +kernel
    rw [ha]
    exact (canonical17755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 3) (sourceB2154 + difference 3 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 3) (sourceB2154 + difference 3 0) sourceC2154) = raw17756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17756; decide +kernel
    rw [ha]
    exact (canonical17756 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 4) (sourceB2154 + difference 4 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 4) (sourceB2154 + difference 4 0) sourceC2154) = raw29787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29787; decide +kernel
    rw [ha]
    exact (canonical29787 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 5) (sourceB2154 + difference 5 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 5) (sourceB2154 + difference 5 0) sourceC2154) = raw17757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17757; decide +kernel
    rw [ha]
    exact (canonical17757 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 0) (sourceB2154 + difference 0 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 0) (sourceB2154 + difference 0 1) sourceC2154) = raw29788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29788; decide +kernel
    rw [ha]
    exact (canonical29788 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 2) (sourceB2154 + difference 2 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 2) (sourceB2154 + difference 2 1) sourceC2154) = raw29789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29789; decide +kernel
    rw [ha]
    exact (canonical29789 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 3) (sourceB2154 + difference 3 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 3) (sourceB2154 + difference 3 1) sourceC2154) = raw29790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29790; decide +kernel
    rw [ha]
    exact (canonical29790 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 4) (sourceB2154 + difference 4 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 4) (sourceB2154 + difference 4 1) sourceC2154) = raw17738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17738; decide +kernel
    rw [ha]
    exact (canonical17738 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 5) (sourceB2154 + difference 5 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 5) (sourceB2154 + difference 5 1) sourceC2154) = raw29791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29791; decide +kernel
    rw [ha]
    exact (canonical29791 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 0) (sourceB2154 + difference 0 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 0) (sourceB2154 + difference 0 2) sourceC2154) = raw29792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29792; decide +kernel
    rw [ha]
    exact (canonical29792 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 1) (sourceB2154 + difference 1 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 1) (sourceB2154 + difference 1 2) sourceC2154) = raw29793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29793; decide +kernel
    rw [ha]
    exact (canonical29793 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 3) (sourceB2154 + difference 3 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3599) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 3) (sourceB2154 + difference 3 2) sourceC2154) = raw29794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29794; decide +kernel
    rw [ha]
    exact (canonical29794 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 4) (sourceB2154 + difference 4 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 4) (sourceB2154 + difference 4 2) sourceC2154) = raw17743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17743; decide +kernel
    rw [ha]
    exact (canonical17743 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 5) (sourceB2154 + difference 5 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 5) (sourceB2154 + difference 5 2) sourceC2154) = raw29795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29795; decide +kernel
    rw [ha]
    exact (canonical29795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 0) (sourceB2154 + difference 0 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 0) (sourceB2154 + difference 0 3) sourceC2154) = raw29796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29796; decide +kernel
    rw [ha]
    exact (canonical29796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 1) (sourceB2154 + difference 1 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 1) (sourceB2154 + difference 1 3) sourceC2154) = raw29797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29797; decide +kernel
    rw [ha]
    exact (canonical29797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 2) (sourceB2154 + difference 2 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 2) (sourceB2154 + difference 2 3) sourceC2154) = raw29798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29798; decide +kernel
    rw [ha]
    exact (canonical29798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 4) (sourceB2154 + difference 4 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 4) (sourceB2154 + difference 4 3) sourceC2154) = raw17748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17748; decide +kernel
    rw [ha]
    exact (canonical17748 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 5) (sourceB2154 + difference 5 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 5) (sourceB2154 + difference 5 3) sourceC2154) = raw29799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29799; decide +kernel
    rw [ha]
    exact (canonical29799 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 0) (sourceB2154 + difference 0 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 0) (sourceB2154 + difference 0 4) sourceC2154) = raw29800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29800; decide +kernel
    rw [ha]
    exact (canonical29800 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 1) (sourceB2154 + difference 1 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 1) (sourceB2154 + difference 1 4) sourceC2154) = raw29801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29801; decide +kernel
    rw [ha]
    exact (canonical29801 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 2) (sourceB2154 + difference 2 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 2) (sourceB2154 + difference 2 4) sourceC2154) = raw29802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29802; decide +kernel
    rw [ha]
    exact (canonical29802 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 3) (sourceB2154 + difference 3 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 3) (sourceB2154 + difference 3 4) sourceC2154) = raw29803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29803; decide +kernel
    rw [ha]
    exact (canonical29803 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 5) (sourceB2154 + difference 5 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 5) (sourceB2154 + difference 5 4) sourceC2154) = raw29804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29804; decide +kernel
    rw [ha]
    exact (canonical29804 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 0) (sourceB2154 + difference 0 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 0) (sourceB2154 + difference 0 5) sourceC2154) = raw29805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29805; decide +kernel
    rw [ha]
    exact (canonical29805 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 1) (sourceB2154 + difference 1 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 1) (sourceB2154 + difference 1 5) sourceC2154) = raw29806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29806; decide +kernel
    rw [ha]
    exact (canonical29806 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 2) (sourceB2154 + difference 2 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 2) (sourceB2154 + difference 2 5) sourceC2154) = raw29807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29807; decide +kernel
    rw [ha]
    exact (canonical29807 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 3) (sourceB2154 + difference 3 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 3) (sourceB2154 + difference 3 5) sourceC2154) = raw29808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29808; decide +kernel
    rw [ha]
    exact (canonical29808 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 4) (sourceB2154 + difference 4 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 4) (sourceB2154 + difference 4 5) sourceC2154) = raw17758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17758; decide +kernel
    rw [ha]
    exact (canonical17758 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2154 sourceB2154 sourceC2154
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2154, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2155 + difference 0 1) (sourceB2155 + difference 1 0) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2155 + difference 0 1) (sourceB2155 + difference 1 0) sourceC2155) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2155 + difference 1 1) (sourceB2155 + difference 1 1) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2155 + difference 1 1) (sourceB2155 + difference 1 1) sourceC2155) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2155 + difference 2 1) (sourceB2155 + difference 1 2) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2155 + difference 2 1) (sourceB2155 + difference 1 2) sourceC2155) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2155 + difference 3 1) (sourceB2155 + difference 1 3) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2155 + difference 3 1) (sourceB2155 + difference 1 3) sourceC2155) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2155 + difference 4 1) (sourceB2155 + difference 1 4) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2155 + difference 4 1) (sourceB2155 + difference 1 4) sourceC2155) = raw29812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29812; decide +kernel
    rw [ha]
    exact (canonical29812 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2155 + difference 5 1) (sourceB2155 + difference 1 5) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2155 + difference 5 1) (sourceB2155 + difference 1 5) sourceC2155) = raw27825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw27825; decide +kernel
    rw [ha]
    exact (canonical27825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2155 + sourceB2155) sourceC2155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2155 + sourceB2155) sourceC2155) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2155 sourceB2155 sourceC2155 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2155 sourceB2155 sourceC2155
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2155, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 0) (sourceB2156 + difference 0 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 0) (sourceB2156 + difference 0 2) sourceC2156) = raw29813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29813; decide +kernel
    rw [ha]
    exact (canonical29813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 1) (sourceB2156 + difference 1 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 1) (sourceB2156 + difference 1 2) sourceC2156) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 2) (sourceB2156 + difference 2 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 2) (sourceB2156 + difference 2 2) sourceC2156) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 3) (sourceB2156 + difference 3 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 3) (sourceB2156 + difference 3 2) sourceC2156) = raw29814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29814; decide +kernel
    rw [ha]
    exact (canonical29814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 4) (sourceB2156 + difference 4 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 4) (sourceB2156 + difference 4 2) sourceC2156) = raw29815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29815; decide +kernel
    rw [ha]
    exact (canonical29815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 5) (sourceB2156 + difference 5 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 5) (sourceB2156 + difference 5 2) sourceC2156) = raw29816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29816; decide +kernel
    rw [ha]
    exact (canonical29816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2156 + sourceB2156) sourceC2156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2156 + sourceB2156) sourceC2156) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2156 sourceB2156 sourceC2156 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2156 sourceB2156 sourceC2156
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2156, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2157 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 0) (sourceB2157 + difference 0 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 0) (sourceB2157 + difference 0 3) sourceC2157) = raw29817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29817; decide +kernel
    rw [ha]
    exact (canonical29817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 1) (sourceB2157 + difference 1 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 1) (sourceB2157 + difference 1 3) sourceC2157) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 2) (sourceB2157 + difference 2 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 2) (sourceB2157 + difference 2 3) sourceC2157) = raw29818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29818; decide +kernel
    rw [ha]
    exact (canonical29818 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 3) (sourceB2157 + difference 3 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 3) (sourceB2157 + difference 3 3) sourceC2157) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 4) (sourceB2157 + difference 4 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 4) (sourceB2157 + difference 4 3) sourceC2157) = raw29819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29819; decide +kernel
    rw [ha]
    exact (canonical29819 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 5) (sourceB2157 + difference 5 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 5) (sourceB2157 + difference 5 3) sourceC2157) = raw29820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29820; decide +kernel
    rw [ha]
    exact (canonical29820 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2157 + sourceB2157) sourceC2157) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2157 + sourceB2157) sourceC2157) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2157 sourceB2157 sourceC2157 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2157 sourceB2157 sourceC2157
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2157, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2160 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 0) (sourceB2160 + difference 0 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 0) (sourceB2160 + difference 0 0) sourceC2160) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 1) (sourceB2160 + difference 1 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 1) (sourceB2160 + difference 1 0) sourceC2160) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 2) (sourceB2160 + difference 2 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 2) (sourceB2160 + difference 2 0) sourceC2160) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 3) (sourceB2160 + difference 3 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 3) (sourceB2160 + difference 3 0) sourceC2160) = raw29698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29698; decide +kernel
    rw [ha]
    exact (canonical29698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 4) (sourceB2160 + difference 4 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 4) (sourceB2160 + difference 4 0) sourceC2160) = raw29712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29712; decide +kernel
    rw [ha]
    exact (canonical29712 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 5) (sourceB2160 + difference 5 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 5) (sourceB2160 + difference 5 0) sourceC2160) = raw29860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29860; decide +kernel
    rw [ha]
    exact (canonical29860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2160 + sourceB2160) sourceC2160) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2160 + sourceB2160) sourceC2160) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2160 sourceB2160 sourceC2160 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2160 sourceB2160 sourceC2160
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2160, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2161 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 0) (sourceB2161 + difference 0 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 0) (sourceB2161 + difference 0 0) sourceC2161) = raw29861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29861; decide +kernel
    rw [ha]
    exact (canonical29861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 1) (sourceB2161 + difference 1 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3349) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 1) (sourceB2161 + difference 1 0) sourceC2161) = raw29862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29862; decide +kernel
    rw [ha]
    exact (canonical29862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 2) (sourceB2161 + difference 2 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 2) (sourceB2161 + difference 2 0) sourceC2161) = raw29863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29863; decide +kernel
    rw [ha]
    exact (canonical29863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 3) (sourceB2161 + difference 3 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3357) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 3) (sourceB2161 + difference 3 0) sourceC2161) = raw29864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29864; decide +kernel
    rw [ha]
    exact (canonical29864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 4) (sourceB2161 + difference 4 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 4) (sourceB2161 + difference 4 0) sourceC2161) = raw29865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29865; decide +kernel
    rw [ha]
    exact (canonical29865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 5) (sourceB2161 + difference 5 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 5) (sourceB2161 + difference 5 0) sourceC2161) = raw29866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29866; decide +kernel
    rw [ha]
    exact (canonical29866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2161 + sourceB2161) sourceC2161) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2161 + sourceB2161) sourceC2161) = raw29867 := by
      apply Matrix.ext; unfold doubleCharges sourceA2161 sourceB2161 sourceC2161 raw29867; decide +kernel
    rw [ha]
    exact (canonical29867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2161 sourceB2161 sourceC2161
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2161, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2168 + difference 0 2) (sourceB2168 + difference 2 0) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2168 + difference 0 2) (sourceB2168 + difference 2 0) sourceC2168) = raw29894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29894; decide +kernel
    rw [ha]
    exact (canonical29894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2168 + difference 1 2) (sourceB2168 + difference 2 1) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2168 + difference 1 2) (sourceB2168 + difference 2 1) sourceC2168) = raw29895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29895; decide +kernel
    rw [ha]
    exact (canonical29895 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2168 + difference 2 2) (sourceB2168 + difference 2 2) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA2168 + difference 2 2) (sourceB2168 + difference 2 2) sourceC2168) = raw29896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29896; decide +kernel
    rw [ha]
    exact (canonical29896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2168 + difference 3 2) (sourceB2168 + difference 2 3) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2438) := by
    have ha : (tripleCharges (sourceA2168 + difference 3 2) (sourceB2168 + difference 2 3) sourceC2168) = raw29897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29897; decide +kernel
    rw [ha]
    exact (canonical29897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2168 + difference 4 2) (sourceB2168 + difference 2 4) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA2168 + difference 4 2) (sourceB2168 + difference 2 4) sourceC2168) = raw29898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29898; decide +kernel
    rw [ha]
    exact (canonical29898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2168 + difference 5 2) (sourceB2168 + difference 2 5) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2168 + difference 5 2) (sourceB2168 + difference 2 5) sourceC2168) = raw29899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29899; decide +kernel
    rw [ha]
    exact (canonical29899 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2168 + sourceB2168) sourceC2168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2168 + sourceB2168) sourceC2168) = raw29900 := by
      apply Matrix.ext; unfold doubleCharges sourceA2168 sourceB2168 sourceC2168 raw29900; decide +kernel
    rw [ha]
    exact (canonical29900 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2168 sourceB2168 sourceC2168
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2168, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2169 + difference 0 1) (sourceB2169 + difference 1 0) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2169 + difference 0 1) (sourceB2169 + difference 1 0) sourceC2169) = raw29901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29901; decide +kernel
    rw [ha]
    exact (canonical29901 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2169 + difference 1 1) (sourceB2169 + difference 1 1) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2169 + difference 1 1) (sourceB2169 + difference 1 1) sourceC2169) = raw29902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29902; decide +kernel
    rw [ha]
    exact (canonical29902 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2169 + difference 2 1) (sourceB2169 + difference 1 2) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2169 + difference 2 1) (sourceB2169 + difference 1 2) sourceC2169) = raw29903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29903; decide +kernel
    rw [ha]
    exact (canonical29903 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2169 + difference 3 1) (sourceB2169 + difference 1 3) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2169 + difference 3 1) (sourceB2169 + difference 1 3) sourceC2169) = raw29904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29904; decide +kernel
    rw [ha]
    exact (canonical29904 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2169 + difference 4 1) (sourceB2169 + difference 1 4) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2169 + difference 4 1) (sourceB2169 + difference 1 4) sourceC2169) = raw29905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29905; decide +kernel
    rw [ha]
    exact (canonical29905 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2169 + difference 5 1) (sourceB2169 + difference 1 5) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2169 + difference 5 1) (sourceB2169 + difference 1 5) sourceC2169) = raw29906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29906; decide +kernel
    rw [ha]
    exact (canonical29906 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2169 + sourceB2169) sourceC2169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2169 + sourceB2169) sourceC2169) = raw29907 := by
      apply Matrix.ext; unfold doubleCharges sourceA2169 sourceB2169 sourceC2169 raw29907; decide +kernel
    rw [ha]
    exact (canonical29907 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2169 sourceB2169 sourceC2169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2169, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 0) (sourceB2170 + difference 0 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 0) (sourceB2170 + difference 0 2) sourceC2170) = raw29908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29908; decide +kernel
    rw [ha]
    exact (canonical29908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 1) (sourceB2170 + difference 1 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 1) (sourceB2170 + difference 1 2) sourceC2170) = raw29903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29903; decide +kernel
    rw [ha]
    exact (canonical29903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 2) (sourceB2170 + difference 2 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 2) (sourceB2170 + difference 2 2) sourceC2170) = raw29902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29902; decide +kernel
    rw [ha]
    exact (canonical29902 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 3) (sourceB2170 + difference 3 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2848) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 3) (sourceB2170 + difference 3 2) sourceC2170) = raw29909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29909; decide +kernel
    rw [ha]
    exact (canonical29909 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 4) (sourceB2170 + difference 4 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 4) (sourceB2170 + difference 4 2) sourceC2170) = raw29910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29910; decide +kernel
    rw [ha]
    exact (canonical29910 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 5) (sourceB2170 + difference 5 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 5) (sourceB2170 + difference 5 2) sourceC2170) = raw29911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29911; decide +kernel
    rw [ha]
    exact (canonical29911 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2170 + sourceB2170) sourceC2170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2170 + sourceB2170) sourceC2170) = raw29907 := by
      apply Matrix.ext; unfold doubleCharges sourceA2170 sourceB2170 sourceC2170 raw29907; decide +kernel
    rw [ha]
    exact (canonical29907 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2170 sourceB2170 sourceC2170
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2170, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2171 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 0) (sourceB2171 + difference 0 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 0) (sourceB2171 + difference 0 0) sourceC2171) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 1) (sourceB2171 + difference 1 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 1) (sourceB2171 + difference 1 0) sourceC2171) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 2) (sourceB2171 + difference 2 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 2) (sourceB2171 + difference 2 0) sourceC2171) = raw29912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29912; decide +kernel
    rw [ha]
    exact (canonical29912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 3) (sourceB2171 + difference 3 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 3) (sourceB2171 + difference 3 0) sourceC2171) = raw29913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29913; decide +kernel
    rw [ha]
    exact (canonical29913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 4) (sourceB2171 + difference 4 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 4) (sourceB2171 + difference 4 0) sourceC2171) = raw29914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29914; decide +kernel
    rw [ha]
    exact (canonical29914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 5) (sourceB2171 + difference 5 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 5) (sourceB2171 + difference 5 0) sourceC2171) = raw29915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29915; decide +kernel
    rw [ha]
    exact (canonical29915 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2171 + sourceB2171) sourceC2171) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2171 + sourceB2171) sourceC2171) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2171 sourceB2171 sourceC2171 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2171 sourceB2171 sourceC2171
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2171, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2172 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 0) (sourceB2172 + difference 0 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 0) (sourceB2172 + difference 0 4) sourceC2172) = raw29916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29916; decide +kernel
    rw [ha]
    exact (canonical29916 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 1) (sourceB2172 + difference 1 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 1) (sourceB2172 + difference 1 4) sourceC2172) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 2) (sourceB2172 + difference 2 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3386) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 2) (sourceB2172 + difference 2 4) sourceC2172) = raw29917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29917; decide +kernel
    rw [ha]
    exact (canonical29917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 3) (sourceB2172 + difference 3 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 3) (sourceB2172 + difference 3 4) sourceC2172) = raw29918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29918; decide +kernel
    rw [ha]
    exact (canonical29918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 4) (sourceB2172 + difference 4 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 4) (sourceB2172 + difference 4 4) sourceC2172) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 5) (sourceB2172 + difference 5 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 5) (sourceB2172 + difference 5 4) sourceC2172) = raw29496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29496; decide +kernel
    rw [ha]
    exact (canonical29496 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2172 + sourceB2172) sourceC2172) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2172 + sourceB2172) sourceC2172) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2172 sourceB2172 sourceC2172 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2172 sourceB2172 sourceC2172
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2172, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1792 : Integer.Sparse.reindex keyMap MixedData.row1792 = numericRow1792 := by decide +kernel

theorem numericCheck1792 (x : Master → ℝ) : Integer.Sparse.eval numericRow1792 x =
    (1 : ℝ) * reducedSource1792 x := by
  norm_num [numericRow1792, reducedSource1792, Integer.Sparse.eval, Sparse.eval, nodeValue1171, nodeValue2362, nodeValue2529, nodeValue2575, nodeValue2590, nodeValue2600, nodeValue4092]

theorem reindexCheck1793 : Integer.Sparse.reindex keyMap MixedData.row1793 = numericRow1793 := by decide +kernel

theorem numericCheck1793 (x : Master → ℝ) : Integer.Sparse.eval numericRow1793 x =
    (1 : ℝ) * reducedSource1793 x := by
  norm_num [numericRow1793, reducedSource1793, Integer.Sparse.eval, Sparse.eval, nodeValue1812, nodeValue2892, nodeValue2899, nodeValue2930, nodeValue3394, nodeValue4083]

theorem reindexCheck1794 : Integer.Sparse.reindex keyMap MixedData.row1794 = numericRow1794 := by decide +kernel

theorem numericCheck1794 (x : Master → ℝ) : Integer.Sparse.eval numericRow1794 x =
    (1 : ℝ) * reducedSource1794 x := by
  norm_num [numericRow1794, reducedSource1794, Integer.Sparse.eval, Sparse.eval, nodeValue2396, nodeValue2399, nodeValue2401, nodeValue2405, nodeValue2681, nodeValue3612, nodeValue4082]

theorem reindexCheck1797 : Integer.Sparse.reindex keyMap MixedData.row1797 = numericRow1797 := by decide +kernel

theorem numericCheck1797 (x : Master → ℝ) : Integer.Sparse.eval numericRow1797 x =
    (1 : ℝ) * reducedSource1797 x := by
  norm_num [numericRow1797, reducedSource1797, Integer.Sparse.eval, Sparse.eval, nodeValue1678, nodeValue1679, nodeValue1682, nodeValue1689, nodeValue1736, nodeValue3408, nodeValue3414, nodeValue3415, nodeValue3418, nodeValue3419, nodeValue3420, nodeValue3452, nodeValue3454, nodeValue3476, nodeValue3481, nodeValue3530, nodeValue3562, nodeValue3565, nodeValue3580, nodeValue3588, nodeValue3599, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3764, nodeValue3773, nodeValue3774, nodeValue3816, nodeValue3961]

theorem reindexCheck1798 : Integer.Sparse.reindex keyMap MixedData.row1798 = numericRow1798 := by decide +kernel

theorem numericCheck1798 (x : Master → ℝ) : Integer.Sparse.eval numericRow1798 x =
    (1 : ℝ) * reducedSource1798 x := by
  norm_num [numericRow1798, reducedSource1798, Integer.Sparse.eval, Sparse.eval, nodeValue2326, nodeValue2802, nodeValue2822, nodeValue2827, nodeValue2931, nodeValue3694, nodeValue4091]

theorem reindexCheck1799 : Integer.Sparse.reindex keyMap MixedData.row1799 = numericRow1799 := by decide +kernel

theorem numericCheck1799 (x : Master → ℝ) : Integer.Sparse.eval numericRow1799 x =
    (1 : ℝ) * reducedSource1799 x := by
  norm_num [numericRow1799, reducedSource1799, Integer.Sparse.eval, Sparse.eval, nodeValue1328, nodeValue2822, nodeValue2893, nodeValue2924, nodeValue2925, nodeValue2931, nodeValue4091]

theorem reindexCheck1800 : Integer.Sparse.reindex keyMap MixedData.row1800 = numericRow1800 := by decide +kernel

theorem numericCheck1800 (x : Master → ℝ) : Integer.Sparse.eval numericRow1800 x =
    (1 : ℝ) * reducedSource1800 x := by
  norm_num [numericRow1800, reducedSource1800, Integer.Sparse.eval, Sparse.eval, nodeValue1338, nodeValue2827, nodeValue2900, nodeValue2931, nodeValue2954, nodeValue2955, nodeValue4091]

theorem reindexCheck1801 : Integer.Sparse.reindex keyMap MixedData.row1801 = numericRow1801 := by decide +kernel

theorem numericCheck1801 (x : Master → ℝ) : Integer.Sparse.eval numericRow1801 x =
    (1 : ℝ) * reducedSource1801 x := by
  norm_num [numericRow1801, reducedSource1801, Integer.Sparse.eval, Sparse.eval, nodeValue2399, nodeValue3433, nodeValue3439, nodeValue3485, nodeValue3522, nodeValue3612, nodeValue4082]

theorem reindexCheck1802 : Integer.Sparse.reindex keyMap MixedData.row1802 = numericRow1802 := by decide +kernel

theorem numericCheck1802 (x : Master → ℝ) : Integer.Sparse.eval numericRow1802 x =
    (1 : ℝ) * reducedSource1802 x := by
  norm_num [numericRow1802, reducedSource1802, Integer.Sparse.eval, Sparse.eval, nodeValue2910, nodeValue3346, nodeValue3349, nodeValue3357, nodeValue3479, nodeValue3570, nodeValue4080]

theorem reindexCheck1803 : Integer.Sparse.reindex keyMap MixedData.row1803 = numericRow1803 := by decide +kernel

theorem numericCheck1803 (x : Master → ℝ) : Integer.Sparse.eval numericRow1803 x =
    (1 : ℝ) * reducedSource1803 x := by
  norm_num [numericRow1803, reducedSource1803, Integer.Sparse.eval, Sparse.eval, nodeValue2355, nodeValue2438, nodeValue2443, nodeValue2488, nodeValue2620, nodeValue3732, nodeValue4092]

theorem reindexCheck1804 : Integer.Sparse.reindex keyMap MixedData.row1804 = numericRow1804 := by decide +kernel

theorem numericCheck1804 (x : Master → ℝ) : Integer.Sparse.eval numericRow1804 x =
    (1 : ℝ) * reducedSource1804 x := by
  norm_num [numericRow1804, reducedSource1804, Integer.Sparse.eval, Sparse.eval, nodeValue2352, nodeValue2798, nodeValue2803, nodeValue2817, nodeValue2867, nodeValue3693, nodeValue4092]

theorem reindexCheck1805 : Integer.Sparse.reindex keyMap MixedData.row1805 = numericRow1805 := by decide +kernel

theorem numericCheck1805 (x : Master → ℝ) : Integer.Sparse.eval numericRow1805 x =
    (1 : ℝ) * reducedSource1805 x := by
  norm_num [numericRow1805, reducedSource1805, Integer.Sparse.eval, Sparse.eval, nodeValue1321, nodeValue2817, nodeValue2848, nodeValue2867, nodeValue2881, nodeValue2885, nodeValue4092]

theorem reindexCheck1806 : Integer.Sparse.reindex keyMap MixedData.row1806 = numericRow1806 := by decide +kernel

theorem numericCheck1806 (x : Master → ℝ) : Integer.Sparse.eval numericRow1806 x =
    (1 : ℝ) * reducedSource1806 x := by
  norm_num [numericRow1806, reducedSource1806, Integer.Sparse.eval, Sparse.eval, nodeValue2538, nodeValue3345, nodeValue3348, nodeValue3354, nodeValue3478, nodeValue3538, nodeValue4082]

theorem reindexCheck1807 : Integer.Sparse.reindex keyMap MixedData.row1807 = numericRow1807 := by decide +kernel

theorem numericCheck1807 (x : Master → ℝ) : Integer.Sparse.eval numericRow1807 x =
    (1 : ℝ) * reducedSource1807 x := by
  norm_num [numericRow1807, reducedSource1807, Integer.Sparse.eval, Sparse.eval, nodeValue2048, nodeValue3386, nodeValue3491, nodeValue3522, nodeValue3538, nodeValue3542, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1792 (mixedVector B) = 0 := by
  have h1171 : mixedVector B (Sum.inr 1171) = Sparse.eval nodeValue1171 (mixedVector B) := by
    change mixedMoment B node1171 node1171Labels = _
    exact sound1171 B hB hF
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h2529 : mixedVector B (Sum.inr 2529) = Sparse.eval nodeValue2529 (mixedVector B) := by
    change mixedMoment B node2529 node2529Labels = _
    exact sound2529 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2147, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1171, h2362, h2529, h2575, h2590, h2600, h4092, reducedSource1792] using sourceEq2147 B hB

theorem rowSound1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1792 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1792, numericCheck1792, reducedZero1792 B hB hF, mul_zero]

theorem reducedZero1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1793 (mixedVector B) = 0 := by
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h2892 : mixedVector B (Sum.inr 2892) = Sparse.eval nodeValue2892 (mixedVector B) := by
    change mixedMoment B node2892 node2892Labels = _
    exact sound2892 B hB hF
  have h2899 : mixedVector B (Sum.inr 2899) = Sparse.eval nodeValue2899 (mixedVector B) := by
    change mixedMoment B node2899 node2899Labels = _
    exact sound2899 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1812, h2892, h2899, h2930, h3394, h4083, reducedSource1793] using sourceEq2148 B hB

theorem rowSound1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1793 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1793, numericCheck1793, reducedZero1793 B hB hF, mul_zero]

theorem reducedZero1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1794 (mixedVector B) = 0 := by
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2149, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2396, h2399, h2401, h2405, h2681, h3612, h4082, reducedSource1794] using sourceEq2149 B hB

theorem rowSound1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1794 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1794, numericCheck1794, reducedZero1794 B hB hF, mul_zero]

theorem reducedZero1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1797 (mixedVector B) = 0 := by
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h3599 : mixedVector B (Sum.inr 3599) = Sparse.eval nodeValue3599 (mixedVector B) := by
    change mixedMoment B node3599 node3599Labels = _
    exact sound3599 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  simpa only [sourceForm2154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1678, h1679, h1682, h1689, h1736, h3408, h3414, h3415, h3418, h3419, h3420, h3452, h3454, h3476, h3481, h3530, h3562, h3565, h3580, h3588, h3599, h3605, h3606, h3612, h3625, h3764, h3773, h3774, h3816, h3961, reducedSource1797] using sourceEq2154 B hB

theorem rowSound1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1797 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1797, numericCheck1797, reducedZero1797 B hB hF, mul_zero]

theorem reducedZero1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1798 (mixedVector B) = 0 := by
  have h2326 : mixedVector B (Sum.inr 2326) = Sparse.eval nodeValue2326 (mixedVector B) := by
    change mixedMoment B node2326 node2326Labels = _
    exact sound2326 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2827 : mixedVector B (Sum.inr 2827) = Sparse.eval nodeValue2827 (mixedVector B) := by
    change mixedMoment B node2827 node2827Labels = _
    exact sound2827 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2326, h2802, h2822, h2827, h2931, h3694, h4091, reducedSource1798] using sourceEq2155 B hB

theorem rowSound1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1798 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1798, numericCheck1798, reducedZero1798 B hB hF, mul_zero]

theorem reducedZero1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1799 (mixedVector B) = 0 := by
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1328, h2822, h2893, h2924, h2925, h2931, h4091, reducedSource1799] using sourceEq2156 B hB

theorem rowSound1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1799 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1799, numericCheck1799, reducedZero1799 B hB hF, mul_zero]

theorem reducedZero1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1800 (mixedVector B) = 0 := by
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h2827 : mixedVector B (Sum.inr 2827) = Sparse.eval nodeValue2827 (mixedVector B) := by
    change mixedMoment B node2827 node2827Labels = _
    exact sound2827 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2157, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1338, h2827, h2900, h2931, h2954, h2955, h4091, reducedSource1800] using sourceEq2157 B hB

theorem rowSound1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1800 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1800, numericCheck1800, reducedZero1800 B hB hF, mul_zero]

theorem reducedZero1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1801 (mixedVector B) = 0 := by
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h3433 : mixedVector B (Sum.inr 3433) = Sparse.eval nodeValue3433 (mixedVector B) := by
    change mixedMoment B node3433 node3433Labels = _
    exact sound3433 B hB hF
  have h3439 : mixedVector B (Sum.inr 3439) = Sparse.eval nodeValue3439 (mixedVector B) := by
    change mixedMoment B node3439 node3439Labels = _
    exact sound3439 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2160, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2399, h3433, h3439, h3485, h3522, h3612, h4082, reducedSource1801] using sourceEq2160 B hB

theorem rowSound1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1801 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1801, numericCheck1801, reducedZero1801 B hB hF, mul_zero]

theorem reducedZero1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1802 (mixedVector B) = 0 := by
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3349 : mixedVector B (Sum.inr 3349) = Sparse.eval nodeValue3349 (mixedVector B) := by
    change mixedMoment B node3349 node3349Labels = _
    exact sound3349 B hB hF
  have h3357 : mixedVector B (Sum.inr 3357) = Sparse.eval nodeValue3357 (mixedVector B) := by
    change mixedMoment B node3357 node3357Labels = _
    exact sound3357 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2161, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2910, h3346, h3349, h3357, h3479, h3570, h4080, reducedSource1802] using sourceEq2161 B hB

theorem rowSound1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1802 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1802, numericCheck1802, reducedZero1802 B hB hF, mul_zero]

theorem reducedZero1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1803 (mixedVector B) = 0 := by
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2438 : mixedVector B (Sum.inr 2438) = Sparse.eval nodeValue2438 (mixedVector B) := by
    change mixedMoment B node2438 node2438Labels = _
    exact sound2438 B hB hF
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2355, h2438, h2443, h2488, h2620, h3732, h4092, reducedSource1803] using sourceEq2168 B hB

theorem rowSound1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1803 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1803, numericCheck1803, reducedZero1803 B hB hF, mul_zero]

theorem reducedZero1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1804 (mixedVector B) = 0 := by
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2352, h2798, h2803, h2817, h2867, h3693, h4092, reducedSource1804] using sourceEq2169 B hB

theorem rowSound1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1804 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1804, numericCheck1804, reducedZero1804 B hB hF, mul_zero]

theorem reducedZero1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1805 (mixedVector B) = 0 := by
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2848 : mixedVector B (Sum.inr 2848) = Sparse.eval nodeValue2848 (mixedVector B) := by
    change mixedMoment B node2848 node2848Labels = _
    exact sound2848 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1321, h2817, h2848, h2867, h2881, h2885, h4092, reducedSource1805] using sourceEq2170 B hB

theorem rowSound1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1805 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1805, numericCheck1805, reducedZero1805 B hB hF, mul_zero]

theorem reducedZero1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1806 (mixedVector B) = 0 := by
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3354 : mixedVector B (Sum.inr 3354) = Sparse.eval nodeValue3354 (mixedVector B) := by
    change mixedMoment B node3354 node3354Labels = _
    exact sound3354 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2171, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2538, h3345, h3348, h3354, h3478, h3538, h4082, reducedSource1806] using sourceEq2171 B hB

theorem rowSound1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1806 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1806, numericCheck1806, reducedZero1806 B hB hF, mul_zero]

theorem reducedZero1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1807 (mixedVector B) = 0 := by
  have h2048 : mixedVector B (Sum.inr 2048) = Sparse.eval nodeValue2048 (mixedVector B) := by
    change mixedMoment B node2048 node2048Labels = _
    exact sound2048 B hB hF
  have h3386 : mixedVector B (Sum.inr 3386) = Sparse.eval nodeValue3386 (mixedVector B) := by
    change mixedMoment B node3386 node3386Labels = _
    exact sound3386 B hB hF
  have h3491 : mixedVector B (Sum.inr 3491) = Sparse.eval nodeValue3491 (mixedVector B) := by
    change mixedMoment B node3491 node3491Labels = _
    exact sound3491 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2172, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2048, h3386, h3491, h3522, h3538, h3542, h4082, reducedSource1807] using sourceEq2172 B hB

theorem rowSound1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1807 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1807, numericCheck1807, reducedZero1807 B hB hF, mul_zero]

theorem sourceRowsAt1792 : MixedData.sourceRows (1792 : Fin 2425) =
    MixedData.row1792 := by decide +kernel

theorem sourceRowsAt1793 : MixedData.sourceRows (1793 : Fin 2425) =
    MixedData.row1793 := by decide +kernel

theorem sourceRowsAt1794 : MixedData.sourceRows (1794 : Fin 2425) =
    MixedData.row1794 := by decide +kernel

theorem sourceRowsAt1795 : MixedData.sourceRows (1795 : Fin 2425) =
    MixedData.row1795 := by decide +kernel

theorem sourceRowsAt1796 : MixedData.sourceRows (1796 : Fin 2425) =
    MixedData.row1796 := by decide +kernel

theorem sourceRowsAt1797 : MixedData.sourceRows (1797 : Fin 2425) =
    MixedData.row1797 := by decide +kernel

theorem sourceRowsAt1798 : MixedData.sourceRows (1798 : Fin 2425) =
    MixedData.row1798 := by decide +kernel

theorem sourceRowsAt1799 : MixedData.sourceRows (1799 : Fin 2425) =
    MixedData.row1799 := by decide +kernel

theorem sourceRowsAt1800 : MixedData.sourceRows (1800 : Fin 2425) =
    MixedData.row1800 := by decide +kernel

theorem sourceRowsAt1801 : MixedData.sourceRows (1801 : Fin 2425) =
    MixedData.row1801 := by decide +kernel

theorem sourceRowsAt1802 : MixedData.sourceRows (1802 : Fin 2425) =
    MixedData.row1802 := by decide +kernel

theorem sourceRowsAt1803 : MixedData.sourceRows (1803 : Fin 2425) =
    MixedData.row1803 := by decide +kernel

theorem sourceRowsAt1804 : MixedData.sourceRows (1804 : Fin 2425) =
    MixedData.row1804 := by decide +kernel

theorem sourceRowsAt1805 : MixedData.sourceRows (1805 : Fin 2425) =
    MixedData.row1805 := by decide +kernel

theorem sourceRowsAt1806 : MixedData.sourceRows (1806 : Fin 2425) =
    MixedData.row1806 := by decide +kernel

theorem sourceRowsAt1807 : MixedData.sourceRows (1807 : Fin 2425) =
    MixedData.row1807 := by decide +kernel

theorem chunkSound112_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 112) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1792 ∨ k.val = 1793 ∨ k.val = 1794 ∨ k.val = 1795 ∨ k.val = 1796 ∨ k.val = 1797 ∨ k.val = 1798 ∨ k.val = 1799 ∨ k.val = 1800 ∨ k.val = 1801 ∨ k.val = 1802 ∨ k.val = 1803 ∨ k.val = 1804 ∨ k.val = 1805 ∨ k.val = 1806 ∨ k.val = 1807 := by omega
  rcases heq with h1792 | h1793 | h1794 | h1795 | h1796 | h1797 | h1798 | h1799 | h1800 | h1801 | h1802 | h1803 | h1804 | h1805 | h1806 | h1807
  · have he : k = (1792 : Fin 2425) := Fin.ext h1792
    subst k
    rw [sourceRowsAt1792]
    exact rowSound1792 B hB hF
  · have he : k = (1793 : Fin 2425) := Fin.ext h1793
    subst k
    rw [sourceRowsAt1793]
    exact rowSound1793 B hB hF
  · have he : k = (1794 : Fin 2425) := Fin.ext h1794
    subst k
    rw [sourceRowsAt1794]
    exact rowSound1794 B hB hF
  · have he : k = (1795 : Fin 2425) := Fin.ext h1795
    subst k
    rw [sourceRowsAt1795]
    exact rowSound1795_e B hB hF
  · have he : k = (1796 : Fin 2425) := Fin.ext h1796
    subst k
    rw [sourceRowsAt1796]
    exact rowSound1796_e B hB hF
  · have he : k = (1797 : Fin 2425) := Fin.ext h1797
    subst k
    rw [sourceRowsAt1797]
    exact rowSound1797 B hB hF
  · have he : k = (1798 : Fin 2425) := Fin.ext h1798
    subst k
    rw [sourceRowsAt1798]
    exact rowSound1798 B hB hF
  · have he : k = (1799 : Fin 2425) := Fin.ext h1799
    subst k
    rw [sourceRowsAt1799]
    exact rowSound1799 B hB hF
  · have he : k = (1800 : Fin 2425) := Fin.ext h1800
    subst k
    rw [sourceRowsAt1800]
    exact rowSound1800 B hB hF
  · have he : k = (1801 : Fin 2425) := Fin.ext h1801
    subst k
    rw [sourceRowsAt1801]
    exact rowSound1801 B hB hF
  · have he : k = (1802 : Fin 2425) := Fin.ext h1802
    subst k
    rw [sourceRowsAt1802]
    exact rowSound1802 B hB hF
  · have he : k = (1803 : Fin 2425) := Fin.ext h1803
    subst k
    rw [sourceRowsAt1803]
    exact rowSound1803 B hB hF
  · have he : k = (1804 : Fin 2425) := Fin.ext h1804
    subst k
    rw [sourceRowsAt1804]
    exact rowSound1804 B hB hF
  · have he : k = (1805 : Fin 2425) := Fin.ext h1805
    subst k
    rw [sourceRowsAt1805]
    exact rowSound1805 B hB hF
  · have he : k = (1806 : Fin 2425) := Fin.ext h1806
    subst k
    rw [sourceRowsAt1806]
    exact rowSound1806 B hB hF
  · have he : k = (1807 : Fin 2425) := Fin.ext h1807
    subst k
    rw [sourceRowsAt1807]
    exact rowSound1807 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e_oai
