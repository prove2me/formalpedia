-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:40.724475+00:00
-- url     : https://prove2.me/submissions/12029260-5333-4e90-b476-e21380b9b3a8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1335_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1340_e

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14373 raw14373Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14373 raw14373Labels = mixedMoment B raw14373step0 raw14373step0Labels := by
      have hz : ∀ j, raw14373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14373step0 = (fun i j => raw14373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14373step0 raw14373; decide +kernel
      have hl : raw14373step0Labels = raw14373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373 raw14373Labels permutation346 hz
    mixedMoment B raw14373step0 raw14373step0Labels = mixedMoment B raw14373step1 raw14373step1Labels := by
      have hz : ∀ j, raw14373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14373step1 = (fun i j => raw14373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14373step1 raw14373step0; decide +kernel
      have hl : raw14373step1Labels = raw14373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373step0 raw14373step0Labels permutation56 hz
    mixedMoment B raw14373step1 raw14373step1Labels = mixedMoment B raw14373step2 raw14373step2Labels := by
      have hz : ∀ i, raw14373step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14373step2 = (fun i j => raw14373step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14373step2 raw14373step1; decide +kernel
      have hl : raw14373step2Labels = (fun j => raw14373step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14373step1 raw14373step1Labels permutation6 hz
    mixedMoment B raw14373step2 raw14373step2Labels = mixedMoment B raw14373step3 raw14373step3Labels := by
      have ha : raw14373step3 = (fun i j => raw14373step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14373step3 raw14373step2; decide +kernel
      have hl : raw14373step3Labels = raw14373step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14373step2 raw14373step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22017 raw22017Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw22017 raw22017Labels = mixedMoment B raw22017step0 raw22017step0Labels := by
      have hz : ∀ j, raw22017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22017step0 = (fun i j => raw22017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22017step0 raw22017; decide +kernel
      have hl : raw22017step0Labels = raw22017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017 raw22017Labels permutation434 hz
    mixedMoment B raw22017step0 raw22017step0Labels = mixedMoment B raw22017step1 raw22017step1Labels := by
      have hz : ∀ j, raw22017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22017step1 = (fun i j => raw22017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22017step1 raw22017step0; decide +kernel
      have hl : raw22017step1Labels = raw22017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017step0 raw22017step0Labels permutation80 hz
    _ = mixedMoment B node858 node858Labels := by rfl

theorem canonical22020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22020 raw22020Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22020 raw22020Labels = mixedMoment B raw22020step0 raw22020step0Labels := by
      have hz : ∀ j, raw22020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22020step0 = (fun i j => raw22020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22020step0 raw22020; decide +kernel
      have hl : raw22020step0Labels = raw22020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020 raw22020Labels permutation434 hz
    mixedMoment B raw22020step0 raw22020step0Labels = mixedMoment B raw22020step1 raw22020step1Labels := by
      have hz : ∀ j, raw22020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22020step1 = (fun i j => raw22020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22020step1 raw22020step0; decide +kernel
      have hl : raw22020step1Labels = raw22020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020step0 raw22020step0Labels permutation80 hz
    mixedMoment B raw22020step1 raw22020step1Labels = mixedMoment B raw22020step2 raw22020step2Labels := by
      have ha : raw22020step2 = (fun i j => raw22020step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22020step2 raw22020step1; decide +kernel
      have hl : raw22020step2Labels = raw22020step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22020step1 raw22020step1Labels permutation9 permutation2
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical22022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22022 raw22022Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22022 raw22022Labels = mixedMoment B raw22022step0 raw22022step0Labels := by
      have hz : ∀ j, raw22022 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22022step0 = (fun i j => raw22022 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22022step0 raw22022; decide +kernel
      have hl : raw22022step0Labels = raw22022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022 raw22022Labels permutation590 hz
    mixedMoment B raw22022step0 raw22022step0Labels = mixedMoment B raw22022step1 raw22022step1Labels := by
      have hz : ∀ j, raw22022step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22022step1 = (fun i j => raw22022step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22022step1 raw22022step0; decide +kernel
      have hl : raw22022step1Labels = raw22022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step0 raw22022step0Labels permutation104 hz
    mixedMoment B raw22022step1 raw22022step1Labels = mixedMoment B raw22022step2 raw22022step2Labels := by
      have hz : ∀ j, raw22022step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22022step2 = (fun i j => raw22022step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22022step2 raw22022step1; decide +kernel
      have hl : raw22022step2Labels = raw22022step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step1 raw22022step1Labels permutation20 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical22028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22028 raw22028Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw22028 raw22028Labels = mixedMoment B raw22028step0 raw22028step0Labels := by
      have hz : ∀ j, raw22028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22028step0 = (fun i j => raw22028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22028step0 raw22028; decide +kernel
      have hl : raw22028step0Labels = raw22028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028 raw22028Labels permutation434 hz
    mixedMoment B raw22028step0 raw22028step0Labels = mixedMoment B raw22028step1 raw22028step1Labels := by
      have hz : ∀ j, raw22028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22028step1 = (fun i j => raw22028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22028step1 raw22028step0; decide +kernel
      have hl : raw22028step1Labels = raw22028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028step0 raw22028step0Labels permutation80 hz
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical22029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22029 raw22029Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22029 raw22029Labels = mixedMoment B raw22029step0 raw22029step0Labels := by
      have hz : ∀ j, raw22029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22029step0 = (fun i j => raw22029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22029step0 raw22029; decide +kernel
      have hl : raw22029step0Labels = raw22029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029 raw22029Labels permutation434 hz
    mixedMoment B raw22029step0 raw22029step0Labels = mixedMoment B raw22029step1 raw22029step1Labels := by
      have hz : ∀ j, raw22029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22029step1 = (fun i j => raw22029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22029step1 raw22029step0; decide +kernel
      have hl : raw22029step1Labels = raw22029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029step0 raw22029step0Labels permutation80 hz
    mixedMoment B raw22029step1 raw22029step1Labels = mixedMoment B raw22029step2 raw22029step2Labels := by
      have ha : raw22029step2 = (fun i j => raw22029step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22029step2 raw22029step1; decide +kernel
      have hl : raw22029step2Labels = raw22029step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22029step1 raw22029step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22037 raw22037Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw22037 raw22037Labels = mixedMoment B raw22037step0 raw22037step0Labels := by
      have hz : ∀ j, raw22037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22037step0 = (fun i j => raw22037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22037step0 raw22037; decide +kernel
      have hl : raw22037step0Labels = raw22037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037 raw22037Labels permutation434 hz
    mixedMoment B raw22037step0 raw22037step0Labels = mixedMoment B raw22037step1 raw22037step1Labels := by
      have hz : ∀ j, raw22037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22037step1 = (fun i j => raw22037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22037step1 raw22037step0; decide +kernel
      have hl : raw22037step1Labels = raw22037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037step0 raw22037step0Labels permutation80 hz
    _ = mixedMoment B node831 node831Labels := by rfl

theorem canonical22072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22072 raw22072Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw22072 raw22072Labels = mixedMoment B raw22072step0 raw22072step0Labels := by
      have hz : ∀ j, raw22072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22072step0 = (fun i j => raw22072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22072step0 raw22072; decide +kernel
      have hl : raw22072step0Labels = raw22072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22072 raw22072Labels permutation434 hz
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical22073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22073 raw22073Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw22073 raw22073Labels = mixedMoment B raw22073step0 raw22073step0Labels := by
      have hz : ∀ j, raw22073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22073step0 = (fun i j => raw22073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22073step0 raw22073; decide +kernel
      have hl : raw22073step0Labels = raw22073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22073 raw22073Labels permutation434 hz
    mixedMoment B raw22073step0 raw22073step0Labels = mixedMoment B raw22073step1 raw22073step1Labels := by
      have ha : raw22073step1 = (fun i j => raw22073step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22073step1 raw22073step0; decide +kernel
      have hl : raw22073step1Labels = raw22073step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22073step0 raw22073step0Labels permutation38 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical22076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22076 raw22076Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw22076 raw22076Labels = mixedMoment B raw22076step0 raw22076step0Labels := by
      have hz : ∀ j, raw22076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22076step0 = (fun i j => raw22076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22076step0 raw22076; decide +kernel
      have hl : raw22076step0Labels = raw22076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22076 raw22076Labels permutation434 hz
    mixedMoment B raw22076step0 raw22076step0Labels = mixedMoment B raw22076step1 raw22076step1Labels := by
      have ha : raw22076step1 = (fun i j => raw22076step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22076step1 raw22076step0; decide +kernel
      have hl : raw22076step1Labels = raw22076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22076step0 raw22076step0Labels permutation33 permutation2
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical22078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22078 raw22078Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22078 raw22078Labels = mixedMoment B raw22078step0 raw22078step0Labels := by
      have hz : ∀ j, raw22078 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22078step0 = (fun i j => raw22078 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22078step0 raw22078; decide +kernel
      have hl : raw22078step0Labels = raw22078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22078 raw22078Labels permutation590 hz
    mixedMoment B raw22078step0 raw22078step0Labels = mixedMoment B raw22078step1 raw22078step1Labels := by
      have hz : ∀ j, raw22078step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22078step1 = (fun i j => raw22078step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22078step1 raw22078step0; decide +kernel
      have hl : raw22078step1Labels = raw22078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22078step0 raw22078step0Labels permutation104 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22084 raw22084Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw22084 raw22084Labels = mixedMoment B raw22084step0 raw22084step0Labels := by
      have hz : ∀ j, raw22084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22084step0 = (fun i j => raw22084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22084step0 raw22084; decide +kernel
      have hl : raw22084step0Labels = raw22084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22084 raw22084Labels permutation434 hz
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical22085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22085 raw22085Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22085 raw22085Labels = mixedMoment B raw22085step0 raw22085step0Labels := by
      have hz : ∀ j, raw22085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22085step0 = (fun i j => raw22085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22085step0 raw22085; decide +kernel
      have hl : raw22085step0Labels = raw22085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22085 raw22085Labels permutation434 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical22090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22090 raw22090Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw22090 raw22090Labels = mixedMoment B raw22090step0 raw22090step0Labels := by
      have hz : ∀ j, raw22090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22090step0 = (fun i j => raw22090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22090step0 raw22090; decide +kernel
      have hl : raw22090step0Labels = raw22090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22090 raw22090Labels permutation434 hz
    mixedMoment B raw22090step0 raw22090step0Labels = mixedMoment B raw22090step1 raw22090step1Labels := by
      have ha : raw22090step1 = (fun i j => raw22090step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22090step1 raw22090step0; decide +kernel
      have hl : raw22090step1Labels = raw22090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22090step0 raw22090step0Labels permutation38 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical22093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22093 raw22093Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw22093 raw22093Labels = mixedMoment B raw22093step0 raw22093step0Labels := by
      have hz : ∀ j, raw22093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22093step0 = (fun i j => raw22093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22093step0 raw22093; decide +kernel
      have hl : raw22093step0Labels = raw22093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22093 raw22093Labels permutation434 hz
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical22119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22119 raw22119Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw22119 raw22119Labels = mixedMoment B raw22119step0 raw22119step0Labels := by
      have hz : ∀ j, raw22119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22119step0 = (fun i j => raw22119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22119step0 raw22119; decide +kernel
      have hl : raw22119step0Labels = raw22119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119 raw22119Labels permutation434 hz
    mixedMoment B raw22119step0 raw22119step0Labels = mixedMoment B raw22119step1 raw22119step1Labels := by
      have hz : ∀ j, raw22119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22119step1 = (fun i j => raw22119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22119step1 raw22119step0; decide +kernel
      have hl : raw22119step1Labels = raw22119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119step0 raw22119step0Labels permutation80 hz
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical22120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22120 raw22120Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22120 raw22120Labels = mixedMoment B raw22120step0 raw22120step0Labels := by
      have hz : ∀ j, raw22120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22120step0 = (fun i j => raw22120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22120step0 raw22120; decide +kernel
      have hl : raw22120step0Labels = raw22120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120 raw22120Labels permutation434 hz
    mixedMoment B raw22120step0 raw22120step0Labels = mixedMoment B raw22120step1 raw22120step1Labels := by
      have hz : ∀ j, raw22120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22120step1 = (fun i j => raw22120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22120step1 raw22120step0; decide +kernel
      have hl : raw22120step1Labels = raw22120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120step0 raw22120step0Labels permutation80 hz
    mixedMoment B raw22120step1 raw22120step1Labels = mixedMoment B raw22120step2 raw22120step2Labels := by
      have ha : raw22120step2 = (fun i j => raw22120step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22120step2 raw22120step1; decide +kernel
      have hl : raw22120step2Labels = raw22120step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22120step1 raw22120step1Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22121 raw22121Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw22121 raw22121Labels = mixedMoment B raw22121step0 raw22121step0Labels := by
      have hz : ∀ j, raw22121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22121step0 = (fun i j => raw22121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22121step0 raw22121; decide +kernel
      have hl : raw22121step0Labels = raw22121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121 raw22121Labels permutation434 hz
    mixedMoment B raw22121step0 raw22121step0Labels = mixedMoment B raw22121step1 raw22121step1Labels := by
      have hz : ∀ j, raw22121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22121step1 = (fun i j => raw22121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22121step1 raw22121step0; decide +kernel
      have hl : raw22121step1Labels = raw22121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121step0 raw22121step0Labels permutation80 hz
    _ = mixedMoment B node548 node548Labels := by rfl

theorem canonical22122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22122 raw22122Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw22122 raw22122Labels = mixedMoment B raw22122step0 raw22122step0Labels := by
      have hz : ∀ j, raw22122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22122step0 = (fun i j => raw22122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22122step0 raw22122; decide +kernel
      have hl : raw22122step0Labels = raw22122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122 raw22122Labels permutation434 hz
    mixedMoment B raw22122step0 raw22122step0Labels = mixedMoment B raw22122step1 raw22122step1Labels := by
      have hz : ∀ j, raw22122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22122step1 = (fun i j => raw22122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22122step1 raw22122step0; decide +kernel
      have hl : raw22122step1Labels = raw22122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122step0 raw22122step0Labels permutation80 hz
    _ = mixedMoment B node743 node743Labels := by rfl

theorem canonical22125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22125 raw22125Labels = mixedMoment B node816 node816Labels := by
  calc
    mixedMoment B raw22125 raw22125Labels = mixedMoment B raw22125step0 raw22125step0Labels := by
      have hz : ∀ j, raw22125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22125step0 = (fun i j => raw22125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22125step0 raw22125; decide +kernel
      have hl : raw22125step0Labels = raw22125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125 raw22125Labels permutation434 hz
    mixedMoment B raw22125step0 raw22125step0Labels = mixedMoment B raw22125step1 raw22125step1Labels := by
      have hz : ∀ j, raw22125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22125step1 = (fun i j => raw22125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22125step1 raw22125step0; decide +kernel
      have hl : raw22125step1Labels = raw22125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125step0 raw22125step0Labels permutation80 hz
    mixedMoment B raw22125step1 raw22125step1Labels = mixedMoment B raw22125step2 raw22125step2Labels := by
      have ha : raw22125step2 = (fun i j => raw22125step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22125step2 raw22125step1; decide +kernel
      have hl : raw22125step2Labels = raw22125step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22125step1 raw22125step1Labels permutation9 permutation2
    _ = mixedMoment B node816 node816Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22310 raw22310Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw22310 raw22310Labels = mixedMoment B raw22310step0 raw22310step0Labels := by
      have hz : ∀ j, raw22310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22310step0 = (fun i j => raw22310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22310step0 raw22310; decide +kernel
      have hl : raw22310step0Labels = raw22310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310 raw22310Labels permutation434 hz
    mixedMoment B raw22310step0 raw22310step0Labels = mixedMoment B raw22310step1 raw22310step1Labels := by
      have hz : ∀ j, raw22310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22310step1 = (fun i j => raw22310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22310step1 raw22310step0; decide +kernel
      have hl : raw22310step1Labels = raw22310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step0 raw22310step0Labels permutation80 hz
    mixedMoment B raw22310step1 raw22310step1Labels = mixedMoment B raw22310step2 raw22310step2Labels := by
      have hz : ∀ j, raw22310step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22310step2 = (fun i j => raw22310step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22310step2 raw22310step1; decide +kernel
      have hl : raw22310step2Labels = raw22310step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step1 raw22310step1Labels permutation14 hz
    mixedMoment B raw22310step2 raw22310step2Labels = mixedMoment B raw22310step3 raw22310step3Labels := by
      have hz : ∀ i, raw22310step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22310step3 = (fun i j => raw22310step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22310step3 raw22310step2; decide +kernel
      have hl : raw22310step3Labels = (fun j => raw22310step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22310step2 raw22310step2Labels permutation6 hz
    _ = mixedMoment B node4061 node4061Labels := by rfl

theorem canonical22311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22311 raw22311Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22311 raw22311Labels = mixedMoment B raw22311step0 raw22311step0Labels := by
      have hz : ∀ j, raw22311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22311step0 = (fun i j => raw22311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22311step0 raw22311; decide +kernel
      have hl : raw22311step0Labels = raw22311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311 raw22311Labels permutation434 hz
    mixedMoment B raw22311step0 raw22311step0Labels = mixedMoment B raw22311step1 raw22311step1Labels := by
      have hz : ∀ j, raw22311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22311step1 = (fun i j => raw22311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22311step1 raw22311step0; decide +kernel
      have hl : raw22311step1Labels = raw22311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311step0 raw22311step0Labels permutation80 hz
    mixedMoment B raw22311step1 raw22311step1Labels = mixedMoment B raw22311step2 raw22311step2Labels := by
      have hz : ∀ i, raw22311step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22311step2 = (fun i j => raw22311step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22311step2 raw22311step1; decide +kernel
      have hl : raw22311step2Labels = (fun j => raw22311step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22311step1 raw22311step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical22312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22312 raw22312Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22312 raw22312Labels = mixedMoment B raw22312step0 raw22312step0Labels := by
      have hz : ∀ j, raw22312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22312step0 = (fun i j => raw22312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22312step0 raw22312; decide +kernel
      have hl : raw22312step0Labels = raw22312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312 raw22312Labels permutation434 hz
    mixedMoment B raw22312step0 raw22312step0Labels = mixedMoment B raw22312step1 raw22312step1Labels := by
      have hz : ∀ j, raw22312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22312step1 = (fun i j => raw22312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22312step1 raw22312step0; decide +kernel
      have hl : raw22312step1Labels = raw22312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312step0 raw22312step0Labels permutation56 hz
    mixedMoment B raw22312step1 raw22312step1Labels = mixedMoment B raw22312step2 raw22312step2Labels := by
      have hz : ∀ i, raw22312step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22312step2 = (fun i j => raw22312step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22312step2 raw22312step1; decide +kernel
      have hl : raw22312step2Labels = (fun j => raw22312step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22312step1 raw22312step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical22313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22313 raw22313Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22313 raw22313Labels = mixedMoment B raw22313step0 raw22313step0Labels := by
      have hz : ∀ j, raw22313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22313step0 = (fun i j => raw22313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22313step0 raw22313; decide +kernel
      have hl : raw22313step0Labels = raw22313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313 raw22313Labels permutation346 hz
    mixedMoment B raw22313step0 raw22313step0Labels = mixedMoment B raw22313step1 raw22313step1Labels := by
      have hz : ∀ j, raw22313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22313step1 = (fun i j => raw22313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22313step1 raw22313step0; decide +kernel
      have hl : raw22313step1Labels = raw22313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313step0 raw22313step0Labels permutation56 hz
    mixedMoment B raw22313step1 raw22313step1Labels = mixedMoment B raw22313step2 raw22313step2Labels := by
      have hz : ∀ i, raw22313step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22313step2 = (fun i j => raw22313step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22313step2 raw22313step1; decide +kernel
      have hl : raw22313step2Labels = (fun j => raw22313step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22313step1 raw22313step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23328 raw23328Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw23328 raw23328Labels = mixedMoment B raw23328step0 raw23328step0Labels := by
      have ha : raw23328step0 = (fun i j => raw23328 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23328step0 raw23328; decide +kernel
      have hl : raw23328step0Labels = raw23328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23328 raw23328Labels permutation201 permutation4
    mixedMoment B raw23328step0 raw23328step0Labels = mixedMoment B raw23328step1 raw23328step1Labels := by
      have ha : raw23328step1 = -raw23328step0 := by apply Matrix.ext; change ∀ i j, raw23328step1 i j = -(raw23328step0 i j); unfold raw23328step1 raw23328step0; decide +kernel
      have hl : raw23328step1Labels = raw23328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node710 node710Labels := by rfl

theorem canonical23329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23329 raw23329Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23329 raw23329Labels = mixedMoment B raw23329step0 raw23329step0Labels := by
      have hz : ∀ j, raw23329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23329step0 = (fun i j => raw23329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23329step0 raw23329; decide +kernel
      have hl : raw23329step0Labels = raw23329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329 raw23329Labels permutation434 hz
    mixedMoment B raw23329step0 raw23329step0Labels = mixedMoment B raw23329step1 raw23329step1Labels := by
      have hz : ∀ j, raw23329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23329step1 = (fun i j => raw23329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23329step1 raw23329step0; decide +kernel
      have hl : raw23329step1Labels = raw23329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329step0 raw23329step0Labels permutation80 hz
    mixedMoment B raw23329step1 raw23329step1Labels = mixedMoment B raw23329step2 raw23329step2Labels := by
      have ha : raw23329step2 = (fun i j => raw23329step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23329step2 raw23329step1; decide +kernel
      have hl : raw23329step2Labels = raw23329step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23329step1 raw23329step1Labels permutation9 permutation4
    mixedMoment B raw23329step2 raw23329step2Labels = mixedMoment B raw23329step3 raw23329step3Labels := by
      have ha : raw23329step3 = -raw23329step2 := by apply Matrix.ext; change ∀ i j, raw23329step3 i j = -(raw23329step2 i j); unfold raw23329step3 raw23329step2; decide +kernel
      have hl : raw23329step3Labels = raw23329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node852 node852Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23662 raw23662Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw23662 raw23662Labels = mixedMoment B raw23662step0 raw23662step0Labels := by
      have hz : ∀ j, raw23662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23662step0 = (fun i j => raw23662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23662step0 raw23662; decide +kernel
      have hl : raw23662step0Labels = raw23662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23662 raw23662Labels permutation434 hz
    mixedMoment B raw23662step0 raw23662step0Labels = mixedMoment B raw23662step1 raw23662step1Labels := by
      have hz : ∀ j, raw23662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23662step1 = (fun i j => raw23662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23662step1 raw23662step0; decide +kernel
      have hl : raw23662step1Labels = raw23662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23662step0 raw23662step0Labels permutation80 hz
    mixedMoment B raw23662step1 raw23662step1Labels = mixedMoment B raw23662step2 raw23662step2Labels := by
      have ha : raw23662step2 = (fun i j => raw23662step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23662step2 raw23662step1; decide +kernel
      have hl : raw23662step2Labels = raw23662step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23662step1 raw23662step1Labels permutation9 permutation2
    _ = mixedMoment B node562 node562Labels := by rfl

theorem canonical23663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23663 raw23663Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23663 raw23663Labels = mixedMoment B raw23663step0 raw23663step0Labels := by
      have hz : ∀ j, raw23663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23663step0 = (fun i j => raw23663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23663step0 raw23663; decide +kernel
      have hl : raw23663step0Labels = raw23663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23663 raw23663Labels permutation434 hz
    mixedMoment B raw23663step0 raw23663step0Labels = mixedMoment B raw23663step1 raw23663step1Labels := by
      have ha : raw23663step1 = (fun i j => raw23663step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23663step1 raw23663step0; decide +kernel
      have hl : raw23663step1Labels = raw23663step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23663step0 raw23663step0Labels permutation39 permutation2
    _ = mixedMoment B node724 node724Labels := by rfl

theorem canonical23664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23664 raw23664Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23664 raw23664Labels = mixedMoment B raw23664step0 raw23664step0Labels := by
      have hz : ∀ j, raw23664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23664step0 = (fun i j => raw23664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23664step0 raw23664; decide +kernel
      have hl : raw23664step0Labels = raw23664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23664 raw23664Labels permutation346 hz
    mixedMoment B raw23664step0 raw23664step0Labels = mixedMoment B raw23664step1 raw23664step1Labels := by
      have ha : raw23664step1 = (fun i j => raw23664step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23664step1 raw23664step0; decide +kernel
      have hl : raw23664step1Labels = raw23664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23664step0 raw23664step0Labels permutation39 permutation2
    _ = mixedMoment B node724 node724Labels := by rfl

theorem canonical23665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23665 raw23665Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23665 raw23665Labels = mixedMoment B raw23665step0 raw23665step0Labels := by
      have hz : ∀ j, raw23665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23665step0 = (fun i j => raw23665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23665step0 raw23665; decide +kernel
      have hl : raw23665step0Labels = raw23665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23665 raw23665Labels permutation434 hz
    mixedMoment B raw23665step0 raw23665step0Labels = mixedMoment B raw23665step1 raw23665step1Labels := by
      have hz : ∀ j, raw23665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23665step1 = (fun i j => raw23665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23665step1 raw23665step0; decide +kernel
      have hl : raw23665step1Labels = raw23665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23665step0 raw23665step0Labels permutation80 hz
    mixedMoment B raw23665step1 raw23665step1Labels = mixedMoment B raw23665step2 raw23665step2Labels := by
      have ha : raw23665step2 = (fun i j => raw23665step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23665step2 raw23665step1; decide +kernel
      have hl : raw23665step2Labels = raw23665step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23665step1 raw23665step1Labels permutation12 permutation2
    _ = mixedMoment B node852 node852Labels := by rfl

theorem canonical23666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23666 raw23666Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw23666 raw23666Labels = mixedMoment B raw23666step0 raw23666step0Labels := by
      have hz : ∀ j, raw23666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23666step0 = (fun i j => raw23666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23666step0 raw23666; decide +kernel
      have hl : raw23666step0Labels = raw23666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23666 raw23666Labels permutation434 hz
    mixedMoment B raw23666step0 raw23666step0Labels = mixedMoment B raw23666step1 raw23666step1Labels := by
      have hz : ∀ j, raw23666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23666step1 = (fun i j => raw23666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23666step1 raw23666step0; decide +kernel
      have hl : raw23666step1Labels = raw23666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23666step0 raw23666step0Labels permutation80 hz
    _ = mixedMoment B node1661 node1661Labels := by rfl

theorem canonical23667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23667 raw23667Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw23667 raw23667Labels = mixedMoment B raw23667step0 raw23667step0Labels := by
      have hz : ∀ j, raw23667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23667step0 = (fun i j => raw23667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23667step0 raw23667; decide +kernel
      have hl : raw23667step0Labels = raw23667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23667 raw23667Labels permutation434 hz
    mixedMoment B raw23667step0 raw23667step0Labels = mixedMoment B raw23667step1 raw23667step1Labels := by
      have ha : raw23667step1 = (fun i j => raw23667step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23667step1 raw23667step0; decide +kernel
      have hl : raw23667step1Labels = raw23667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23667step0 raw23667step0Labels permutation38 permutation2
    _ = mixedMoment B node1612 node1612Labels := by rfl

theorem canonical23668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23668 raw23668Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw23668 raw23668Labels = mixedMoment B raw23668step0 raw23668step0Labels := by
      have hz : ∀ j, raw23668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23668step0 = (fun i j => raw23668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23668step0 raw23668; decide +kernel
      have hl : raw23668step0Labels = raw23668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23668 raw23668Labels permutation346 hz
    mixedMoment B raw23668step0 raw23668step0Labels = mixedMoment B raw23668step1 raw23668step1Labels := by
      have ha : raw23668step1 = (fun i j => raw23668step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23668step1 raw23668step0; decide +kernel
      have hl : raw23668step1Labels = raw23668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23668step0 raw23668step0Labels permutation38 permutation2
    _ = mixedMoment B node1612 node1612Labels := by rfl

theorem canonical23669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23669 raw23669Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw23669 raw23669Labels = mixedMoment B raw23669step0 raw23669step0Labels := by
      have hz : ∀ j, raw23669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23669step0 = (fun i j => raw23669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23669step0 raw23669; decide +kernel
      have hl : raw23669step0Labels = raw23669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23669 raw23669Labels permutation434 hz
    mixedMoment B raw23669step0 raw23669step0Labels = mixedMoment B raw23669step1 raw23669step1Labels := by
      have hz : ∀ j, raw23669step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23669step1 = (fun i j => raw23669step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23669step1 raw23669step0; decide +kernel
      have hl : raw23669step1Labels = raw23669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23669step0 raw23669step0Labels permutation80 hz
    mixedMoment B raw23669step1 raw23669step1Labels = mixedMoment B raw23669step2 raw23669step2Labels := by
      have ha : raw23669step2 = (fun i j => raw23669step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23669step2 raw23669step1; decide +kernel
      have hl : raw23669step2Labels = raw23669step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23669step1 raw23669step1Labels permutation9 permutation2
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical23674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23674 raw23674Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw23674 raw23674Labels = mixedMoment B raw23674step0 raw23674step0Labels := by
      have hz : ∀ j, raw23674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23674step0 = (fun i j => raw23674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23674step0 raw23674; decide +kernel
      have hl : raw23674step0Labels = raw23674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23674 raw23674Labels permutation434 hz
    mixedMoment B raw23674step0 raw23674step0Labels = mixedMoment B raw23674step1 raw23674step1Labels := by
      have ha : raw23674step1 = (fun i j => raw23674step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23674step1 raw23674step0; decide +kernel
      have hl : raw23674step1Labels = raw23674step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23674step0 raw23674step0Labels permutation33 permutation2
    _ = mixedMoment B node1640 node1640Labels := by rfl

theorem canonical23675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23675 raw23675Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw23675 raw23675Labels = mixedMoment B raw23675step0 raw23675step0Labels := by
      have hz : ∀ j, raw23675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23675step0 = (fun i j => raw23675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23675step0 raw23675; decide +kernel
      have hl : raw23675step0Labels = raw23675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23675 raw23675Labels permutation434 hz
    mixedMoment B raw23675step0 raw23675step0Labels = mixedMoment B raw23675step1 raw23675step1Labels := by
      have ha : raw23675step1 = (fun i j => raw23675step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23675step1 raw23675step0; decide +kernel
      have hl : raw23675step1Labels = raw23675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23675step0 raw23675step0Labels permutation39 permutation2
    _ = mixedMoment B node1640 node1640Labels := by rfl

theorem canonical23676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23676 raw23676Labels = mixedMoment B node1594 node1594Labels := by
  calc
    mixedMoment B raw23676 raw23676Labels = mixedMoment B raw23676step0 raw23676step0Labels := by
      have ha : raw23676step0 = (fun i j => raw23676 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23676step0 raw23676; decide +kernel
      have hl : raw23676step0Labels = raw23676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23676 raw23676Labels permutation201 permutation2
    _ = mixedMoment B node1594 node1594Labels := by rfl

theorem canonical23677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23677 raw23677Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23677 raw23677Labels = mixedMoment B raw23677step0 raw23677step0Labels := by
      have hz : ∀ j, raw23677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23677step0 = (fun i j => raw23677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23677step0 raw23677; decide +kernel
      have hl : raw23677step0Labels = raw23677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23677 raw23677Labels permutation434 hz
    mixedMoment B raw23677step0 raw23677step0Labels = mixedMoment B raw23677step1 raw23677step1Labels := by
      have ha : raw23677step1 = (fun i j => raw23677step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23677step1 raw23677step0; decide +kernel
      have hl : raw23677step1Labels = raw23677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23677step0 raw23677step0Labels permutation33 permutation2
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical23678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23678 raw23678Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw23678 raw23678Labels = mixedMoment B raw23678step0 raw23678step0Labels := by
      have hz : ∀ j, raw23678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23678step0 = (fun i j => raw23678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23678step0 raw23678; decide +kernel
      have hl : raw23678step0Labels = raw23678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23678 raw23678Labels permutation434 hz
    mixedMoment B raw23678step0 raw23678step0Labels = mixedMoment B raw23678step1 raw23678step1Labels := by
      have ha : raw23678step1 = (fun i j => raw23678step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23678step1 raw23678step0; decide +kernel
      have hl : raw23678step1Labels = raw23678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23678step0 raw23678step0Labels permutation39 permutation2
    _ = mixedMoment B node543 node543Labels := by rfl

theorem canonical23679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23679 raw23679Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw23679 raw23679Labels = mixedMoment B raw23679step0 raw23679step0Labels := by
      have hz : ∀ j, raw23679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23679step0 = (fun i j => raw23679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23679step0 raw23679; decide +kernel
      have hl : raw23679step0Labels = raw23679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23679 raw23679Labels permutation434 hz
    mixedMoment B raw23679step0 raw23679step0Labels = mixedMoment B raw23679step1 raw23679step1Labels := by
      have ha : raw23679step1 = (fun i j => raw23679step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23679step1 raw23679step0; decide +kernel
      have hl : raw23679step1Labels = raw23679step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23679step0 raw23679step0Labels permutation39 permutation2
    _ = mixedMoment B node738 node738Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23680 raw23680Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw23680 raw23680Labels = mixedMoment B raw23680step0 raw23680step0Labels := by
      have ha : raw23680step0 = (fun i j => raw23680 (permutation207 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23680step0 raw23680; decide +kernel
      have hl : raw23680step0Labels = raw23680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23680 raw23680Labels permutation207 permutation2
    _ = mixedMoment B node703 node703Labels := by rfl

theorem canonical23681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23681 raw23681Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23681 raw23681Labels = mixedMoment B raw23681step0 raw23681step0Labels := by
      have hz : ∀ j, raw23681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23681step0 = (fun i j => raw23681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23681step0 raw23681; decide +kernel
      have hl : raw23681step0Labels = raw23681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23681 raw23681Labels permutation434 hz
    mixedMoment B raw23681step0 raw23681step0Labels = mixedMoment B raw23681step1 raw23681step1Labels := by
      have ha : raw23681step1 = (fun i j => raw23681step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23681step1 raw23681step0; decide +kernel
      have hl : raw23681step1Labels = raw23681step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23681step0 raw23681step0Labels permutation42 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical23682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23682 raw23682Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw23682 raw23682Labels = mixedMoment B raw23682step0 raw23682step0Labels := by
      have hz : ∀ j, raw23682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23682step0 = (fun i j => raw23682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23682step0 raw23682; decide +kernel
      have hl : raw23682step0Labels = raw23682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23682 raw23682Labels permutation434 hz
    mixedMoment B raw23682step0 raw23682step0Labels = mixedMoment B raw23682step1 raw23682step1Labels := by
      have ha : raw23682step1 = (fun i j => raw23682step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23682step1 raw23682step0; decide +kernel
      have hl : raw23682step1Labels = raw23682step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23682step0 raw23682step0Labels permutation33 permutation4
    mixedMoment B raw23682step1 raw23682step1Labels = mixedMoment B raw23682step2 raw23682step2Labels := by
      have ha : raw23682step2 = -raw23682step1 := by apply Matrix.ext; change ∀ i j, raw23682step2 i j = -(raw23682step1 i j); unfold raw23682step2 raw23682step1; decide +kernel
      have hl : raw23682step2Labels = raw23682step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node552 node552Labels := by rfl

theorem canonical23683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23683 raw23683Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23683 raw23683Labels = mixedMoment B raw23683step0 raw23683step0Labels := by
      have hz : ∀ j, raw23683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23683step0 = (fun i j => raw23683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23683step0 raw23683; decide +kernel
      have hl : raw23683step0Labels = raw23683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23683 raw23683Labels permutation434 hz
    mixedMoment B raw23683step0 raw23683step0Labels = mixedMoment B raw23683step1 raw23683step1Labels := by
      have hz : ∀ j, raw23683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23683step1 = (fun i j => raw23683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23683step1 raw23683step0; decide +kernel
      have hl : raw23683step1Labels = raw23683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23683step0 raw23683step0Labels permutation56 hz
    mixedMoment B raw23683step1 raw23683step1Labels = mixedMoment B raw23683step2 raw23683step2Labels := by
      have ha : raw23683step2 = (fun i j => raw23683step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23683step2 raw23683step1; decide +kernel
      have hl : raw23683step2Labels = raw23683step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23683step1 raw23683step1Labels permutation9 permutation4
    mixedMoment B raw23683step2 raw23683step2Labels = mixedMoment B raw23683step3 raw23683step3Labels := by
      have ha : raw23683step3 = -raw23683step2 := by apply Matrix.ext; change ∀ i j, raw23683step3 i j = -(raw23683step2 i j); unfold raw23683step3 raw23683step2; decide +kernel
      have hl : raw23683step3Labels = raw23683step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node852 node852Labels := by rfl

theorem canonical23684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23684 raw23684Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw23684 raw23684Labels = mixedMoment B raw23684step0 raw23684step0Labels := by
      have hz : ∀ j, raw23684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23684step0 = (fun i j => raw23684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23684step0 raw23684; decide +kernel
      have hl : raw23684step0Labels = raw23684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23684 raw23684Labels permutation434 hz
    mixedMoment B raw23684step0 raw23684step0Labels = mixedMoment B raw23684step1 raw23684step1Labels := by
      have ha : raw23684step1 = (fun i j => raw23684step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23684step1 raw23684step0; decide +kernel
      have hl : raw23684step1Labels = raw23684step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23684step0 raw23684step0Labels permutation32 permutation4
    mixedMoment B raw23684step1 raw23684step1Labels = mixedMoment B raw23684step2 raw23684step2Labels := by
      have ha : raw23684step2 = -raw23684step1 := by apply Matrix.ext; change ∀ i j, raw23684step2 i j = -(raw23684step1 i j); unfold raw23684step2 raw23684step1; decide +kernel
      have hl : raw23684step2Labels = raw23684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical23685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23685 raw23685Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw23685 raw23685Labels = mixedMoment B raw23685step0 raw23685step0Labels := by
      have hz : ∀ j, raw23685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23685step0 = (fun i j => raw23685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23685step0 raw23685; decide +kernel
      have hl : raw23685step0Labels = raw23685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23685 raw23685Labels permutation434 hz
    mixedMoment B raw23685step0 raw23685step0Labels = mixedMoment B raw23685step1 raw23685step1Labels := by
      have ha : raw23685step1 = (fun i j => raw23685step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23685step1 raw23685step0; decide +kernel
      have hl : raw23685step1Labels = raw23685step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23685step0 raw23685step0Labels permutation50 permutation4
    mixedMoment B raw23685step1 raw23685step1Labels = mixedMoment B raw23685step2 raw23685step2Labels := by
      have ha : raw23685step2 = -raw23685step1 := by apply Matrix.ext; change ∀ i j, raw23685step2 i j = -(raw23685step1 i j); unfold raw23685step2 raw23685step1; decide +kernel
      have hl : raw23685step2Labels = raw23685step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical23686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23686 raw23686Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw23686 raw23686Labels = mixedMoment B raw23686step0 raw23686step0Labels := by
      have hz : ∀ j, raw23686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23686step0 = (fun i j => raw23686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23686step0 raw23686; decide +kernel
      have hl : raw23686step0Labels = raw23686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23686 raw23686Labels permutation434 hz
    _ = mixedMoment B node1641 node1641Labels := by rfl

theorem canonical23687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23687 raw23687Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw23687 raw23687Labels = mixedMoment B raw23687step0 raw23687step0Labels := by
      have hz : ∀ j, raw23687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23687step0 = (fun i j => raw23687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23687step0 raw23687; decide +kernel
      have hl : raw23687step0Labels = raw23687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23687 raw23687Labels permutation434 hz
    mixedMoment B raw23687step0 raw23687step0Labels = mixedMoment B raw23687step1 raw23687step1Labels := by
      have ha : raw23687step1 = (fun i j => raw23687step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23687step1 raw23687step0; decide +kernel
      have hl : raw23687step1Labels = raw23687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23687step0 raw23687step0Labels permutation38 permutation2
    _ = mixedMoment B node1641 node1641Labels := by rfl

theorem canonical23688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23688 raw23688Labels = mixedMoment B node1595 node1595Labels := by
  calc
    mixedMoment B raw23688 raw23688Labels = mixedMoment B raw23688step0 raw23688step0Labels := by
      have ha : raw23688step0 = (fun i j => raw23688 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23688step0 raw23688; decide +kernel
      have hl : raw23688step0Labels = raw23688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23688 raw23688Labels permutation200 permutation2
    _ = mixedMoment B node1595 node1595Labels := by rfl

theorem canonical23689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23689 raw23689Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw23689 raw23689Labels = mixedMoment B raw23689step0 raw23689step0Labels := by
      have hz : ∀ j, raw23689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23689step0 = (fun i j => raw23689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23689step0 raw23689; decide +kernel
      have hl : raw23689step0Labels = raw23689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23689 raw23689Labels permutation434 hz
    mixedMoment B raw23689step0 raw23689step0Labels = mixedMoment B raw23689step1 raw23689step1Labels := by
      have ha : raw23689step1 = (fun i j => raw23689step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23689step1 raw23689step0; decide +kernel
      have hl : raw23689step1Labels = raw23689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23689step0 raw23689step0Labels permutation33 permutation2
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical23690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23690 raw23690Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw23690 raw23690Labels = mixedMoment B raw23690step0 raw23690step0Labels := by
      have hz : ∀ j, raw23690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23690step0 = (fun i j => raw23690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23690step0 raw23690; decide +kernel
      have hl : raw23690step0Labels = raw23690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23690 raw23690Labels permutation434 hz
    mixedMoment B raw23690step0 raw23690step0Labels = mixedMoment B raw23690step1 raw23690step1Labels := by
      have ha : raw23690step1 = (fun i j => raw23690step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23690step1 raw23690step0; decide +kernel
      have hl : raw23690step1Labels = raw23690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23690step0 raw23690step0Labels permutation38 permutation2
    _ = mixedMoment B node544 node544Labels := by rfl

theorem canonical23691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23691 raw23691Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw23691 raw23691Labels = mixedMoment B raw23691step0 raw23691step0Labels := by
      have hz : ∀ j, raw23691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23691step0 = (fun i j => raw23691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23691step0 raw23691; decide +kernel
      have hl : raw23691step0Labels = raw23691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23691 raw23691Labels permutation434 hz
    mixedMoment B raw23691step0 raw23691step0Labels = mixedMoment B raw23691step1 raw23691step1Labels := by
      have ha : raw23691step1 = (fun i j => raw23691step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23691step1 raw23691step0; decide +kernel
      have hl : raw23691step1Labels = raw23691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23691step0 raw23691step0Labels permutation38 permutation2
    _ = mixedMoment B node739 node739Labels := by rfl

theorem canonical23692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23692 raw23692Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw23692 raw23692Labels = mixedMoment B raw23692step0 raw23692step0Labels := by
      have ha : raw23692step0 = (fun i j => raw23692 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23692step0 raw23692; decide +kernel
      have hl : raw23692step0Labels = raw23692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23692 raw23692Labels permutation206 permutation2
    _ = mixedMoment B node704 node704Labels := by rfl

theorem canonical23693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23693 raw23693Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw23693 raw23693Labels = mixedMoment B raw23693step0 raw23693step0Labels := by
      have hz : ∀ j, raw23693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23693step0 = (fun i j => raw23693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23693step0 raw23693; decide +kernel
      have hl : raw23693step0Labels = raw23693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23693 raw23693Labels permutation434 hz
    mixedMoment B raw23693step0 raw23693step0Labels = mixedMoment B raw23693step1 raw23693step1Labels := by
      have ha : raw23693step1 = (fun i j => raw23693step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23693step1 raw23693step0; decide +kernel
      have hl : raw23693step1Labels = raw23693step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23693step0 raw23693step0Labels permutation39 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical23724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23724 raw23724Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw23724 raw23724Labels = mixedMoment B raw23724step0 raw23724step0Labels := by
      have hz : ∀ j, raw23724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23724step0 = (fun i j => raw23724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23724step0 raw23724; decide +kernel
      have hl : raw23724step0Labels = raw23724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23724 raw23724Labels permutation434 hz
    mixedMoment B raw23724step0 raw23724step0Labels = mixedMoment B raw23724step1 raw23724step1Labels := by
      have hz : ∀ j, raw23724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23724step1 = (fun i j => raw23724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23724step1 raw23724step0; decide +kernel
      have hl : raw23724step1Labels = raw23724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23724step0 raw23724step0Labels permutation80 hz
    mixedMoment B raw23724step1 raw23724step1Labels = mixedMoment B raw23724step2 raw23724step2Labels := by
      have ha : raw23724step2 = (fun i j => raw23724step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23724step2 raw23724step1; decide +kernel
      have hl : raw23724step2Labels = raw23724step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23724step1 raw23724step1Labels permutation9 permutation7
    mixedMoment B raw23724step2 raw23724step2Labels = mixedMoment B raw23724step3 raw23724step3Labels := by
      have ha : raw23724step3 = -raw23724step2 := by apply Matrix.ext; change ∀ i j, raw23724step3 i j = -(raw23724step2 i j); unfold raw23724step3 raw23724step2; decide +kernel
      have hl : raw23724step3Labels = raw23724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23724step3 raw23724step3Labels = mixedMoment B raw23724step4 raw23724step4Labels := by
      have ha : raw23724step4 = raw23724step3 := by apply Matrix.ext; unfold raw23724step4 raw23724step3; decide +kernel
      have hl : raw23724step3Labels = labelEmbedding1 ∘ raw23724step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23724step3 raw23724step3Labels raw23724step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical23725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23725 raw23725Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw23725 raw23725Labels = mixedMoment B raw23725step0 raw23725step0Labels := by
      have hz : ∀ j, raw23725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23725step0 = (fun i j => raw23725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23725step0 raw23725; decide +kernel
      have hl : raw23725step0Labels = raw23725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23725 raw23725Labels permutation434 hz
    mixedMoment B raw23725step0 raw23725step0Labels = mixedMoment B raw23725step1 raw23725step1Labels := by
      have ha : raw23725step1 = (fun i j => raw23725step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23725step1 raw23725step0; decide +kernel
      have hl : raw23725step1Labels = raw23725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23725step0 raw23725step0Labels permutation39 permutation7
    mixedMoment B raw23725step1 raw23725step1Labels = mixedMoment B raw23725step2 raw23725step2Labels := by
      have ha : raw23725step2 = -raw23725step1 := by apply Matrix.ext; change ∀ i j, raw23725step2 i j = -(raw23725step1 i j); unfold raw23725step2 raw23725step1; decide +kernel
      have hl : raw23725step2Labels = raw23725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23725step2 raw23725step2Labels = mixedMoment B raw23725step3 raw23725step3Labels := by
      have ha : raw23725step3 = raw23725step2 := by apply Matrix.ext; unfold raw23725step3 raw23725step2; decide +kernel
      have hl : raw23725step2Labels = labelEmbedding1 ∘ raw23725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23725step2 raw23725step2Labels raw23725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical23726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23726 raw23726Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw23726 raw23726Labels = mixedMoment B raw23726step0 raw23726step0Labels := by
      have hz : ∀ j, raw23726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23726step0 = (fun i j => raw23726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23726step0 raw23726; decide +kernel
      have hl : raw23726step0Labels = raw23726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23726 raw23726Labels permutation346 hz
    mixedMoment B raw23726step0 raw23726step0Labels = mixedMoment B raw23726step1 raw23726step1Labels := by
      have ha : raw23726step1 = (fun i j => raw23726step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23726step1 raw23726step0; decide +kernel
      have hl : raw23726step1Labels = raw23726step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23726step0 raw23726step0Labels permutation39 permutation7
    mixedMoment B raw23726step1 raw23726step1Labels = mixedMoment B raw23726step2 raw23726step2Labels := by
      have ha : raw23726step2 = -raw23726step1 := by apply Matrix.ext; change ∀ i j, raw23726step2 i j = -(raw23726step1 i j); unfold raw23726step2 raw23726step1; decide +kernel
      have hl : raw23726step2Labels = raw23726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23726step2 raw23726step2Labels = mixedMoment B raw23726step3 raw23726step3Labels := by
      have ha : raw23726step3 = raw23726step2 := by apply Matrix.ext; unfold raw23726step3 raw23726step2; decide +kernel
      have hl : raw23726step2Labels = labelEmbedding1 ∘ raw23726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23726step2 raw23726step2Labels raw23726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical23727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23727 raw23727Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23727 raw23727Labels = mixedMoment B raw23727step0 raw23727step0Labels := by
      have hz : ∀ j, raw23727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23727step0 = (fun i j => raw23727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23727step0 raw23727; decide +kernel
      have hl : raw23727step0Labels = raw23727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23727 raw23727Labels permutation434 hz
    mixedMoment B raw23727step0 raw23727step0Labels = mixedMoment B raw23727step1 raw23727step1Labels := by
      have hz : ∀ j, raw23727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23727step1 = (fun i j => raw23727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23727step1 raw23727step0; decide +kernel
      have hl : raw23727step1Labels = raw23727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23727step0 raw23727step0Labels permutation80 hz
    mixedMoment B raw23727step1 raw23727step1Labels = mixedMoment B raw23727step2 raw23727step2Labels := by
      have ha : raw23727step2 = (fun i j => raw23727step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23727step2 raw23727step1; decide +kernel
      have hl : raw23727step2Labels = raw23727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23727step1 raw23727step1Labels permutation9 permutation7
    mixedMoment B raw23727step2 raw23727step2Labels = mixedMoment B raw23727step3 raw23727step3Labels := by
      have ha : raw23727step3 = -raw23727step2 := by apply Matrix.ext; change ∀ i j, raw23727step3 i j = -(raw23727step2 i j); unfold raw23727step3 raw23727step2; decide +kernel
      have hl : raw23727step3Labels = raw23727step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23727step3 raw23727step3Labels = mixedMoment B raw23727step4 raw23727step4Labels := by
      have ha : raw23727step4 = raw23727step3 := by apply Matrix.ext; unfold raw23727step4 raw23727step3; decide +kernel
      have hl : raw23727step3Labels = labelEmbedding1 ∘ raw23727step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23727step3 raw23727step3Labels raw23727step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical23728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23728 raw23728Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw23728 raw23728Labels = mixedMoment B raw23728step0 raw23728step0Labels := by
      have hz : ∀ j, raw23728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23728step0 = (fun i j => raw23728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23728step0 raw23728; decide +kernel
      have hl : raw23728step0Labels = raw23728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23728 raw23728Labels permutation434 hz
    mixedMoment B raw23728step0 raw23728step0Labels = mixedMoment B raw23728step1 raw23728step1Labels := by
      have hz : ∀ j, raw23728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23728step1 = (fun i j => raw23728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23728step1 raw23728step0; decide +kernel
      have hl : raw23728step1Labels = raw23728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23728step0 raw23728step0Labels permutation80 hz
    mixedMoment B raw23728step1 raw23728step1Labels = mixedMoment B raw23728step2 raw23728step2Labels := by
      have ha : raw23728step2 = (fun i j => raw23728step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23728step2 raw23728step1; decide +kernel
      have hl : raw23728step2Labels = raw23728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23728step1 raw23728step1Labels permutation9 permutation7
    mixedMoment B raw23728step2 raw23728step2Labels = mixedMoment B raw23728step3 raw23728step3Labels := by
      have ha : raw23728step3 = -raw23728step2 := by apply Matrix.ext; change ∀ i j, raw23728step3 i j = -(raw23728step2 i j); unfold raw23728step3 raw23728step2; decide +kernel
      have hl : raw23728step3Labels = raw23728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23728step3 raw23728step3Labels = mixedMoment B raw23728step4 raw23728step4Labels := by
      have ha : raw23728step4 = raw23728step3 := by apply Matrix.ext; unfold raw23728step4 raw23728step3; decide +kernel
      have hl : raw23728step3Labels = labelEmbedding1 ∘ raw23728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23728step3 raw23728step3Labels raw23728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1082 node1082Labels := by rfl

theorem canonical23729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23729 raw23729Labels = mixedMoment B node689 node689Labels := by
  calc
    mixedMoment B raw23729 raw23729Labels = mixedMoment B raw23729step0 raw23729step0Labels := by
      have hz : ∀ j, raw23729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23729step0 = (fun i j => raw23729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23729step0 raw23729; decide +kernel
      have hl : raw23729step0Labels = raw23729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23729 raw23729Labels permutation434 hz
    mixedMoment B raw23729step0 raw23729step0Labels = mixedMoment B raw23729step1 raw23729step1Labels := by
      have hz : ∀ j, raw23729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23729step1 = (fun i j => raw23729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23729step1 raw23729step0; decide +kernel
      have hl : raw23729step1Labels = raw23729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23729step0 raw23729step0Labels permutation80 hz
    mixedMoment B raw23729step1 raw23729step1Labels = mixedMoment B raw23729step2 raw23729step2Labels := by
      have ha : raw23729step2 = (fun i j => raw23729step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23729step2 raw23729step1; decide +kernel
      have hl : raw23729step2Labels = raw23729step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23729step1 raw23729step1Labels permutation9 permutation7
    mixedMoment B raw23729step2 raw23729step2Labels = mixedMoment B raw23729step3 raw23729step3Labels := by
      have ha : raw23729step3 = -raw23729step2 := by apply Matrix.ext; change ∀ i j, raw23729step3 i j = -(raw23729step2 i j); unfold raw23729step3 raw23729step2; decide +kernel
      have hl : raw23729step3Labels = raw23729step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23729step3 raw23729step3Labels = mixedMoment B raw23729step4 raw23729step4Labels := by
      have ha : raw23729step4 = raw23729step3 := by apply Matrix.ext; unfold raw23729step4 raw23729step3; decide +kernel
      have hl : raw23729step3Labels = labelEmbedding1 ∘ raw23729step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23729step3 raw23729step3Labels raw23729step4Labels labelEmbedding1 hl
    _ = mixedMoment B node689 node689Labels := by rfl

theorem canonical23730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23730 raw23730Labels = mixedMoment B node768 node768Labels := by
  calc
    mixedMoment B raw23730 raw23730Labels = mixedMoment B raw23730step0 raw23730step0Labels := by
      have hz : ∀ j, raw23730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23730step0 = (fun i j => raw23730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23730step0 raw23730; decide +kernel
      have hl : raw23730step0Labels = raw23730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23730 raw23730Labels permutation434 hz
    mixedMoment B raw23730step0 raw23730step0Labels = mixedMoment B raw23730step1 raw23730step1Labels := by
      have ha : raw23730step1 = (fun i j => raw23730step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23730step1 raw23730step0; decide +kernel
      have hl : raw23730step1Labels = raw23730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23730step0 raw23730step0Labels permutation39 permutation7
    mixedMoment B raw23730step1 raw23730step1Labels = mixedMoment B raw23730step2 raw23730step2Labels := by
      have ha : raw23730step2 = -raw23730step1 := by apply Matrix.ext; change ∀ i j, raw23730step2 i j = -(raw23730step1 i j); unfold raw23730step2 raw23730step1; decide +kernel
      have hl : raw23730step2Labels = raw23730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23730step2 raw23730step2Labels = mixedMoment B raw23730step3 raw23730step3Labels := by
      have ha : raw23730step3 = raw23730step2 := by apply Matrix.ext; unfold raw23730step3 raw23730step2; decide +kernel
      have hl : raw23730step2Labels = labelEmbedding1 ∘ raw23730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23730step2 raw23730step2Labels raw23730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node768 node768Labels := by rfl

theorem canonical23731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23731 raw23731Labels = mixedMoment B node768 node768Labels := by
  calc
    mixedMoment B raw23731 raw23731Labels = mixedMoment B raw23731step0 raw23731step0Labels := by
      have hz : ∀ j, raw23731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23731step0 = (fun i j => raw23731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23731step0 raw23731; decide +kernel
      have hl : raw23731step0Labels = raw23731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23731 raw23731Labels permutation346 hz
    mixedMoment B raw23731step0 raw23731step0Labels = mixedMoment B raw23731step1 raw23731step1Labels := by
      have ha : raw23731step1 = (fun i j => raw23731step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23731step1 raw23731step0; decide +kernel
      have hl : raw23731step1Labels = raw23731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23731step0 raw23731step0Labels permutation39 permutation7
    mixedMoment B raw23731step1 raw23731step1Labels = mixedMoment B raw23731step2 raw23731step2Labels := by
      have ha : raw23731step2 = -raw23731step1 := by apply Matrix.ext; change ∀ i j, raw23731step2 i j = -(raw23731step1 i j); unfold raw23731step2 raw23731step1; decide +kernel
      have hl : raw23731step2Labels = raw23731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23731step2 raw23731step2Labels = mixedMoment B raw23731step3 raw23731step3Labels := by
      have ha : raw23731step3 = raw23731step2 := by apply Matrix.ext; unfold raw23731step3 raw23731step2; decide +kernel
      have hl : raw23731step2Labels = labelEmbedding1 ∘ raw23731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23731step2 raw23731step2Labels raw23731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node768 node768Labels := by rfl

theorem canonical23732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23732 raw23732Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw23732 raw23732Labels = mixedMoment B raw23732step0 raw23732step0Labels := by
      have hz : ∀ j, raw23732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23732step0 = (fun i j => raw23732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23732step0 raw23732; decide +kernel
      have hl : raw23732step0Labels = raw23732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23732 raw23732Labels permutation434 hz
    mixedMoment B raw23732step0 raw23732step0Labels = mixedMoment B raw23732step1 raw23732step1Labels := by
      have hz : ∀ j, raw23732step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23732step1 = (fun i j => raw23732step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23732step1 raw23732step0; decide +kernel
      have hl : raw23732step1Labels = raw23732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23732step0 raw23732step0Labels permutation80 hz
    mixedMoment B raw23732step1 raw23732step1Labels = mixedMoment B raw23732step2 raw23732step2Labels := by
      have ha : raw23732step2 = (fun i j => raw23732step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23732step2 raw23732step1; decide +kernel
      have hl : raw23732step2Labels = raw23732step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23732step1 raw23732step1Labels permutation9 permutation7
    mixedMoment B raw23732step2 raw23732step2Labels = mixedMoment B raw23732step3 raw23732step3Labels := by
      have ha : raw23732step3 = -raw23732step2 := by apply Matrix.ext; change ∀ i j, raw23732step3 i j = -(raw23732step2 i j); unfold raw23732step3 raw23732step2; decide +kernel
      have hl : raw23732step3Labels = raw23732step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23732step3 raw23732step3Labels = mixedMoment B raw23732step4 raw23732step4Labels := by
      have ha : raw23732step4 = raw23732step3 := by apply Matrix.ext; unfold raw23732step4 raw23732step3; decide +kernel
      have hl : raw23732step3Labels = labelEmbedding1 ∘ raw23732step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23732step3 raw23732step3Labels raw23732step4Labels labelEmbedding1 hl
    _ = mixedMoment B node856 node856Labels := by rfl

theorem canonical23733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23733 raw23733Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23733 raw23733Labels = mixedMoment B raw23733step0 raw23733step0Labels := by
      have hz : ∀ j, raw23733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23733step0 = (fun i j => raw23733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23733step0 raw23733; decide +kernel
      have hl : raw23733step0Labels = raw23733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23733 raw23733Labels permutation434 hz
    mixedMoment B raw23733step0 raw23733step0Labels = mixedMoment B raw23733step1 raw23733step1Labels := by
      have hz : ∀ j, raw23733step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23733step1 = (fun i j => raw23733step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23733step1 raw23733step0; decide +kernel
      have hl : raw23733step1Labels = raw23733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23733step0 raw23733step0Labels permutation80 hz
    mixedMoment B raw23733step1 raw23733step1Labels = mixedMoment B raw23733step2 raw23733step2Labels := by
      have hz : ∀ i, raw23733step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23733step2 = (fun i j => raw23733step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23733step2 raw23733step1; decide +kernel
      have hl : raw23733step2Labels = (fun j => raw23733step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23733step1 raw23733step1Labels permutation4 hz
    mixedMoment B raw23733step2 raw23733step2Labels = mixedMoment B raw23733step3 raw23733step3Labels := by
      have ha : raw23733step3 = (fun i j => raw23733step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23733step3 raw23733step2; decide +kernel
      have hl : raw23733step3Labels = raw23733step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23733step2 raw23733step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23734 raw23734Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw23734 raw23734Labels = mixedMoment B raw23734step0 raw23734step0Labels := by
      have hz : ∀ j, raw23734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23734step0 = (fun i j => raw23734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23734step0 raw23734; decide +kernel
      have hl : raw23734step0Labels = raw23734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23734 raw23734Labels permutation434 hz
    mixedMoment B raw23734step0 raw23734step0Labels = mixedMoment B raw23734step1 raw23734step1Labels := by
      have ha : raw23734step1 = (fun i j => raw23734step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23734step1 raw23734step0; decide +kernel
      have hl : raw23734step1Labels = raw23734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23734step0 raw23734step0Labels permutation39 permutation7
    mixedMoment B raw23734step1 raw23734step1Labels = mixedMoment B raw23734step2 raw23734step2Labels := by
      have ha : raw23734step2 = -raw23734step1 := by apply Matrix.ext; change ∀ i j, raw23734step2 i j = -(raw23734step1 i j); unfold raw23734step2 raw23734step1; decide +kernel
      have hl : raw23734step2Labels = raw23734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23734step2 raw23734step2Labels = mixedMoment B raw23734step3 raw23734step3Labels := by
      have ha : raw23734step3 = raw23734step2 := by apply Matrix.ext; unfold raw23734step3 raw23734step2; decide +kernel
      have hl : raw23734step2Labels = labelEmbedding1 ∘ raw23734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23734step2 raw23734step2Labels raw23734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

theorem canonical23735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23735 raw23735Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw23735 raw23735Labels = mixedMoment B raw23735step0 raw23735step0Labels := by
      have hz : ∀ j, raw23735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23735step0 = (fun i j => raw23735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23735step0 raw23735; decide +kernel
      have hl : raw23735step0Labels = raw23735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23735 raw23735Labels permutation434 hz
    mixedMoment B raw23735step0 raw23735step0Labels = mixedMoment B raw23735step1 raw23735step1Labels := by
      have ha : raw23735step1 = (fun i j => raw23735step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23735step1 raw23735step0; decide +kernel
      have hl : raw23735step1Labels = raw23735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23735step0 raw23735step0Labels permutation39 permutation7
    mixedMoment B raw23735step1 raw23735step1Labels = mixedMoment B raw23735step2 raw23735step2Labels := by
      have ha : raw23735step2 = -raw23735step1 := by apply Matrix.ext; change ∀ i j, raw23735step2 i j = -(raw23735step1 i j); unfold raw23735step2 raw23735step1; decide +kernel
      have hl : raw23735step2Labels = raw23735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23735step2 raw23735step2Labels = mixedMoment B raw23735step3 raw23735step3Labels := by
      have ha : raw23735step3 = raw23735step2 := by apply Matrix.ext; unfold raw23735step3 raw23735step2; decide +kernel
      have hl : raw23735step2Labels = labelEmbedding1 ∘ raw23735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23735step2 raw23735step2Labels raw23735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

theorem canonical23736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23736 raw23736Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw23736 raw23736Labels = mixedMoment B raw23736step0 raw23736step0Labels := by
      have ha : raw23736step0 = (fun i j => raw23736 (permutation207 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23736step0 raw23736; decide +kernel
      have hl : raw23736step0Labels = raw23736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23736 raw23736Labels permutation207 permutation7
    mixedMoment B raw23736step0 raw23736step0Labels = mixedMoment B raw23736step1 raw23736step1Labels := by
      have ha : raw23736step1 = -raw23736step0 := by apply Matrix.ext; change ∀ i j, raw23736step1 i j = -(raw23736step0 i j); unfold raw23736step1 raw23736step0; decide +kernel
      have hl : raw23736step1Labels = raw23736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23736step1 raw23736step1Labels = mixedMoment B raw23736step2 raw23736step2Labels := by
      have ha : raw23736step2 = raw23736step1 := by apply Matrix.ext; unfold raw23736step2 raw23736step1; decide +kernel
      have hl : raw23736step1Labels = labelEmbedding1 ∘ raw23736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23736step1 raw23736step1Labels raw23736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

theorem canonical23737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23737 raw23737Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23737 raw23737Labels = mixedMoment B raw23737step0 raw23737step0Labels := by
      have hz : ∀ j, raw23737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23737step0 = (fun i j => raw23737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23737step0 raw23737; decide +kernel
      have hl : raw23737step0Labels = raw23737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23737 raw23737Labels permutation434 hz
    mixedMoment B raw23737step0 raw23737step0Labels = mixedMoment B raw23737step1 raw23737step1Labels := by
      have ha : raw23737step1 = (fun i j => raw23737step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23737step1 raw23737step0; decide +kernel
      have hl : raw23737step1Labels = raw23737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23737step0 raw23737step0Labels permutation39 permutation7
    mixedMoment B raw23737step1 raw23737step1Labels = mixedMoment B raw23737step2 raw23737step2Labels := by
      have ha : raw23737step2 = -raw23737step1 := by apply Matrix.ext; change ∀ i j, raw23737step2 i j = -(raw23737step1 i j); unfold raw23737step2 raw23737step1; decide +kernel
      have hl : raw23737step2Labels = raw23737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23737step2 raw23737step2Labels = mixedMoment B raw23737step3 raw23737step3Labels := by
      have ha : raw23737step3 = raw23737step2 := by apply Matrix.ext; unfold raw23737step3 raw23737step2; decide +kernel
      have hl : raw23737step2Labels = labelEmbedding1 ∘ raw23737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23737step2 raw23737step2Labels raw23737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical23738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23738 raw23738Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23738 raw23738Labels = mixedMoment B raw23738step0 raw23738step0Labels := by
      have hz : ∀ j, raw23738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23738step0 = (fun i j => raw23738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23738step0 raw23738; decide +kernel
      have hl : raw23738step0Labels = raw23738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23738 raw23738Labels permutation434 hz
    mixedMoment B raw23738step0 raw23738step0Labels = mixedMoment B raw23738step1 raw23738step1Labels := by
      have ha : raw23738step1 = (fun i j => raw23738step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23738step1 raw23738step0; decide +kernel
      have hl : raw23738step1Labels = raw23738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23738step0 raw23738step0Labels permutation39 permutation7
    mixedMoment B raw23738step1 raw23738step1Labels = mixedMoment B raw23738step2 raw23738step2Labels := by
      have ha : raw23738step2 = -raw23738step1 := by apply Matrix.ext; change ∀ i j, raw23738step2 i j = -(raw23738step1 i j); unfold raw23738step2 raw23738step1; decide +kernel
      have hl : raw23738step2Labels = raw23738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23738step2 raw23738step2Labels = mixedMoment B raw23738step3 raw23738step3Labels := by
      have ha : raw23738step3 = raw23738step2 := by apply Matrix.ext; unfold raw23738step3 raw23738step2; decide +kernel
      have hl : raw23738step2Labels = labelEmbedding1 ∘ raw23738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23738step2 raw23738step2Labels raw23738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical23739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23739 raw23739Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw23739 raw23739Labels = mixedMoment B raw23739step0 raw23739step0Labels := by
      have hz : ∀ j, raw23739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23739step0 = (fun i j => raw23739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23739step0 raw23739; decide +kernel
      have hl : raw23739step0Labels = raw23739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23739 raw23739Labels permutation346 hz
    mixedMoment B raw23739step0 raw23739step0Labels = mixedMoment B raw23739step1 raw23739step1Labels := by
      have ha : raw23739step1 = (fun i j => raw23739step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23739step1 raw23739step0; decide +kernel
      have hl : raw23739step1Labels = raw23739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23739step0 raw23739step0Labels permutation39 permutation7
    mixedMoment B raw23739step1 raw23739step1Labels = mixedMoment B raw23739step2 raw23739step2Labels := by
      have ha : raw23739step2 = -raw23739step1 := by apply Matrix.ext; change ∀ i j, raw23739step2 i j = -(raw23739step1 i j); unfold raw23739step2 raw23739step1; decide +kernel
      have hl : raw23739step2Labels = raw23739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23739step2 raw23739step2Labels = mixedMoment B raw23739step3 raw23739step3Labels := by
      have ha : raw23739step3 = raw23739step2 := by apply Matrix.ext; unfold raw23739step3 raw23739step2; decide +kernel
      have hl : raw23739step2Labels = labelEmbedding1 ∘ raw23739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23739step2 raw23739step2Labels raw23739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

theorem canonical23740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23740 raw23740Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw23740 raw23740Labels = mixedMoment B raw23740step0 raw23740step0Labels := by
      have hz : ∀ j, raw23740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23740step0 = (fun i j => raw23740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23740step0 raw23740; decide +kernel
      have hl : raw23740step0Labels = raw23740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23740 raw23740Labels permutation346 hz
    mixedMoment B raw23740step0 raw23740step0Labels = mixedMoment B raw23740step1 raw23740step1Labels := by
      have ha : raw23740step1 = (fun i j => raw23740step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23740step1 raw23740step0; decide +kernel
      have hl : raw23740step1Labels = raw23740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23740step0 raw23740step0Labels permutation39 permutation7
    mixedMoment B raw23740step1 raw23740step1Labels = mixedMoment B raw23740step2 raw23740step2Labels := by
      have ha : raw23740step2 = -raw23740step1 := by apply Matrix.ext; change ∀ i j, raw23740step2 i j = -(raw23740step1 i j); unfold raw23740step2 raw23740step1; decide +kernel
      have hl : raw23740step2Labels = raw23740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23740step2 raw23740step2Labels = mixedMoment B raw23740step3 raw23740step3Labels := by
      have ha : raw23740step3 = raw23740step2 := by apply Matrix.ext; unfold raw23740step3 raw23740step2; decide +kernel
      have hl : raw23740step2Labels = labelEmbedding1 ∘ raw23740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23740step2 raw23740step2Labels raw23740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

theorem canonical23741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23741 raw23741Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw23741 raw23741Labels = mixedMoment B raw23741step0 raw23741step0Labels := by
      have ha : raw23741step0 = (fun i j => raw23741 (permutation183 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23741step0 raw23741; decide +kernel
      have hl : raw23741step0Labels = raw23741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23741 raw23741Labels permutation183 permutation7
    mixedMoment B raw23741step0 raw23741step0Labels = mixedMoment B raw23741step1 raw23741step1Labels := by
      have ha : raw23741step1 = -raw23741step0 := by apply Matrix.ext; change ∀ i j, raw23741step1 i j = -(raw23741step0 i j); unfold raw23741step1 raw23741step0; decide +kernel
      have hl : raw23741step1Labels = raw23741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23741step1 raw23741step1Labels = mixedMoment B raw23741step2 raw23741step2Labels := by
      have ha : raw23741step2 = raw23741step1 := by apply Matrix.ext; unfold raw23741step2 raw23741step1; decide +kernel
      have hl : raw23741step1Labels = labelEmbedding1 ∘ raw23741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23741step1 raw23741step1Labels raw23741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

theorem canonical23742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23742 raw23742Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23742 raw23742Labels = mixedMoment B raw23742step0 raw23742step0Labels := by
      have hz : ∀ j, raw23742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23742step0 = (fun i j => raw23742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23742step0 raw23742; decide +kernel
      have hl : raw23742step0Labels = raw23742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23742 raw23742Labels permutation346 hz
    mixedMoment B raw23742step0 raw23742step0Labels = mixedMoment B raw23742step1 raw23742step1Labels := by
      have ha : raw23742step1 = (fun i j => raw23742step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23742step1 raw23742step0; decide +kernel
      have hl : raw23742step1Labels = raw23742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23742step0 raw23742step0Labels permutation39 permutation7
    mixedMoment B raw23742step1 raw23742step1Labels = mixedMoment B raw23742step2 raw23742step2Labels := by
      have ha : raw23742step2 = -raw23742step1 := by apply Matrix.ext; change ∀ i j, raw23742step2 i j = -(raw23742step1 i j); unfold raw23742step2 raw23742step1; decide +kernel
      have hl : raw23742step2Labels = raw23742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23742step2 raw23742step2Labels = mixedMoment B raw23742step3 raw23742step3Labels := by
      have ha : raw23742step3 = raw23742step2 := by apply Matrix.ext; unfold raw23742step3 raw23742step2; decide +kernel
      have hl : raw23742step2Labels = labelEmbedding1 ∘ raw23742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23742step2 raw23742step2Labels raw23742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical23743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23743 raw23743Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23743 raw23743Labels = mixedMoment B raw23743step0 raw23743step0Labels := by
      have hz : ∀ j, raw23743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23743step0 = (fun i j => raw23743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23743step0 raw23743; decide +kernel
      have hl : raw23743step0Labels = raw23743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23743 raw23743Labels permutation346 hz
    mixedMoment B raw23743step0 raw23743step0Labels = mixedMoment B raw23743step1 raw23743step1Labels := by
      have ha : raw23743step1 = (fun i j => raw23743step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23743step1 raw23743step0; decide +kernel
      have hl : raw23743step1Labels = raw23743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23743step0 raw23743step0Labels permutation39 permutation7
    mixedMoment B raw23743step1 raw23743step1Labels = mixedMoment B raw23743step2 raw23743step2Labels := by
      have ha : raw23743step2 = -raw23743step1 := by apply Matrix.ext; change ∀ i j, raw23743step2 i j = -(raw23743step1 i j); unfold raw23743step2 raw23743step1; decide +kernel
      have hl : raw23743step2Labels = raw23743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23743step2 raw23743step2Labels = mixedMoment B raw23743step3 raw23743step3Labels := by
      have ha : raw23743step3 = raw23743step2 := by apply Matrix.ext; unfold raw23743step3 raw23743step2; decide +kernel
      have hl : raw23743step2Labels = labelEmbedding1 ∘ raw23743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23743step2 raw23743step2Labels raw23743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical23744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23744 raw23744Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw23744 raw23744Labels = mixedMoment B raw23744step0 raw23744step0Labels := by
      have hz : ∀ j, raw23744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23744step0 = (fun i j => raw23744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23744step0 raw23744; decide +kernel
      have hl : raw23744step0Labels = raw23744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23744 raw23744Labels permutation434 hz
    mixedMoment B raw23744step0 raw23744step0Labels = mixedMoment B raw23744step1 raw23744step1Labels := by
      have hz : ∀ j, raw23744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23744step1 = (fun i j => raw23744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23744step1 raw23744step0; decide +kernel
      have hl : raw23744step1Labels = raw23744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23744step0 raw23744step0Labels permutation80 hz
    mixedMoment B raw23744step1 raw23744step1Labels = mixedMoment B raw23744step2 raw23744step2Labels := by
      have ha : raw23744step2 = (fun i j => raw23744step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23744step2 raw23744step1; decide +kernel
      have hl : raw23744step2Labels = raw23744step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23744step1 raw23744step1Labels permutation9 permutation7
    mixedMoment B raw23744step2 raw23744step2Labels = mixedMoment B raw23744step3 raw23744step3Labels := by
      have ha : raw23744step3 = -raw23744step2 := by apply Matrix.ext; change ∀ i j, raw23744step3 i j = -(raw23744step2 i j); unfold raw23744step3 raw23744step2; decide +kernel
      have hl : raw23744step3Labels = raw23744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23744step3 raw23744step3Labels = mixedMoment B raw23744step4 raw23744step4Labels := by
      have ha : raw23744step4 = raw23744step3 := by apply Matrix.ext; unfold raw23744step4 raw23744step3; decide +kernel
      have hl : raw23744step3Labels = labelEmbedding1 ∘ raw23744step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23744step3 raw23744step3Labels raw23744step4Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

theorem canonical23745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23745 raw23745Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw23745 raw23745Labels = mixedMoment B raw23745step0 raw23745step0Labels := by
      have hz : ∀ j, raw23745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23745step0 = (fun i j => raw23745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23745step0 raw23745; decide +kernel
      have hl : raw23745step0Labels = raw23745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23745 raw23745Labels permutation434 hz
    mixedMoment B raw23745step0 raw23745step0Labels = mixedMoment B raw23745step1 raw23745step1Labels := by
      have hz : ∀ j, raw23745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23745step1 = (fun i j => raw23745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23745step1 raw23745step0; decide +kernel
      have hl : raw23745step1Labels = raw23745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23745step0 raw23745step0Labels permutation80 hz
    mixedMoment B raw23745step1 raw23745step1Labels = mixedMoment B raw23745step2 raw23745step2Labels := by
      have ha : raw23745step2 = (fun i j => raw23745step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23745step2 raw23745step1; decide +kernel
      have hl : raw23745step2Labels = raw23745step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23745step1 raw23745step1Labels permutation9 permutation7
    mixedMoment B raw23745step2 raw23745step2Labels = mixedMoment B raw23745step3 raw23745step3Labels := by
      have ha : raw23745step3 = -raw23745step2 := by apply Matrix.ext; change ∀ i j, raw23745step3 i j = -(raw23745step2 i j); unfold raw23745step3 raw23745step2; decide +kernel
      have hl : raw23745step3Labels = raw23745step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23745step3 raw23745step3Labels = mixedMoment B raw23745step4 raw23745step4Labels := by
      have ha : raw23745step4 = raw23745step3 := by apply Matrix.ext; unfold raw23745step4 raw23745step3; decide +kernel
      have hl : raw23745step3Labels = labelEmbedding1 ∘ raw23745step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23745step3 raw23745step3Labels raw23745step4Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

theorem canonical23746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23746 raw23746Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw23746 raw23746Labels = mixedMoment B raw23746step0 raw23746step0Labels := by
      have hz : ∀ j, raw23746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23746step0 = (fun i j => raw23746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23746step0 raw23746; decide +kernel
      have hl : raw23746step0Labels = raw23746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23746 raw23746Labels permutation434 hz
    mixedMoment B raw23746step0 raw23746step0Labels = mixedMoment B raw23746step1 raw23746step1Labels := by
      have ha : raw23746step1 = (fun i j => raw23746step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23746step1 raw23746step0; decide +kernel
      have hl : raw23746step1Labels = raw23746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23746step0 raw23746step0Labels permutation39 permutation7
    mixedMoment B raw23746step1 raw23746step1Labels = mixedMoment B raw23746step2 raw23746step2Labels := by
      have ha : raw23746step2 = -raw23746step1 := by apply Matrix.ext; change ∀ i j, raw23746step2 i j = -(raw23746step1 i j); unfold raw23746step2 raw23746step1; decide +kernel
      have hl : raw23746step2Labels = raw23746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23746step2 raw23746step2Labels = mixedMoment B raw23746step3 raw23746step3Labels := by
      have ha : raw23746step3 = raw23746step2 := by apply Matrix.ext; unfold raw23746step3 raw23746step2; decide +kernel
      have hl : raw23746step2Labels = labelEmbedding1 ∘ raw23746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23746step2 raw23746step2Labels raw23746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical23747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23747 raw23747Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw23747 raw23747Labels = mixedMoment B raw23747step0 raw23747step0Labels := by
      have hz : ∀ j, raw23747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23747step0 = (fun i j => raw23747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23747step0 raw23747; decide +kernel
      have hl : raw23747step0Labels = raw23747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23747 raw23747Labels permutation346 hz
    mixedMoment B raw23747step0 raw23747step0Labels = mixedMoment B raw23747step1 raw23747step1Labels := by
      have ha : raw23747step1 = (fun i j => raw23747step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23747step1 raw23747step0; decide +kernel
      have hl : raw23747step1Labels = raw23747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23747step0 raw23747step0Labels permutation39 permutation7
    mixedMoment B raw23747step1 raw23747step1Labels = mixedMoment B raw23747step2 raw23747step2Labels := by
      have ha : raw23747step2 = -raw23747step1 := by apply Matrix.ext; change ∀ i j, raw23747step2 i j = -(raw23747step1 i j); unfold raw23747step2 raw23747step1; decide +kernel
      have hl : raw23747step2Labels = raw23747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23747step2 raw23747step2Labels = mixedMoment B raw23747step3 raw23747step3Labels := by
      have ha : raw23747step3 = raw23747step2 := by apply Matrix.ext; unfold raw23747step3 raw23747step2; decide +kernel
      have hl : raw23747step2Labels = labelEmbedding1 ∘ raw23747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23747step2 raw23747step2Labels raw23747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical23748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23748 raw23748Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw23748 raw23748Labels = mixedMoment B raw23748step0 raw23748step0Labels := by
      have hz : ∀ j, raw23748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23748step0 = (fun i j => raw23748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23748step0 raw23748; decide +kernel
      have hl : raw23748step0Labels = raw23748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23748 raw23748Labels permutation434 hz
    mixedMoment B raw23748step0 raw23748step0Labels = mixedMoment B raw23748step1 raw23748step1Labels := by
      have hz : ∀ j, raw23748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23748step1 = (fun i j => raw23748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23748step1 raw23748step0; decide +kernel
      have hl : raw23748step1Labels = raw23748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23748step0 raw23748step0Labels permutation80 hz
    mixedMoment B raw23748step1 raw23748step1Labels = mixedMoment B raw23748step2 raw23748step2Labels := by
      have ha : raw23748step2 = (fun i j => raw23748step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23748step2 raw23748step1; decide +kernel
      have hl : raw23748step2Labels = raw23748step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23748step1 raw23748step1Labels permutation9 permutation7
    mixedMoment B raw23748step2 raw23748step2Labels = mixedMoment B raw23748step3 raw23748step3Labels := by
      have ha : raw23748step3 = -raw23748step2 := by apply Matrix.ext; change ∀ i j, raw23748step3 i j = -(raw23748step2 i j); unfold raw23748step3 raw23748step2; decide +kernel
      have hl : raw23748step3Labels = raw23748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23748step3 raw23748step3Labels = mixedMoment B raw23748step4 raw23748step4Labels := by
      have ha : raw23748step4 = raw23748step3 := by apply Matrix.ext; unfold raw23748step4 raw23748step3; decide +kernel
      have hl : raw23748step3Labels = labelEmbedding1 ∘ raw23748step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23748step3 raw23748step3Labels raw23748step4Labels labelEmbedding1 hl
    _ = mixedMoment B node851 node851Labels := by rfl

theorem canonical23749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23749 raw23749Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw23749 raw23749Labels = mixedMoment B raw23749step0 raw23749step0Labels := by
      have hz : ∀ j, raw23749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23749step0 = (fun i j => raw23749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23749step0 raw23749; decide +kernel
      have hl : raw23749step0Labels = raw23749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23749 raw23749Labels permutation434 hz
    mixedMoment B raw23749step0 raw23749step0Labels = mixedMoment B raw23749step1 raw23749step1Labels := by
      have hz : ∀ j, raw23749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23749step1 = (fun i j => raw23749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23749step1 raw23749step0; decide +kernel
      have hl : raw23749step1Labels = raw23749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23749step0 raw23749step0Labels permutation80 hz
    mixedMoment B raw23749step1 raw23749step1Labels = mixedMoment B raw23749step2 raw23749step2Labels := by
      have ha : raw23749step2 = (fun i j => raw23749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23749step2 raw23749step1; decide +kernel
      have hl : raw23749step2Labels = raw23749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23749step1 raw23749step1Labels permutation9 permutation7
    mixedMoment B raw23749step2 raw23749step2Labels = mixedMoment B raw23749step3 raw23749step3Labels := by
      have ha : raw23749step3 = -raw23749step2 := by apply Matrix.ext; change ∀ i j, raw23749step3 i j = -(raw23749step2 i j); unfold raw23749step3 raw23749step2; decide +kernel
      have hl : raw23749step3Labels = raw23749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23749step3 raw23749step3Labels = mixedMoment B raw23749step4 raw23749step4Labels := by
      have ha : raw23749step4 = raw23749step3 := by apply Matrix.ext; unfold raw23749step4 raw23749step3; decide +kernel
      have hl : raw23749step3Labels = labelEmbedding1 ∘ raw23749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23749step3 raw23749step3Labels raw23749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node685 node685Labels := by rfl

theorem canonical23750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23750 raw23750Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw23750 raw23750Labels = mixedMoment B raw23750step0 raw23750step0Labels := by
      have hz : ∀ j, raw23750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23750step0 = (fun i j => raw23750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23750step0 raw23750; decide +kernel
      have hl : raw23750step0Labels = raw23750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23750 raw23750Labels permutation434 hz
    mixedMoment B raw23750step0 raw23750step0Labels = mixedMoment B raw23750step1 raw23750step1Labels := by
      have hz : ∀ j, raw23750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23750step1 = (fun i j => raw23750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23750step1 raw23750step0; decide +kernel
      have hl : raw23750step1Labels = raw23750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23750step0 raw23750step0Labels permutation80 hz
    mixedMoment B raw23750step1 raw23750step1Labels = mixedMoment B raw23750step2 raw23750step2Labels := by
      have ha : raw23750step2 = (fun i j => raw23750step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23750step2 raw23750step1; decide +kernel
      have hl : raw23750step2Labels = raw23750step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23750step1 raw23750step1Labels permutation9 permutation7
    mixedMoment B raw23750step2 raw23750step2Labels = mixedMoment B raw23750step3 raw23750step3Labels := by
      have ha : raw23750step3 = -raw23750step2 := by apply Matrix.ext; change ∀ i j, raw23750step3 i j = -(raw23750step2 i j); unfold raw23750step3 raw23750step2; decide +kernel
      have hl : raw23750step3Labels = raw23750step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23750step3 raw23750step3Labels = mixedMoment B raw23750step4 raw23750step4Labels := by
      have ha : raw23750step4 = raw23750step3 := by apply Matrix.ext; unfold raw23750step4 raw23750step3; decide +kernel
      have hl : raw23750step3Labels = labelEmbedding1 ∘ raw23750step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23750step3 raw23750step3Labels raw23750step4Labels labelEmbedding1 hl
    _ = mixedMoment B node844 node844Labels := by rfl

theorem canonical23751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23751 raw23751Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw23751 raw23751Labels = mixedMoment B raw23751step0 raw23751step0Labels := by
      have hz : ∀ j, raw23751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23751step0 = (fun i j => raw23751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23751step0 raw23751; decide +kernel
      have hl : raw23751step0Labels = raw23751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23751 raw23751Labels permutation434 hz
    mixedMoment B raw23751step0 raw23751step0Labels = mixedMoment B raw23751step1 raw23751step1Labels := by
      have ha : raw23751step1 = (fun i j => raw23751step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23751step1 raw23751step0; decide +kernel
      have hl : raw23751step1Labels = raw23751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23751step0 raw23751step0Labels permutation39 permutation7
    mixedMoment B raw23751step1 raw23751step1Labels = mixedMoment B raw23751step2 raw23751step2Labels := by
      have ha : raw23751step2 = -raw23751step1 := by apply Matrix.ext; change ∀ i j, raw23751step2 i j = -(raw23751step1 i j); unfold raw23751step2 raw23751step1; decide +kernel
      have hl : raw23751step2Labels = raw23751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23751step2 raw23751step2Labels = mixedMoment B raw23751step3 raw23751step3Labels := by
      have ha : raw23751step3 = raw23751step2 := by apply Matrix.ext; unfold raw23751step3 raw23751step2; decide +kernel
      have hl : raw23751step2Labels = labelEmbedding1 ∘ raw23751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23751step2 raw23751step2Labels raw23751step3Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

theorem canonical23752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23752 raw23752Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw23752 raw23752Labels = mixedMoment B raw23752step0 raw23752step0Labels := by
      have hz : ∀ j, raw23752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23752step0 = (fun i j => raw23752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23752step0 raw23752; decide +kernel
      have hl : raw23752step0Labels = raw23752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23752 raw23752Labels permutation346 hz
    mixedMoment B raw23752step0 raw23752step0Labels = mixedMoment B raw23752step1 raw23752step1Labels := by
      have ha : raw23752step1 = (fun i j => raw23752step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23752step1 raw23752step0; decide +kernel
      have hl : raw23752step1Labels = raw23752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23752step0 raw23752step0Labels permutation39 permutation7
    mixedMoment B raw23752step1 raw23752step1Labels = mixedMoment B raw23752step2 raw23752step2Labels := by
      have ha : raw23752step2 = -raw23752step1 := by apply Matrix.ext; change ∀ i j, raw23752step2 i j = -(raw23752step1 i j); unfold raw23752step2 raw23752step1; decide +kernel
      have hl : raw23752step2Labels = raw23752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23752step2 raw23752step2Labels = mixedMoment B raw23752step3 raw23752step3Labels := by
      have ha : raw23752step3 = raw23752step2 := by apply Matrix.ext; unfold raw23752step3 raw23752step2; decide +kernel
      have hl : raw23752step2Labels = labelEmbedding1 ∘ raw23752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23752step2 raw23752step2Labels raw23752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

theorem canonical23753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23753 raw23753Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw23753 raw23753Labels = mixedMoment B raw23753step0 raw23753step0Labels := by
      have hz : ∀ j, raw23753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23753step0 = (fun i j => raw23753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23753step0 raw23753; decide +kernel
      have hl : raw23753step0Labels = raw23753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23753 raw23753Labels permutation434 hz
    mixedMoment B raw23753step0 raw23753step0Labels = mixedMoment B raw23753step1 raw23753step1Labels := by
      have hz : ∀ j, raw23753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23753step1 = (fun i j => raw23753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23753step1 raw23753step0; decide +kernel
      have hl : raw23753step1Labels = raw23753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23753step0 raw23753step0Labels permutation80 hz
    mixedMoment B raw23753step1 raw23753step1Labels = mixedMoment B raw23753step2 raw23753step2Labels := by
      have ha : raw23753step2 = (fun i j => raw23753step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23753step2 raw23753step1; decide +kernel
      have hl : raw23753step2Labels = raw23753step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23753step1 raw23753step1Labels permutation9 permutation7
    mixedMoment B raw23753step2 raw23753step2Labels = mixedMoment B raw23753step3 raw23753step3Labels := by
      have ha : raw23753step3 = -raw23753step2 := by apply Matrix.ext; change ∀ i j, raw23753step3 i j = -(raw23753step2 i j); unfold raw23753step3 raw23753step2; decide +kernel
      have hl : raw23753step3Labels = raw23753step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23753step3 raw23753step3Labels = mixedMoment B raw23753step4 raw23753step4Labels := by
      have ha : raw23753step4 = raw23753step3 := by apply Matrix.ext; unfold raw23753step4 raw23753step3; decide +kernel
      have hl : raw23753step3Labels = labelEmbedding1 ∘ raw23753step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23753step3 raw23753step3Labels raw23753step4Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

theorem canonical23754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23754 raw23754Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw23754 raw23754Labels = mixedMoment B raw23754step0 raw23754step0Labels := by
      have hz : ∀ j, raw23754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23754step0 = (fun i j => raw23754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23754step0 raw23754; decide +kernel
      have hl : raw23754step0Labels = raw23754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23754 raw23754Labels permutation434 hz
    mixedMoment B raw23754step0 raw23754step0Labels = mixedMoment B raw23754step1 raw23754step1Labels := by
      have hz : ∀ j, raw23754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23754step1 = (fun i j => raw23754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23754step1 raw23754step0; decide +kernel
      have hl : raw23754step1Labels = raw23754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23754step0 raw23754step0Labels permutation80 hz
    mixedMoment B raw23754step1 raw23754step1Labels = mixedMoment B raw23754step2 raw23754step2Labels := by
      have ha : raw23754step2 = (fun i j => raw23754step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23754step2 raw23754step1; decide +kernel
      have hl : raw23754step2Labels = raw23754step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23754step1 raw23754step1Labels permutation9 permutation2
    _ = mixedMoment B node1653 node1653Labels := by rfl

theorem canonical23755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23755 raw23755Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23755 raw23755Labels = mixedMoment B raw23755step0 raw23755step0Labels := by
      have hz : ∀ j, raw23755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23755step0 = (fun i j => raw23755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23755step0 raw23755; decide +kernel
      have hl : raw23755step0Labels = raw23755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23755 raw23755Labels permutation434 hz
    mixedMoment B raw23755step0 raw23755step0Labels = mixedMoment B raw23755step1 raw23755step1Labels := by
      have ha : raw23755step1 = (fun i j => raw23755step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23755step1 raw23755step0; decide +kernel
      have hl : raw23755step1Labels = raw23755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23755step0 raw23755step0Labels permutation39 permutation2
    _ = mixedMoment B node1605 node1605Labels := by rfl

theorem canonical23756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23756 raw23756Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23756 raw23756Labels = mixedMoment B raw23756step0 raw23756step0Labels := by
      have hz : ∀ j, raw23756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23756step0 = (fun i j => raw23756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23756step0 raw23756; decide +kernel
      have hl : raw23756step0Labels = raw23756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23756 raw23756Labels permutation346 hz
    mixedMoment B raw23756step0 raw23756step0Labels = mixedMoment B raw23756step1 raw23756step1Labels := by
      have ha : raw23756step1 = (fun i j => raw23756step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23756step1 raw23756step0; decide +kernel
      have hl : raw23756step1Labels = raw23756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23756step0 raw23756step0Labels permutation39 permutation2
    _ = mixedMoment B node1605 node1605Labels := by rfl

theorem canonical23757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23757 raw23757Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23757 raw23757Labels = mixedMoment B raw23757step0 raw23757step0Labels := by
      have hz : ∀ j, raw23757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23757step0 = (fun i j => raw23757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23757step0 raw23757; decide +kernel
      have hl : raw23757step0Labels = raw23757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23757 raw23757Labels permutation434 hz
    mixedMoment B raw23757step0 raw23757step0Labels = mixedMoment B raw23757step1 raw23757step1Labels := by
      have hz : ∀ j, raw23757step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23757step1 = (fun i j => raw23757step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23757step1 raw23757step0; decide +kernel
      have hl : raw23757step1Labels = raw23757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23757step0 raw23757step0Labels permutation80 hz
    mixedMoment B raw23757step1 raw23757step1Labels = mixedMoment B raw23757step2 raw23757step2Labels := by
      have ha : raw23757step2 = (fun i j => raw23757step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23757step2 raw23757step1; decide +kernel
      have hl : raw23757step2Labels = raw23757step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23757step1 raw23757step1Labels permutation9 permutation2
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical23758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23758 raw23758Labels = mixedMoment B node561 node561Labels := by
  calc
    mixedMoment B raw23758 raw23758Labels = mixedMoment B raw23758step0 raw23758step0Labels := by
      have hz : ∀ j, raw23758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23758step0 = (fun i j => raw23758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23758step0 raw23758; decide +kernel
      have hl : raw23758step0Labels = raw23758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23758 raw23758Labels permutation434 hz
    mixedMoment B raw23758step0 raw23758step0Labels = mixedMoment B raw23758step1 raw23758step1Labels := by
      have hz : ∀ j, raw23758step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23758step1 = (fun i j => raw23758step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23758step1 raw23758step0; decide +kernel
      have hl : raw23758step1Labels = raw23758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23758step0 raw23758step0Labels permutation80 hz
    mixedMoment B raw23758step1 raw23758step1Labels = mixedMoment B raw23758step2 raw23758step2Labels := by
      have ha : raw23758step2 = (fun i j => raw23758step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23758step2 raw23758step1; decide +kernel
      have hl : raw23758step2Labels = raw23758step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23758step1 raw23758step1Labels permutation9 permutation2
    _ = mixedMoment B node561 node561Labels := by rfl

theorem canonical23759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23759 raw23759Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw23759 raw23759Labels = mixedMoment B raw23759step0 raw23759step0Labels := by
      have hz : ∀ j, raw23759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23759step0 = (fun i j => raw23759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23759step0 raw23759; decide +kernel
      have hl : raw23759step0Labels = raw23759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23759 raw23759Labels permutation434 hz
    mixedMoment B raw23759step0 raw23759step0Labels = mixedMoment B raw23759step1 raw23759step1Labels := by
      have ha : raw23759step1 = (fun i j => raw23759step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23759step1 raw23759step0; decide +kernel
      have hl : raw23759step1Labels = raw23759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23759step0 raw23759step0Labels permutation33 permutation2
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical23760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23760 raw23760Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw23760 raw23760Labels = mixedMoment B raw23760step0 raw23760step0Labels := by
      have hz : ∀ j, raw23760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23760step0 = (fun i j => raw23760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23760step0 raw23760; decide +kernel
      have hl : raw23760step0Labels = raw23760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23760 raw23760Labels permutation346 hz
    mixedMoment B raw23760step0 raw23760step0Labels = mixedMoment B raw23760step1 raw23760step1Labels := by
      have ha : raw23760step1 = (fun i j => raw23760step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23760step1 raw23760step0; decide +kernel
      have hl : raw23760step1Labels = raw23760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23760step0 raw23760step0Labels permutation33 permutation2
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical23761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23761 raw23761Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw23761 raw23761Labels = mixedMoment B raw23761step0 raw23761step0Labels := by
      have hz : ∀ j, raw23761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23761step0 = (fun i j => raw23761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23761step0 raw23761; decide +kernel
      have hl : raw23761step0Labels = raw23761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23761 raw23761Labels permutation434 hz
    mixedMoment B raw23761step0 raw23761step0Labels = mixedMoment B raw23761step1 raw23761step1Labels := by
      have hz : ∀ j, raw23761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23761step1 = (fun i j => raw23761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23761step1 raw23761step0; decide +kernel
      have hl : raw23761step1Labels = raw23761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23761step0 raw23761step0Labels permutation80 hz
    mixedMoment B raw23761step1 raw23761step1Labels = mixedMoment B raw23761step2 raw23761step2Labels := by
      have ha : raw23761step2 = (fun i j => raw23761step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23761step2 raw23761step1; decide +kernel
      have hl : raw23761step2Labels = raw23761step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23761step1 raw23761step1Labels permutation9 permutation2
    _ = mixedMoment B node547 node547Labels := by rfl

theorem canonical23762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23762 raw23762Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw23762 raw23762Labels = mixedMoment B raw23762step0 raw23762step0Labels := by
      have hz : ∀ j, raw23762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23762step0 = (fun i j => raw23762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23762step0 raw23762; decide +kernel
      have hl : raw23762step0Labels = raw23762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23762 raw23762Labels permutation434 hz
    mixedMoment B raw23762step0 raw23762step0Labels = mixedMoment B raw23762step1 raw23762step1Labels := by
      have ha : raw23762step1 = (fun i j => raw23762step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23762step1 raw23762step0; decide +kernel
      have hl : raw23762step1Labels = raw23762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23762step0 raw23762step0Labels permutation33 permutation2
    _ = mixedMoment B node734 node734Labels := by rfl

theorem canonical23763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23763 raw23763Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw23763 raw23763Labels = mixedMoment B raw23763step0 raw23763step0Labels := by
      have hz : ∀ j, raw23763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23763step0 = (fun i j => raw23763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23763step0 raw23763; decide +kernel
      have hl : raw23763step0Labels = raw23763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23763 raw23763Labels permutation346 hz
    mixedMoment B raw23763step0 raw23763step0Labels = mixedMoment B raw23763step1 raw23763step1Labels := by
      have ha : raw23763step1 = (fun i j => raw23763step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23763step1 raw23763step0; decide +kernel
      have hl : raw23763step1Labels = raw23763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23763step0 raw23763step0Labels permutation33 permutation2
    _ = mixedMoment B node734 node734Labels := by rfl

theorem canonical23764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23764 raw23764Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw23764 raw23764Labels = mixedMoment B raw23764step0 raw23764step0Labels := by
      have hz : ∀ j, raw23764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23764step0 = (fun i j => raw23764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23764step0 raw23764; decide +kernel
      have hl : raw23764step0Labels = raw23764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23764 raw23764Labels permutation434 hz
    mixedMoment B raw23764step0 raw23764step0Labels = mixedMoment B raw23764step1 raw23764step1Labels := by
      have hz : ∀ j, raw23764step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23764step1 = (fun i j => raw23764step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23764step1 raw23764step0; decide +kernel
      have hl : raw23764step1Labels = raw23764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23764step0 raw23764step0Labels permutation80 hz
    mixedMoment B raw23764step1 raw23764step1Labels = mixedMoment B raw23764step2 raw23764step2Labels := by
      have ha : raw23764step2 = (fun i j => raw23764step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23764step2 raw23764step1; decide +kernel
      have hl : raw23764step2Labels = raw23764step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23764step1 raw23764step1Labels permutation9 permutation2
    _ = mixedMoment B node742 node742Labels := by rfl

theorem canonical23777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23777 raw23777Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23777 raw23777Labels = mixedMoment B raw23777step0 raw23777step0Labels := by
      have hz : ∀ j, raw23777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23777step0 = (fun i j => raw23777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23777step0 raw23777; decide +kernel
      have hl : raw23777step0Labels = raw23777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23777 raw23777Labels permutation434 hz
    mixedMoment B raw23777step0 raw23777step0Labels = mixedMoment B raw23777step1 raw23777step1Labels := by
      have hz : ∀ j, raw23777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23777step1 = (fun i j => raw23777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23777step1 raw23777step0; decide +kernel
      have hl : raw23777step1Labels = raw23777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23777step0 raw23777step0Labels permutation80 hz
    mixedMoment B raw23777step1 raw23777step1Labels = mixedMoment B raw23777step2 raw23777step2Labels := by
      have hz : ∀ i, raw23777step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23777step2 = (fun i j => raw23777step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23777step2 raw23777step1; decide +kernel
      have hl : raw23777step2Labels = (fun j => raw23777step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23777step1 raw23777step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

theorem canonical23778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23778 raw23778Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23778 raw23778Labels = mixedMoment B raw23778step0 raw23778step0Labels := by
      have hz : ∀ j, raw23778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23778step0 = (fun i j => raw23778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23778step0 raw23778; decide +kernel
      have hl : raw23778step0Labels = raw23778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23778 raw23778Labels permutation434 hz
    mixedMoment B raw23778step0 raw23778step0Labels = mixedMoment B raw23778step1 raw23778step1Labels := by
      have hz : ∀ i, raw23778step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23778step1 = (fun i j => raw23778step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23778step1 raw23778step0; decide +kernel
      have hl : raw23778step1Labels = (fun j => raw23778step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23778step0 raw23778step0Labels permutation6 hz
    mixedMoment B raw23778step1 raw23778step1Labels = mixedMoment B raw23778step2 raw23778step2Labels := by
      have ha : raw23778step2 = (fun i j => raw23778step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23778step2 raw23778step1; decide +kernel
      have hl : raw23778step2Labels = raw23778step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23778step1 raw23778step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23779 raw23779Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23779 raw23779Labels = mixedMoment B raw23779step0 raw23779step0Labels := by
      have hz : ∀ j, raw23779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23779step0 = (fun i j => raw23779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23779step0 raw23779; decide +kernel
      have hl : raw23779step0Labels = raw23779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23779 raw23779Labels permutation346 hz
    mixedMoment B raw23779step0 raw23779step0Labels = mixedMoment B raw23779step1 raw23779step1Labels := by
      have hz : ∀ i, raw23779step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23779step1 = (fun i j => raw23779step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23779step1 raw23779step0; decide +kernel
      have hl : raw23779step1Labels = (fun j => raw23779step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23779step0 raw23779step0Labels permutation6 hz
    mixedMoment B raw23779step1 raw23779step1Labels = mixedMoment B raw23779step2 raw23779step2Labels := by
      have ha : raw23779step2 = (fun i j => raw23779step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23779step2 raw23779step1; decide +kernel
      have hl : raw23779step2Labels = raw23779step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23779step1 raw23779step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23780 raw23780Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23780 raw23780Labels = mixedMoment B raw23780step0 raw23780step0Labels := by
      have hz : ∀ j, raw23780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23780step0 = (fun i j => raw23780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23780step0 raw23780; decide +kernel
      have hl : raw23780step0Labels = raw23780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23780 raw23780Labels permutation434 hz
    mixedMoment B raw23780step0 raw23780step0Labels = mixedMoment B raw23780step1 raw23780step1Labels := by
      have hz : ∀ j, raw23780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23780step1 = (fun i j => raw23780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23780step1 raw23780step0; decide +kernel
      have hl : raw23780step1Labels = raw23780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23780step0 raw23780step0Labels permutation80 hz
    mixedMoment B raw23780step1 raw23780step1Labels = mixedMoment B raw23780step2 raw23780step2Labels := by
      have hz : ∀ i, raw23780step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23780step2 = (fun i j => raw23780step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23780step2 raw23780step1; decide +kernel
      have hl : raw23780step2Labels = (fun j => raw23780step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23780step1 raw23780step1Labels permutation6 hz
    mixedMoment B raw23780step2 raw23780step2Labels = mixedMoment B raw23780step3 raw23780step3Labels := by
      have ha : raw23780step3 = (fun i j => raw23780step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23780step3 raw23780step2; decide +kernel
      have hl : raw23780step3Labels = raw23780step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23780step2 raw23780step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23781 raw23781Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23781 raw23781Labels = mixedMoment B raw23781step0 raw23781step0Labels := by
      have hz : ∀ j, raw23781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23781step0 = (fun i j => raw23781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23781step0 raw23781; decide +kernel
      have hl : raw23781step0Labels = raw23781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23781 raw23781Labels permutation434 hz
    mixedMoment B raw23781step0 raw23781step0Labels = mixedMoment B raw23781step1 raw23781step1Labels := by
      have hz : ∀ j, raw23781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23781step1 = (fun i j => raw23781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23781step1 raw23781step0; decide +kernel
      have hl : raw23781step1Labels = raw23781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23781step0 raw23781step0Labels permutation56 hz
    mixedMoment B raw23781step1 raw23781step1Labels = mixedMoment B raw23781step2 raw23781step2Labels := by
      have hz : ∀ i, raw23781step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23781step2 = (fun i j => raw23781step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23781step2 raw23781step1; decide +kernel
      have hl : raw23781step2Labels = (fun j => raw23781step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23781step1 raw23781step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

theorem canonical23782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23782 raw23782Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23782 raw23782Labels = mixedMoment B raw23782step0 raw23782step0Labels := by
      have hz : ∀ j, raw23782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23782step0 = (fun i j => raw23782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23782step0 raw23782; decide +kernel
      have hl : raw23782step0Labels = raw23782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23782 raw23782Labels permutation434 hz
    mixedMoment B raw23782step0 raw23782step0Labels = mixedMoment B raw23782step1 raw23782step1Labels := by
      have hz : ∀ i, raw23782step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23782step1 = (fun i j => raw23782step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23782step1 raw23782step0; decide +kernel
      have hl : raw23782step1Labels = (fun j => raw23782step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23782step0 raw23782step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23783 raw23783Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23783 raw23783Labels = mixedMoment B raw23783step0 raw23783step0Labels := by
      have hz : ∀ j, raw23783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23783step0 = (fun i j => raw23783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23783step0 raw23783; decide +kernel
      have hl : raw23783step0Labels = raw23783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23783 raw23783Labels permutation265 hz
    mixedMoment B raw23783step0 raw23783step0Labels = mixedMoment B raw23783step1 raw23783step1Labels := by
      have hz : ∀ i, raw23783step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23783step1 = (fun i j => raw23783step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23783step1 raw23783step0; decide +kernel
      have hl : raw23783step1Labels = (fun j => raw23783step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23783step0 raw23783step0Labels permutation6 hz
    mixedMoment B raw23783step1 raw23783step1Labels = mixedMoment B raw23783step2 raw23783step2Labels := by
      have ha : raw23783step2 = (fun i j => raw23783step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23783step2 raw23783step1; decide +kernel
      have hl : raw23783step2Labels = raw23783step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23783step1 raw23783step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23784 raw23784Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23784 raw23784Labels = mixedMoment B raw23784step0 raw23784step0Labels := by
      have hz : ∀ j, raw23784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23784step0 = (fun i j => raw23784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23784step0 raw23784; decide +kernel
      have hl : raw23784step0Labels = raw23784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784 raw23784Labels permutation434 hz
    mixedMoment B raw23784step0 raw23784step0Labels = mixedMoment B raw23784step1 raw23784step1Labels := by
      have hz : ∀ j, raw23784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23784step1 = (fun i j => raw23784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23784step1 raw23784step0; decide +kernel
      have hl : raw23784step1Labels = raw23784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784step0 raw23784step0Labels permutation56 hz
    mixedMoment B raw23784step1 raw23784step1Labels = mixedMoment B raw23784step2 raw23784step2Labels := by
      have hz : ∀ i, raw23784step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23784step2 = (fun i j => raw23784step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23784step2 raw23784step1; decide +kernel
      have hl : raw23784step2Labels = (fun j => raw23784step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23784step1 raw23784step1Labels permutation6 hz
    mixedMoment B raw23784step2 raw23784step2Labels = mixedMoment B raw23784step3 raw23784step3Labels := by
      have ha : raw23784step3 = (fun i j => raw23784step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23784step3 raw23784step2; decide +kernel
      have hl : raw23784step3Labels = raw23784step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23784step2 raw23784step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23785 raw23785Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23785 raw23785Labels = mixedMoment B raw23785step0 raw23785step0Labels := by
      have hz : ∀ j, raw23785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23785step0 = (fun i j => raw23785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23785step0 raw23785; decide +kernel
      have hl : raw23785step0Labels = raw23785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23785 raw23785Labels permutation346 hz
    mixedMoment B raw23785step0 raw23785step0Labels = mixedMoment B raw23785step1 raw23785step1Labels := by
      have hz : ∀ j, raw23785step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23785step1 = (fun i j => raw23785step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23785step1 raw23785step0; decide +kernel
      have hl : raw23785step1Labels = raw23785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23785step0 raw23785step0Labels permutation56 hz
    mixedMoment B raw23785step1 raw23785step1Labels = mixedMoment B raw23785step2 raw23785step2Labels := by
      have hz : ∀ i, raw23785step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23785step2 = (fun i j => raw23785step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23785step2 raw23785step1; decide +kernel
      have hl : raw23785step2Labels = (fun j => raw23785step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23785step1 raw23785step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

theorem canonical23786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23786 raw23786Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23786 raw23786Labels = mixedMoment B raw23786step0 raw23786step0Labels := by
      have hz : ∀ j, raw23786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23786step0 = (fun i j => raw23786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23786step0 raw23786; decide +kernel
      have hl : raw23786step0Labels = raw23786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23786 raw23786Labels permutation346 hz
    mixedMoment B raw23786step0 raw23786step0Labels = mixedMoment B raw23786step1 raw23786step1Labels := by
      have hz : ∀ i, raw23786step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23786step1 = (fun i j => raw23786step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23786step1 raw23786step0; decide +kernel
      have hl : raw23786step1Labels = (fun j => raw23786step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23786step0 raw23786step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23787 raw23787Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23787 raw23787Labels = mixedMoment B raw23787step0 raw23787step0Labels := by
      have hz : ∀ j, raw23787 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23787step0 = (fun i j => raw23787 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23787step0 raw23787; decide +kernel
      have hl : raw23787step0Labels = raw23787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23787 raw23787Labels permutation265 hz
    mixedMoment B raw23787step0 raw23787step0Labels = mixedMoment B raw23787step1 raw23787step1Labels := by
      have hz : ∀ i, raw23787step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23787step1 = (fun i j => raw23787step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23787step1 raw23787step0; decide +kernel
      have hl : raw23787step1Labels = (fun j => raw23787step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23787step0 raw23787step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical23788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23788 raw23788Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw23788 raw23788Labels = mixedMoment B raw23788step0 raw23788step0Labels := by
      have hz : ∀ j, raw23788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23788step0 = (fun i j => raw23788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23788step0 raw23788; decide +kernel
      have hl : raw23788step0Labels = raw23788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788 raw23788Labels permutation434 hz
    mixedMoment B raw23788step0 raw23788step0Labels = mixedMoment B raw23788step1 raw23788step1Labels := by
      have hz : ∀ j, raw23788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23788step1 = (fun i j => raw23788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23788step1 raw23788step0; decide +kernel
      have hl : raw23788step1Labels = raw23788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788step0 raw23788step0Labels permutation80 hz
    mixedMoment B raw23788step1 raw23788step1Labels = mixedMoment B raw23788step2 raw23788step2Labels := by
      have hz : ∀ j, raw23788step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23788step2 = (fun i j => raw23788step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23788step2 raw23788step1; decide +kernel
      have hl : raw23788step2Labels = raw23788step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788step1 raw23788step1Labels permutation14 hz
    mixedMoment B raw23788step2 raw23788step2Labels = mixedMoment B raw23788step3 raw23788step3Labels := by
      have hz : ∀ i, raw23788step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23788step3 = (fun i j => raw23788step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23788step3 raw23788step2; decide +kernel
      have hl : raw23788step3Labels = (fun j => raw23788step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23788step2 raw23788step2Labels permutation6 hz
    mixedMoment B raw23788step3 raw23788step3Labels = mixedMoment B raw23788step4 raw23788step4Labels := by
      have ha : raw23788step4 = (fun i j => raw23788step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23788step4 raw23788step3; decide +kernel
      have hl : raw23788step4Labels = raw23788step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23788step3 raw23788step3Labels permutation3 permutation0
    _ = mixedMoment B node4061 node4061Labels := by rfl

theorem canonical23789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23789 raw23789Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23789 raw23789Labels = mixedMoment B raw23789step0 raw23789step0Labels := by
      have hz : ∀ j, raw23789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23789step0 = (fun i j => raw23789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23789step0 raw23789; decide +kernel
      have hl : raw23789step0Labels = raw23789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789 raw23789Labels permutation434 hz
    mixedMoment B raw23789step0 raw23789step0Labels = mixedMoment B raw23789step1 raw23789step1Labels := by
      have hz : ∀ j, raw23789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23789step1 = (fun i j => raw23789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23789step1 raw23789step0; decide +kernel
      have hl : raw23789step1Labels = raw23789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789step0 raw23789step0Labels permutation80 hz
    mixedMoment B raw23789step1 raw23789step1Labels = mixedMoment B raw23789step2 raw23789step2Labels := by
      have hz : ∀ i, raw23789step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23789step2 = (fun i j => raw23789step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23789step2 raw23789step1; decide +kernel
      have hl : raw23789step2Labels = (fun j => raw23789step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23789step1 raw23789step1Labels permutation6 hz
    mixedMoment B raw23789step2 raw23789step2Labels = mixedMoment B raw23789step3 raw23789step3Labels := by
      have ha : raw23789step3 = (fun i j => raw23789step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23789step3 raw23789step2; decide +kernel
      have hl : raw23789step3Labels = raw23789step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23789step2 raw23789step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical23790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23790 raw23790Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23790 raw23790Labels = mixedMoment B raw23790step0 raw23790step0Labels := by
      have hz : ∀ j, raw23790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23790step0 = (fun i j => raw23790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23790step0 raw23790; decide +kernel
      have hl : raw23790step0Labels = raw23790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23790 raw23790Labels permutation434 hz
    mixedMoment B raw23790step0 raw23790step0Labels = mixedMoment B raw23790step1 raw23790step1Labels := by
      have hz : ∀ j, raw23790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23790step1 = (fun i j => raw23790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23790step1 raw23790step0; decide +kernel
      have hl : raw23790step1Labels = raw23790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23790step0 raw23790step0Labels permutation56 hz
    mixedMoment B raw23790step1 raw23790step1Labels = mixedMoment B raw23790step2 raw23790step2Labels := by
      have hz : ∀ i, raw23790step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23790step2 = (fun i j => raw23790step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23790step2 raw23790step1; decide +kernel
      have hl : raw23790step2Labels = (fun j => raw23790step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23790step1 raw23790step1Labels permutation6 hz
    mixedMoment B raw23790step2 raw23790step2Labels = mixedMoment B raw23790step3 raw23790step3Labels := by
      have ha : raw23790step3 = (fun i j => raw23790step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23790step3 raw23790step2; decide +kernel
      have hl : raw23790step3Labels = raw23790step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23790step2 raw23790step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical23791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23791 raw23791Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23791 raw23791Labels = mixedMoment B raw23791step0 raw23791step0Labels := by
      have hz : ∀ j, raw23791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23791step0 = (fun i j => raw23791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23791step0 raw23791; decide +kernel
      have hl : raw23791step0Labels = raw23791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23791 raw23791Labels permutation346 hz
    mixedMoment B raw23791step0 raw23791step0Labels = mixedMoment B raw23791step1 raw23791step1Labels := by
      have hz : ∀ j, raw23791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23791step1 = (fun i j => raw23791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23791step1 raw23791step0; decide +kernel
      have hl : raw23791step1Labels = raw23791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23791step0 raw23791step0Labels permutation56 hz
    mixedMoment B raw23791step1 raw23791step1Labels = mixedMoment B raw23791step2 raw23791step2Labels := by
      have hz : ∀ i, raw23791step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23791step2 = (fun i j => raw23791step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23791step2 raw23791step1; decide +kernel
      have hl : raw23791step2Labels = (fun j => raw23791step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23791step1 raw23791step1Labels permutation6 hz
    mixedMoment B raw23791step2 raw23791step2Labels = mixedMoment B raw23791step3 raw23791step3Labels := by
      have ha : raw23791step3 = (fun i j => raw23791step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23791step3 raw23791step2; decide +kernel
      have hl : raw23791step3Labels = raw23791step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23791step2 raw23791step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical23792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23792 raw23792Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw23792 raw23792Labels = mixedMoment B raw23792step0 raw23792step0Labels := by
      have hz : ∀ j, raw23792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23792step0 = (fun i j => raw23792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23792step0 raw23792; decide +kernel
      have hl : raw23792step0Labels = raw23792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792 raw23792Labels permutation434 hz
    mixedMoment B raw23792step0 raw23792step0Labels = mixedMoment B raw23792step1 raw23792step1Labels := by
      have hz : ∀ j, raw23792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23792step1 = (fun i j => raw23792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23792step1 raw23792step0; decide +kernel
      have hl : raw23792step1Labels = raw23792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792step0 raw23792step0Labels permutation80 hz
    mixedMoment B raw23792step1 raw23792step1Labels = mixedMoment B raw23792step2 raw23792step2Labels := by
      have hz : ∀ j, raw23792step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23792step2 = (fun i j => raw23792step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23792step2 raw23792step1; decide +kernel
      have hl : raw23792step2Labels = raw23792step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792step1 raw23792step1Labels permutation14 hz
    mixedMoment B raw23792step2 raw23792step2Labels = mixedMoment B raw23792step3 raw23792step3Labels := by
      have hz : ∀ i, raw23792step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23792step3 = (fun i j => raw23792step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23792step3 raw23792step2; decide +kernel
      have hl : raw23792step3Labels = (fun j => raw23792step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23792step2 raw23792step2Labels permutation6 hz
    mixedMoment B raw23792step3 raw23792step3Labels = mixedMoment B raw23792step4 raw23792step4Labels := by
      have ha : raw23792step4 = (fun i j => raw23792step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23792step4 raw23792step3; decide +kernel
      have hl : raw23792step4Labels = raw23792step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23792step3 raw23792step3Labels permutation3 permutation0
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical23793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23793 raw23793Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23793 raw23793Labels = mixedMoment B raw23793step0 raw23793step0Labels := by
      have hz : ∀ j, raw23793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23793step0 = (fun i j => raw23793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23793step0 raw23793; decide +kernel
      have hl : raw23793step0Labels = raw23793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23793 raw23793Labels permutation346 hz
    mixedMoment B raw23793step0 raw23793step0Labels = mixedMoment B raw23793step1 raw23793step1Labels := by
      have hz : ∀ j, raw23793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23793step1 = (fun i j => raw23793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23793step1 raw23793step0; decide +kernel
      have hl : raw23793step1Labels = raw23793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23793step0 raw23793step0Labels permutation56 hz
    mixedMoment B raw23793step1 raw23793step1Labels = mixedMoment B raw23793step2 raw23793step2Labels := by
      have ha : raw23793step2 = (fun i j => raw23793step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23793step2 raw23793step1; decide +kernel
      have hl : raw23793step2Labels = raw23793step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23793step1 raw23793step1Labels permutation9 permutation4
    mixedMoment B raw23793step2 raw23793step2Labels = mixedMoment B raw23793step3 raw23793step3Labels := by
      have ha : raw23793step3 = -raw23793step2 := by apply Matrix.ext; change ∀ i j, raw23793step3 i j = -(raw23793step2 i j); unfold raw23793step3 raw23793step2; decide +kernel
      have hl : raw23793step3Labels = raw23793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical23794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23794 raw23794Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw23794 raw23794Labels = mixedMoment B raw23794step0 raw23794step0Labels := by
      have hz : ∀ j, raw23794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23794step0 = (fun i j => raw23794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23794step0 raw23794; decide +kernel
      have hl : raw23794step0Labels = raw23794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23794 raw23794Labels permutation346 hz
    mixedMoment B raw23794step0 raw23794step0Labels = mixedMoment B raw23794step1 raw23794step1Labels := by
      have ha : raw23794step1 = (fun i j => raw23794step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23794step1 raw23794step0; decide +kernel
      have hl : raw23794step1Labels = raw23794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23794step0 raw23794step0Labels permutation127 permutation4
    _ = mixedMoment B node3022 node3022Labels := by rfl

theorem canonical23795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23795 raw23795Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw23795 raw23795Labels = mixedMoment B raw23795step0 raw23795step0Labels := by
      have hz : ∀ j, raw23795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23795step0 = (fun i j => raw23795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23795step0 raw23795; decide +kernel
      have hl : raw23795step0Labels = raw23795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23795 raw23795Labels permutation265 hz
    mixedMoment B raw23795step0 raw23795step0Labels = mixedMoment B raw23795step1 raw23795step1Labels := by
      have ha : raw23795step1 = (fun i j => raw23795step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23795step1 raw23795step0; decide +kernel
      have hl : raw23795step1Labels = raw23795step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23795step0 raw23795step0Labels permutation127 permutation4
    _ = mixedMoment B node3022 node3022Labels := by rfl

theorem canonical23796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23796 raw23796Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw23796 raw23796Labels = mixedMoment B raw23796step0 raw23796step0Labels := by
      have hz : ∀ j, raw23796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23796step0 = (fun i j => raw23796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23796step0 raw23796; decide +kernel
      have hl : raw23796step0Labels = raw23796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23796 raw23796Labels permutation346 hz
    mixedMoment B raw23796step0 raw23796step0Labels = mixedMoment B raw23796step1 raw23796step1Labels := by
      have hz : ∀ j, raw23796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23796step1 = (fun i j => raw23796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23796step1 raw23796step0; decide +kernel
      have hl : raw23796step1Labels = raw23796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23796step0 raw23796step0Labels permutation56 hz
    mixedMoment B raw23796step1 raw23796step1Labels = mixedMoment B raw23796step2 raw23796step2Labels := by
      have ha : raw23796step2 = (fun i j => raw23796step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23796step2 raw23796step1; decide +kernel
      have hl : raw23796step2Labels = raw23796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23796step1 raw23796step1Labels permutation25 permutation4
    _ = mixedMoment B node3049 node3049Labels := by rfl

theorem canonical23797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23797 raw23797Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw23797 raw23797Labels = mixedMoment B raw23797step0 raw23797step0Labels := by
      have hz : ∀ j, raw23797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23797step0 = (fun i j => raw23797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23797step0 raw23797; decide +kernel
      have hl : raw23797step0Labels = raw23797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797 raw23797Labels permutation346 hz
    mixedMoment B raw23797step0 raw23797step0Labels = mixedMoment B raw23797step1 raw23797step1Labels := by
      have hz : ∀ j, raw23797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23797step1 = (fun i j => raw23797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23797step1 raw23797step0; decide +kernel
      have hl : raw23797step1Labels = raw23797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797step0 raw23797step0Labels permutation56 hz
    mixedMoment B raw23797step1 raw23797step1Labels = mixedMoment B raw23797step2 raw23797step2Labels := by
      have ha : raw23797step2 = (fun i j => raw23797step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23797step2 raw23797step1; decide +kernel
      have hl : raw23797step2Labels = raw23797step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23797step1 raw23797step1Labels permutation10 permutation2
    mixedMoment B raw23797step2 raw23797step2Labels = mixedMoment B raw23797step3 raw23797step3Labels := by
      have ha : raw23797step3 = -raw23797step2 := by apply Matrix.ext; change ∀ i j, raw23797step3 i j = -(raw23797step2 i j); unfold raw23797step3 raw23797step2; decide +kernel
      have hl : raw23797step3Labels = raw23797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical23798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23798 raw23798Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw23798 raw23798Labels = mixedMoment B raw23798step0 raw23798step0Labels := by
      have hz : ∀ j, raw23798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23798step0 = (fun i j => raw23798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23798step0 raw23798; decide +kernel
      have hl : raw23798step0Labels = raw23798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23798 raw23798Labels permutation346 hz
    mixedMoment B raw23798step0 raw23798step0Labels = mixedMoment B raw23798step1 raw23798step1Labels := by
      have hz : ∀ j, raw23798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23798step1 = (fun i j => raw23798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23798step1 raw23798step0; decide +kernel
      have hl : raw23798step1Labels = raw23798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23798step0 raw23798step0Labels permutation56 hz
    mixedMoment B raw23798step1 raw23798step1Labels = mixedMoment B raw23798step2 raw23798step2Labels := by
      have ha : raw23798step2 = (fun i j => raw23798step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23798step2 raw23798step1; decide +kernel
      have hl : raw23798step2Labels = raw23798step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23798step1 raw23798step1Labels permutation29 permutation2
    _ = mixedMoment B node2521 node2521Labels := by rfl

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23800 raw23800Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23800 raw23800Labels = mixedMoment B raw23800step0 raw23800step0Labels := by
      have hz : ∀ j, raw23800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23800step0 = (fun i j => raw23800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23800step0 raw23800; decide +kernel
      have hl : raw23800step0Labels = raw23800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23800 raw23800Labels permutation346 hz
    mixedMoment B raw23800step0 raw23800step0Labels = mixedMoment B raw23800step1 raw23800step1Labels := by
      have ha : raw23800step1 = (fun i j => raw23800step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23800step1 raw23800step0; decide +kernel
      have hl : raw23800step1Labels = raw23800step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23800step0 raw23800step0Labels permutation42 permutation4
    mixedMoment B raw23800step1 raw23800step1Labels = mixedMoment B raw23800step2 raw23800step2Labels := by
      have ha : raw23800step2 = -raw23800step1 := by apply Matrix.ext; change ∀ i j, raw23800step2 i j = -(raw23800step1 i j); unfold raw23800step2 raw23800step1; decide +kernel
      have hl : raw23800step2Labels = raw23800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical23801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23801 raw23801Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23801 raw23801Labels = mixedMoment B raw23801step0 raw23801step0Labels := by
      have hz : ∀ j, raw23801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23801step0 = (fun i j => raw23801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23801step0 raw23801; decide +kernel
      have hl : raw23801step0Labels = raw23801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23801 raw23801Labels permutation265 hz
    mixedMoment B raw23801step0 raw23801step0Labels = mixedMoment B raw23801step1 raw23801step1Labels := by
      have ha : raw23801step1 = (fun i j => raw23801step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23801step1 raw23801step0; decide +kernel
      have hl : raw23801step1Labels = raw23801step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23801step0 raw23801step0Labels permutation42 permutation4
    mixedMoment B raw23801step1 raw23801step1Labels = mixedMoment B raw23801step2 raw23801step2Labels := by
      have ha : raw23801step2 = -raw23801step1 := by apply Matrix.ext; change ∀ i j, raw23801step2 i j = -(raw23801step1 i j); unfold raw23801step2 raw23801step1; decide +kernel
      have hl : raw23801step2Labels = raw23801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical23802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23802 raw23802Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw23802 raw23802Labels = mixedMoment B raw23802step0 raw23802step0Labels := by
      have hz : ∀ j, raw23802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23802step0 = (fun i j => raw23802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23802step0 raw23802; decide +kernel
      have hl : raw23802step0Labels = raw23802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802 raw23802Labels permutation346 hz
    mixedMoment B raw23802step0 raw23802step0Labels = mixedMoment B raw23802step1 raw23802step1Labels := by
      have hz : ∀ j, raw23802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23802step1 = (fun i j => raw23802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23802step1 raw23802step0; decide +kernel
      have hl : raw23802step1Labels = raw23802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802step0 raw23802step0Labels permutation56 hz
    mixedMoment B raw23802step1 raw23802step1Labels = mixedMoment B raw23802step2 raw23802step2Labels := by
      have ha : raw23802step2 = (fun i j => raw23802step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23802step2 raw23802step1; decide +kernel
      have hl : raw23802step2Labels = raw23802step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23802step1 raw23802step1Labels permutation12 permutation4
    mixedMoment B raw23802step2 raw23802step2Labels = mixedMoment B raw23802step3 raw23802step3Labels := by
      have ha : raw23802step3 = -raw23802step2 := by apply Matrix.ext; change ∀ i j, raw23802step3 i j = -(raw23802step2 i j); unfold raw23802step3 raw23802step2; decide +kernel
      have hl : raw23802step3Labels = raw23802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical23803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23803 raw23803Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw23803 raw23803Labels = mixedMoment B raw23803step0 raw23803step0Labels := by
      have hz : ∀ j, raw23803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23803step0 = (fun i j => raw23803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23803step0 raw23803; decide +kernel
      have hl : raw23803step0Labels = raw23803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803 raw23803Labels permutation346 hz
    mixedMoment B raw23803step0 raw23803step0Labels = mixedMoment B raw23803step1 raw23803step1Labels := by
      have hz : ∀ j, raw23803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23803step1 = (fun i j => raw23803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23803step1 raw23803step0; decide +kernel
      have hl : raw23803step1Labels = raw23803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803step0 raw23803step0Labels permutation56 hz
    mixedMoment B raw23803step1 raw23803step1Labels = mixedMoment B raw23803step2 raw23803step2Labels := by
      have ha : raw23803step2 = (fun i j => raw23803step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23803step2 raw23803step1; decide +kernel
      have hl : raw23803step2Labels = raw23803step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23803step1 raw23803step1Labels permutation9 permutation4
    mixedMoment B raw23803step2 raw23803step2Labels = mixedMoment B raw23803step3 raw23803step3Labels := by
      have ha : raw23803step3 = -raw23803step2 := by apply Matrix.ext; change ∀ i j, raw23803step3 i j = -(raw23803step2 i j); unfold raw23803step3 raw23803step2; decide +kernel
      have hl : raw23803step3Labels = raw23803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1728 node1728Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3335 raw3335Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3335 raw3335Labels = mixedMoment B raw3335step0 raw3335step0Labels := by
      have hz : ∀ j, raw3335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3335step0 = (fun i j => raw3335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3335step0 raw3335; decide +kernel
      have hl : raw3335step0Labels = raw3335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335 raw3335Labels permutation434 hz
    mixedMoment B raw3335step0 raw3335step0Labels = mixedMoment B raw3335step1 raw3335step1Labels := by
      have hz : ∀ j, raw3335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3335step1 = (fun i j => raw3335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3335step1 raw3335step0; decide +kernel
      have hl : raw3335step1Labels = raw3335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step0 raw3335step0Labels permutation80 hz
    mixedMoment B raw3335step1 raw3335step1Labels = mixedMoment B raw3335step2 raw3335step2Labels := by
      have hz : ∀ j, raw3335step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3335step2 = (fun i j => raw3335step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3335step2 raw3335step1; decide +kernel
      have hl : raw3335step2Labels = raw3335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step1 raw3335step1Labels permutation14 hz
    mixedMoment B raw3335step2 raw3335step2Labels = mixedMoment B raw3335step3 raw3335step3Labels := by
      have hz : ∀ i, raw3335step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3335step3 = (fun i j => raw3335step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3335step3 raw3335step2; decide +kernel
      have hl : raw3335step3Labels = (fun j => raw3335step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3335step2 raw3335step2Labels permutation6 hz
    mixedMoment B raw3335step3 raw3335step3Labels = mixedMoment B raw3335step4 raw3335step4Labels := by
      have ha : raw3335step4 = (fun i j => raw3335step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3335step4 raw3335step3; decide +kernel
      have hl : raw3335step4Labels = raw3335step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3335step3 raw3335step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5209 raw5209Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5209 raw5209Labels = mixedMoment B raw5209step0 raw5209step0Labels := by
      have hz : ∀ j, raw5209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5209step0 = (fun i j => raw5209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5209step0 raw5209; decide +kernel
      have hl : raw5209step0Labels = raw5209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209 raw5209Labels permutation434 hz
    mixedMoment B raw5209step0 raw5209step0Labels = mixedMoment B raw5209step1 raw5209step1Labels := by
      have hz : ∀ j, raw5209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5209step1 = (fun i j => raw5209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5209step1 raw5209step0; decide +kernel
      have hl : raw5209step1Labels = raw5209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step0 raw5209step0Labels permutation80 hz
    mixedMoment B raw5209step1 raw5209step1Labels = mixedMoment B raw5209step2 raw5209step2Labels := by
      have hz : ∀ j, raw5209step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5209step2 = (fun i j => raw5209step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5209step2 raw5209step1; decide +kernel
      have hl : raw5209step2Labels = raw5209step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step1 raw5209step1Labels permutation14 hz
    mixedMoment B raw5209step2 raw5209step2Labels = mixedMoment B raw5209step3 raw5209step3Labels := by
      have hz : ∀ i, raw5209step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5209step3 = (fun i j => raw5209step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5209step3 raw5209step2; decide +kernel
      have hl : raw5209step3Labels = (fun j => raw5209step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5209step2 raw5209step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11531 raw11531Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11531 raw11531Labels = mixedMoment B raw11531step0 raw11531step0Labels := by
      have hz : ∀ j, raw11531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11531step0 = (fun i j => raw11531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11531step0 raw11531; decide +kernel
      have hl : raw11531step0Labels = raw11531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531 raw11531Labels permutation434 hz
    mixedMoment B raw11531step0 raw11531step0Labels = mixedMoment B raw11531step1 raw11531step1Labels := by
      have hz : ∀ j, raw11531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11531step1 = (fun i j => raw11531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11531step1 raw11531step0; decide +kernel
      have hl : raw11531step1Labels = raw11531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531step0 raw11531step0Labels permutation80 hz
    mixedMoment B raw11531step1 raw11531step1Labels = mixedMoment B raw11531step2 raw11531step2Labels := by
      have hz : ∀ i, raw11531step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11531step2 = (fun i j => raw11531step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11531step2 raw11531step1; decide +kernel
      have hl : raw11531step2Labels = (fun j => raw11531step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11531step1 raw11531step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11534 raw11534Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11534 raw11534Labels = mixedMoment B raw11534step0 raw11534step0Labels := by
      have hz : ∀ j, raw11534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11534step0 = (fun i j => raw11534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11534step0 raw11534; decide +kernel
      have hl : raw11534step0Labels = raw11534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534 raw11534Labels permutation434 hz
    mixedMoment B raw11534step0 raw11534step0Labels = mixedMoment B raw11534step1 raw11534step1Labels := by
      have hz : ∀ j, raw11534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11534step1 = (fun i j => raw11534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11534step1 raw11534step0; decide +kernel
      have hl : raw11534step1Labels = raw11534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534step0 raw11534step0Labels permutation56 hz
    mixedMoment B raw11534step1 raw11534step1Labels = mixedMoment B raw11534step2 raw11534step2Labels := by
      have hz : ∀ i, raw11534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11534step2 = (fun i j => raw11534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11534step2 raw11534step1; decide +kernel
      have hl : raw11534step2Labels = (fun j => raw11534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11534step1 raw11534step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11537 raw11537Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11537 raw11537Labels = mixedMoment B raw11537step0 raw11537step0Labels := by
      have hz : ∀ j, raw11537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11537step0 = (fun i j => raw11537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11537step0 raw11537; decide +kernel
      have hl : raw11537step0Labels = raw11537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537 raw11537Labels permutation346 hz
    mixedMoment B raw11537step0 raw11537step0Labels = mixedMoment B raw11537step1 raw11537step1Labels := by
      have hz : ∀ j, raw11537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11537step1 = (fun i j => raw11537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11537step1 raw11537step0; decide +kernel
      have hl : raw11537step1Labels = raw11537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537step0 raw11537step0Labels permutation56 hz
    mixedMoment B raw11537step1 raw11537step1Labels = mixedMoment B raw11537step2 raw11537step2Labels := by
      have hz : ∀ i, raw11537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11537step2 = (fun i j => raw11537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11537step2 raw11537step1; decide +kernel
      have hl : raw11537step2Labels = (fun j => raw11537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11537step1 raw11537step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11541 raw11541Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11541 raw11541Labels = mixedMoment B raw11541step0 raw11541step0Labels := by
      have hz : ∀ j, raw11541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11541step0 = (fun i j => raw11541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11541step0 raw11541; decide +kernel
      have hl : raw11541step0Labels = raw11541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541 raw11541Labels permutation434 hz
    mixedMoment B raw11541step0 raw11541step0Labels = mixedMoment B raw11541step1 raw11541step1Labels := by
      have hz : ∀ j, raw11541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11541step1 = (fun i j => raw11541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11541step1 raw11541step0; decide +kernel
      have hl : raw11541step1Labels = raw11541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541step0 raw11541step0Labels permutation80 hz
    mixedMoment B raw11541step1 raw11541step1Labels = mixedMoment B raw11541step2 raw11541step2Labels := by
      have hz : ∀ i, raw11541step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11541step2 = (fun i j => raw11541step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11541step2 raw11541step1; decide +kernel
      have hl : raw11541step2Labels = (fun j => raw11541step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11541step1 raw11541step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical11542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11542 raw11542Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11542 raw11542Labels = mixedMoment B raw11542step0 raw11542step0Labels := by
      have hz : ∀ j, raw11542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11542step0 = (fun i j => raw11542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11542step0 raw11542; decide +kernel
      have hl : raw11542step0Labels = raw11542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542 raw11542Labels permutation434 hz
    mixedMoment B raw11542step0 raw11542step0Labels = mixedMoment B raw11542step1 raw11542step1Labels := by
      have hz : ∀ j, raw11542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11542step1 = (fun i j => raw11542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11542step1 raw11542step0; decide +kernel
      have hl : raw11542step1Labels = raw11542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542step0 raw11542step0Labels permutation56 hz
    mixedMoment B raw11542step1 raw11542step1Labels = mixedMoment B raw11542step2 raw11542step2Labels := by
      have hz : ∀ i, raw11542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11542step2 = (fun i j => raw11542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11542step2 raw11542step1; decide +kernel
      have hl : raw11542step2Labels = (fun j => raw11542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11542step1 raw11542step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical11543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11543 raw11543Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11543 raw11543Labels = mixedMoment B raw11543step0 raw11543step0Labels := by
      have hz : ∀ j, raw11543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11543step0 = (fun i j => raw11543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11543step0 raw11543; decide +kernel
      have hl : raw11543step0Labels = raw11543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543 raw11543Labels permutation346 hz
    mixedMoment B raw11543step0 raw11543step0Labels = mixedMoment B raw11543step1 raw11543step1Labels := by
      have hz : ∀ j, raw11543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11543step1 = (fun i j => raw11543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11543step1 raw11543step0; decide +kernel
      have hl : raw11543step1Labels = raw11543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543step0 raw11543step0Labels permutation56 hz
    mixedMoment B raw11543step1 raw11543step1Labels = mixedMoment B raw11543step2 raw11543step2Labels := by
      have hz : ∀ i, raw11543step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11543step2 = (fun i j => raw11543step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11543step2 raw11543step1; decide +kernel
      have hl : raw11543step2Labels = (fun j => raw11543step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11543step1 raw11543step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node689 node689Labels = 0 := by
  exact mixedMoment_order_one B hB node689 node689Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node664 node664Labels = Sparse.eval nodeValue664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 664) = mixedMoment B node664 node664Labels := rfl
  simpa [nodeValue664, Sparse.eval] using hc.symm

theorem sound684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node684 node684Labels = Sparse.eval nodeValue684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 684) = mixedMoment B node684 node684Labels := rfl
  simpa [nodeValue684, Sparse.eval] using hc.symm

theorem sound685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node685 node685Labels = Sparse.eval nodeValue685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 685) = mixedMoment B node685 node685Labels := rfl
  simpa [nodeValue685, Sparse.eval] using hc.symm

theorem sound689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node689 node689Labels = Sparse.eval nodeValue689 (mixedVector B) := by
  simpa only [nodeValue689, Sparse.eval_nil] using zero689 B _hB _hF

theorem sound703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node703 node703Labels = Sparse.eval nodeValue703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 703) = mixedMoment B node703 node703Labels := rfl
  simpa [nodeValue703, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node704 node704Labels = Sparse.eval nodeValue704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 704) = mixedMoment B node704 node704Labels := rfl
  simpa [nodeValue704, Sparse.eval] using hc.symm

theorem sound710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node710 node710Labels = Sparse.eval nodeValue710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 710) = mixedMoment B node710 node710Labels := rfl
  simpa [nodeValue710, Sparse.eval] using hc.symm

theorem sound724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node724 node724Labels = Sparse.eval nodeValue724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 724) = mixedMoment B node724 node724Labels := rfl
  simpa [nodeValue724, Sparse.eval] using hc.symm

theorem sound734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node734 node734Labels = Sparse.eval nodeValue734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 734) = mixedMoment B node734 node734Labels := rfl
  simpa [nodeValue734, Sparse.eval] using hc.symm

theorem sound738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node738 node738Labels = Sparse.eval nodeValue738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 738) = mixedMoment B node738 node738Labels := rfl
  simpa [nodeValue738, Sparse.eval] using hc.symm

theorem sound739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node739 node739Labels = Sparse.eval nodeValue739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 739) = mixedMoment B node739 node739Labels := rfl
  simpa [nodeValue739, Sparse.eval] using hc.symm

theorem sound742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node742 node742Labels = Sparse.eval nodeValue742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 742) = mixedMoment B node742 node742Labels := rfl
  simpa [nodeValue742, Sparse.eval] using hc.symm

theorem sound743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node743 node743Labels = Sparse.eval nodeValue743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 743) = mixedMoment B node743 node743Labels := rfl
  simpa [nodeValue743, Sparse.eval] using hc.symm

theorem sound749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node749 node749Labels = Sparse.eval nodeValue749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 749) = mixedMoment B node749 node749Labels := rfl
  simpa [nodeValue749, Sparse.eval] using hc.symm

theorem sound763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node763 node763Labels = Sparse.eval nodeValue763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 763) = mixedMoment B node763 node763Labels := rfl
  simpa [nodeValue763, Sparse.eval] using hc.symm

theorem sound764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node764 node764Labels = Sparse.eval nodeValue764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 764) = mixedMoment B node764 node764Labels := rfl
  simpa [nodeValue764, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node768 node768Labels = 0 := by
  exact mixedMoment_order_one B hB node768 node768Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = 0 := by
  exact mixedMoment_order_one B hB node806 node806Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = 0 := by
  exact mixedMoment_order_one B hB node810 node810Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node816 node816Labels = 0 := by
  exact mixedMoment_order_one B hB node816 node816Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node768 node768Labels = Sparse.eval nodeValue768 (mixedVector B) := by
  simpa only [nodeValue768, Sparse.eval_nil] using zero768 B _hB _hF

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

theorem sound800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node800 node800Labels = Sparse.eval nodeValue800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 800) = mixedMoment B node800 node800Labels := rfl
  simpa [nodeValue800, Sparse.eval] using hc.symm

theorem sound806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = Sparse.eval nodeValue806 (mixedVector B) := by
  simpa only [nodeValue806, Sparse.eval_nil] using zero806 B _hB _hF

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

theorem sound810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = Sparse.eval nodeValue810 (mixedVector B) := by
  simpa only [nodeValue810, Sparse.eval_nil] using zero810 B _hB _hF

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

theorem sound816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node816 node816Labels = Sparse.eval nodeValue816 (mixedVector B) := by
  simpa only [nodeValue816, Sparse.eval_nil] using zero816 B _hB _hF

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

theorem sound830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node830 node830Labels = Sparse.eval nodeValue830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 830) = mixedMoment B node830 node830Labels := rfl
  simpa [nodeValue830, Sparse.eval] using hc.symm

theorem sound831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node831 node831Labels = Sparse.eval nodeValue831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 831) = mixedMoment B node831 node831Labels := rfl
  simpa [nodeValue831, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node851 node851Labels = 0 := by
  exact mixedMoment_order_one B hB node851 node851Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = 0 := by
  exact mixedMoment_order_one B hB node852 node852Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = 0 := by
  exact mixedMoment_order_one B hB node856 node856Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node843 node843Labels = Sparse.eval nodeValue843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 843) = mixedMoment B node843 node843Labels := rfl
  simpa [nodeValue843, Sparse.eval] using hc.symm

theorem sound844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node844 node844Labels = Sparse.eval nodeValue844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 844) = mixedMoment B node844 node844Labels := rfl
  simpa [nodeValue844, Sparse.eval] using hc.symm

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

theorem sound851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node851 node851Labels = Sparse.eval nodeValue851 (mixedVector B) := by
  simpa only [nodeValue851, Sparse.eval_nil] using zero851 B _hB _hF

theorem sound852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = Sparse.eval nodeValue852 (mixedVector B) := by
  simpa only [nodeValue852, Sparse.eval_nil] using zero852 B _hB _hF

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

theorem sound856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = Sparse.eval nodeValue856 (mixedVector B) := by
  simpa only [nodeValue856, Sparse.eval_nil] using zero856 B _hB _hF

theorem sound858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node858 node858Labels = Sparse.eval nodeValue858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 858) = mixedMoment B node858 node858Labels := rfl
  simpa [nodeValue858, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = 0 := by
  exact mixedMoment_order_one B hB node1082 node1082Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

theorem sound1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = Sparse.eval nodeValue1082 (mixedVector B) := by
  simpa only [nodeValue1082, Sparse.eval_nil] using zero1082 B _hB _hF

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1595 node1595Labels = 0 := by
  exact mixedMoment_alpha B hF node1595 node1595Labels 1 permutation434
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1594 node1594Labels = Sparse.eval nodeValue1594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1594) = mixedMoment B node1594 node1594Labels := rfl
  simpa [nodeValue1594, Sparse.eval] using hc.symm

theorem sound1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1595 node1595Labels = Sparse.eval nodeValue1595 (mixedVector B) := by
  simpa only [nodeValue1595, Sparse.eval_nil] using zero1595 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1605 node1605Labels = Sparse.eval nodeValue1605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1605) = mixedMoment B node1605 node1605Labels := rfl
  simpa [nodeValue1605, Sparse.eval] using hc.symm

theorem sound1612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1612 node1612Labels = Sparse.eval nodeValue1612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1612) = mixedMoment B node1612 node1612Labels := rfl
  simpa [nodeValue1612, Sparse.eval] using hc.symm

theorem sound1640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1640 node1640Labels = Sparse.eval nodeValue1640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1640) = mixedMoment B node1640 node1640Labels := rfl
  simpa [nodeValue1640, Sparse.eval] using hc.symm

theorem sound1641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1641 node1641Labels = Sparse.eval nodeValue1641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1641) = mixedMoment B node1641 node1641Labels := rfl
  simpa [nodeValue1641, Sparse.eval] using hc.symm

theorem sound1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1653 node1653Labels = Sparse.eval nodeValue1653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1653) = mixedMoment B node1653 node1653Labels := rfl
  simpa [nodeValue1653, Sparse.eval] using hc.symm

theorem sound1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1661 node1661Labels = Sparse.eval nodeValue1661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1661) = mixedMoment B node1661 node1661Labels := rfl
  simpa [nodeValue1661, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

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

theorem sound2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2521 node2521Labels = Sparse.eval nodeValue2521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2521) = mixedMoment B node2521 node2521Labels := rfl
  simpa [nodeValue2521, Sparse.eval] using hc.symm

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

theorem sound3022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3022 node3022Labels = Sparse.eval nodeValue3022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3022) = mixedMoment B node3022 node3022Labels := rfl
  simpa [nodeValue3022, Sparse.eval] using hc.symm

theorem sound3049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3049 node3049Labels = Sparse.eval nodeValue3049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3049) = mixedMoment B node3049 node3049Labels := rfl
  simpa [nodeValue3049, Sparse.eval] using hc.symm

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

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node561 node561Labels = 0 := by
  exact mixedMoment_order_one B hB node561 node561Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node539 node539Labels = Sparse.eval nodeValue539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 539) = mixedMoment B node539 node539Labels := rfl
  simpa [nodeValue539, Sparse.eval] using hc.symm

theorem sound543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node543 node543Labels = Sparse.eval nodeValue543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 543) = mixedMoment B node543 node543Labels := rfl
  simpa [nodeValue543, Sparse.eval] using hc.symm

theorem sound544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node544 node544Labels = Sparse.eval nodeValue544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 544) = mixedMoment B node544 node544Labels := rfl
  simpa [nodeValue544, Sparse.eval] using hc.symm

theorem sound547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node547 node547Labels = Sparse.eval nodeValue547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 547) = mixedMoment B node547 node547Labels := rfl
  simpa [nodeValue547, Sparse.eval] using hc.symm

theorem sound548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node548 node548Labels = Sparse.eval nodeValue548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 548) = mixedMoment B node548 node548Labels := rfl
  simpa [nodeValue548, Sparse.eval] using hc.symm

theorem sound552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node552 node552Labels = Sparse.eval nodeValue552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 552) = mixedMoment B node552 node552Labels := rfl
  simpa [nodeValue552, Sparse.eval] using hc.symm

theorem sound561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node561 node561Labels = Sparse.eval nodeValue561 (mixedVector B) := by
  simpa only [nodeValue561, Sparse.eval_nil] using zero561 B _hB _hF

theorem sound562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node562 node562Labels = Sparse.eval nodeValue562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 562) = mixedMoment B node562 node562Labels := rfl
  simpa [nodeValue562, Sparse.eval] using hc.symm

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

theorem sound4059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4059 node4059Labels = Sparse.eval nodeValue4059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4059) = mixedMoment B node4059 node4059Labels := rfl
  simpa [nodeValue4059, Sparse.eval] using hc.symm

theorem sound4061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4061 node4061Labels = Sparse.eval nodeValue4061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4061) = mixedMoment B node4061 node4061Labels := rfl
  simpa [nodeValue4061, Sparse.eval] using hc.symm

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

theorem sound4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4067 node4067Labels = Sparse.eval nodeValue4067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4067) = mixedMoment B node4067 node4067Labels := rfl
  simpa [nodeValue4067, Sparse.eval] using hc.symm

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1561 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 0) (sourceB1561 + difference 0 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 562) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 0) (sourceB1561 + difference 0 1) sourceC1561) = raw23662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23662; decide +kernel
    rw [ha]
    exact (canonical23662 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 1) (sourceB1561 + difference 1 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 1) (sourceB1561 + difference 1 1) sourceC1561) = raw22020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw22020; decide +kernel
    rw [ha]
    exact (canonical22020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 2) (sourceB1561 + difference 2 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 2) (sourceB1561 + difference 2 1) sourceC1561) = raw23663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23663; decide +kernel
    rw [ha]
    exact (canonical23663 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 3) (sourceB1561 + difference 3 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 3) (sourceB1561 + difference 3 1) sourceC1561) = raw23664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23664; decide +kernel
    rw [ha]
    exact (canonical23664 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 4) (sourceB1561 + difference 4 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 4) (sourceB1561 + difference 4 1) sourceC1561) = raw22017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw22017; decide +kernel
    rw [ha]
    exact (canonical22017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 5) (sourceB1561 + difference 5 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 5) (sourceB1561 + difference 5 1) sourceC1561) = raw23665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23665; decide +kernel
    rw [ha]
    exact (canonical23665 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1561 + sourceB1561) sourceC1561) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1561 + sourceB1561) sourceC1561) = raw22022 := by
      apply Matrix.ext; unfold doubleCharges sourceA1561 sourceB1561 sourceC1561 raw22022; decide +kernel
    rw [ha]
    exact (canonical22022 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1561 sourceB1561 sourceC1561
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1561, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1562 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 0) (sourceB1562 + difference 0 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 0) (sourceB1562 + difference 0 0) sourceC1562) = raw22037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw22037; decide +kernel
    rw [ha]
    exact (canonical22037 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 1) (sourceB1562 + difference 1 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 1) (sourceB1562 + difference 1 0) sourceC1562) = raw23666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23666; decide +kernel
    rw [ha]
    exact (canonical23666 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 2) (sourceB1562 + difference 2 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 2) (sourceB1562 + difference 2 0) sourceC1562) = raw23667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23667; decide +kernel
    rw [ha]
    exact (canonical23667 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 3) (sourceB1562 + difference 3 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 3) (sourceB1562 + difference 3 0) sourceC1562) = raw23668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23668; decide +kernel
    rw [ha]
    exact (canonical23668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 4) (sourceB1562 + difference 4 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 4) (sourceB1562 + difference 4 0) sourceC1562) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 5) (sourceB1562 + difference 5 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 5) (sourceB1562 + difference 5 0) sourceC1562) = raw23669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23669; decide +kernel
    rw [ha]
    exact (canonical23669 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1562 + sourceB1562) sourceC1562) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1562 + sourceB1562) sourceC1562) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1562 sourceB1562 sourceC1562 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1562 sourceB1562 sourceC1562
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1562, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1564 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 0) (sourceB1564 + difference 0 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 0) (sourceB1564 + difference 0 0) sourceC1564) = raw22076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw22076; decide +kernel
    rw [ha]
    exact (canonical22076 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 1) (sourceB1564 + difference 1 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 1) (sourceB1564 + difference 1 0) sourceC1564) = raw23674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23674; decide +kernel
    rw [ha]
    exact (canonical23674 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 2) (sourceB1564 + difference 2 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 2) (sourceB1564 + difference 2 0) sourceC1564) = raw23675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23675; decide +kernel
    rw [ha]
    exact (canonical23675 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 3) (sourceB1564 + difference 3 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1594) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 3) (sourceB1564 + difference 3 0) sourceC1564) = raw23676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23676; decide +kernel
    rw [ha]
    exact (canonical23676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 4) (sourceB1564 + difference 4 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 4) (sourceB1564 + difference 4 0) sourceC1564) = raw22072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw22072; decide +kernel
    rw [ha]
    exact (canonical22072 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 5) (sourceB1564 + difference 5 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 5) (sourceB1564 + difference 5 0) sourceC1564) = raw23677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23677; decide +kernel
    rw [ha]
    exact (canonical23677 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1564 + sourceB1564) sourceC1564) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1564 + sourceB1564) sourceC1564) = raw22078 := by
      apply Matrix.ext; unfold doubleCharges sourceA1564 sourceB1564 sourceC1564 raw22078; decide +kernel
    rw [ha]
    exact (canonical22078 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1564 sourceB1564 sourceC1564
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1564, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1565 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 0) (sourceB1565 + difference 0 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 0) (sourceB1565 + difference 0 1) sourceC1565) = raw23678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23678; decide +kernel
    rw [ha]
    exact (canonical23678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 1) (sourceB1565 + difference 1 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 1) (sourceB1565 + difference 1 1) sourceC1565) = raw22076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw22076; decide +kernel
    rw [ha]
    exact (canonical22076 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 2) (sourceB1565 + difference 2 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 2) (sourceB1565 + difference 2 1) sourceC1565) = raw23679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23679; decide +kernel
    rw [ha]
    exact (canonical23679 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 3) (sourceB1565 + difference 3 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 703) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 3) (sourceB1565 + difference 3 1) sourceC1565) = raw23680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23680; decide +kernel
    rw [ha]
    exact (canonical23680 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 4) (sourceB1565 + difference 4 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 4) (sourceB1565 + difference 4 1) sourceC1565) = raw22073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw22073; decide +kernel
    rw [ha]
    exact (canonical22073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 5) (sourceB1565 + difference 5 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 5) (sourceB1565 + difference 5 1) sourceC1565) = raw23681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23681; decide +kernel
    rw [ha]
    exact (canonical23681 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1565 + sourceB1565) sourceC1565) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1565 + sourceB1565) sourceC1565) = raw22078 := by
      apply Matrix.ext; unfold doubleCharges sourceA1565 sourceB1565 sourceC1565 raw22078; decide +kernel
    rw [ha]
    exact (canonical22078 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1565 sourceB1565 sourceC1565
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1565, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 0) (sourceB1566 + difference 0 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 552) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 0) (sourceB1566 + difference 0 5) sourceC1566) = raw23682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23682; decide +kernel
    rw [ha]
    exact (canonical23682 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 1) (sourceB1566 + difference 1 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 1) (sourceB1566 + difference 1 5) sourceC1566) = raw23683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23683; decide +kernel
    rw [ha]
    exact (canonical23683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 2) (sourceB1566 + difference 2 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 2) (sourceB1566 + difference 2 5) sourceC1566) = raw23329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23329; decide +kernel
    rw [ha]
    exact (canonical23329 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 3) (sourceB1566 + difference 3 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 710) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 3) (sourceB1566 + difference 3 5) sourceC1566) = raw23328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23328; decide +kernel
    rw [ha]
    exact (canonical23328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 4) (sourceB1566 + difference 4 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 4) (sourceB1566 + difference 4 5) sourceC1566) = raw23684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23684; decide +kernel
    rw [ha]
    exact (canonical23684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 5) (sourceB1566 + difference 5 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 5) (sourceB1566 + difference 5 5) sourceC1566) = raw23685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23685; decide +kernel
    rw [ha]
    exact (canonical23685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1566 + sourceB1566) sourceC1566) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1566 + sourceB1566) sourceC1566) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1566 sourceB1566 sourceC1566 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1566 sourceB1566 sourceC1566
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1566, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1567 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 0) (sourceB1567 + difference 0 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 0) (sourceB1567 + difference 0 0) sourceC1567) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 1) (sourceB1567 + difference 1 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 1) (sourceB1567 + difference 1 0) sourceC1567) = raw23686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23686; decide +kernel
    rw [ha]
    exact (canonical23686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 2) (sourceB1567 + difference 2 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 2) (sourceB1567 + difference 2 0) sourceC1567) = raw23687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23687; decide +kernel
    rw [ha]
    exact (canonical23687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 3) (sourceB1567 + difference 3 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1595) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 3) (sourceB1567 + difference 3 0) sourceC1567) = raw23688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23688; decide +kernel
    rw [ha]
    exact (canonical23688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 4) (sourceB1567 + difference 4 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 4) (sourceB1567 + difference 4 0) sourceC1567) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 5) (sourceB1567 + difference 5 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 5) (sourceB1567 + difference 5 0) sourceC1567) = raw23689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23689; decide +kernel
    rw [ha]
    exact (canonical23689 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1567 + sourceB1567) sourceC1567) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1567 + sourceB1567) sourceC1567) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1567 sourceB1567 sourceC1567 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1567 sourceB1567 sourceC1567
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1567, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1568 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 0) (sourceB1568 + difference 0 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 544) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 0) (sourceB1568 + difference 0 1) sourceC1568) = raw23690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23690; decide +kernel
    rw [ha]
    exact (canonical23690 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 1) (sourceB1568 + difference 1 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 1) (sourceB1568 + difference 1 1) sourceC1568) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 2) (sourceB1568 + difference 2 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 2) (sourceB1568 + difference 2 1) sourceC1568) = raw23691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23691; decide +kernel
    rw [ha]
    exact (canonical23691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 3) (sourceB1568 + difference 3 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 704) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 3) (sourceB1568 + difference 3 1) sourceC1568) = raw23692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23692; decide +kernel
    rw [ha]
    exact (canonical23692 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 4) (sourceB1568 + difference 4 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 4) (sourceB1568 + difference 4 1) sourceC1568) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1568 + difference 1 5) (sourceB1568 + difference 5 1) sourceC1568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1568 + difference 1 5) (sourceB1568 + difference 5 1) sourceC1568) = raw23693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1568 sourceB1568 sourceC1568 difference raw23693; decide +kernel
    rw [ha]
    exact (canonical23693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1568 + sourceB1568) sourceC1568) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1568 + sourceB1568) sourceC1568) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1568 sourceB1568 sourceC1568 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1568 sourceB1568 sourceC1568
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1568, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1570 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 1) (sourceB1570 + difference 1 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 1) (sourceB1570 + difference 1 0) sourceC1570) = raw23724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23724; decide +kernel
    rw [ha]
    exact (canonical23724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 2) (sourceB1570 + difference 2 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 2) (sourceB1570 + difference 2 0) sourceC1570) = raw23725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23725; decide +kernel
    rw [ha]
    exact (canonical23725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 3) (sourceB1570 + difference 3 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 3) (sourceB1570 + difference 3 0) sourceC1570) = raw23726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23726; decide +kernel
    rw [ha]
    exact (canonical23726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 4) (sourceB1570 + difference 4 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 4) (sourceB1570 + difference 4 0) sourceC1570) = raw23727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23727; decide +kernel
    rw [ha]
    exact (canonical23727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1570 + difference 0 5) (sourceB1570 + difference 5 0) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1570 + difference 0 5) (sourceB1570 + difference 5 0) sourceC1570) = raw23728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23728; decide +kernel
    rw [ha]
    exact (canonical23728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 0) (sourceB1570 + difference 0 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 0) (sourceB1570 + difference 0 1) sourceC1570) = raw23729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23729; decide +kernel
    rw [ha]
    exact (canonical23729 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 2) (sourceB1570 + difference 2 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 768) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 2) (sourceB1570 + difference 2 1) sourceC1570) = raw23730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23730; decide +kernel
    rw [ha]
    exact (canonical23730 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 3) (sourceB1570 + difference 3 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 768) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 3) (sourceB1570 + difference 3 1) sourceC1570) = raw23731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23731; decide +kernel
    rw [ha]
    exact (canonical23731 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 4) (sourceB1570 + difference 4 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 4) (sourceB1570 + difference 4 1) sourceC1570) = raw23732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23732; decide +kernel
    rw [ha]
    exact (canonical23732 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1570 + difference 1 5) (sourceB1570 + difference 5 1) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1570 + difference 1 5) (sourceB1570 + difference 5 1) sourceC1570) = raw23733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23733; decide +kernel
    rw [ha]
    exact (canonical23733 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 0) (sourceB1570 + difference 0 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 0) (sourceB1570 + difference 0 2) sourceC1570) = raw23734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23734; decide +kernel
    rw [ha]
    exact (canonical23734 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 1) (sourceB1570 + difference 1 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 800) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 1) (sourceB1570 + difference 1 2) sourceC1570) = raw23735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23735; decide +kernel
    rw [ha]
    exact (canonical23735 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 3) (sourceB1570 + difference 3 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 749) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 3) (sourceB1570 + difference 3 2) sourceC1570) = raw23736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23736; decide +kernel
    rw [ha]
    exact (canonical23736 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 4) (sourceB1570 + difference 4 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 4) (sourceB1570 + difference 4 2) sourceC1570) = raw23737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23737; decide +kernel
    rw [ha]
    exact (canonical23737 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1570 + difference 2 5) (sourceB1570 + difference 5 2) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1570 + difference 2 5) (sourceB1570 + difference 5 2) sourceC1570) = raw23738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23738; decide +kernel
    rw [ha]
    exact (canonical23738 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 0) (sourceB1570 + difference 0 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 0) (sourceB1570 + difference 0 3) sourceC1570) = raw23739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23739; decide +kernel
    rw [ha]
    exact (canonical23739 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 1) (sourceB1570 + difference 1 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 800) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 1) (sourceB1570 + difference 1 3) sourceC1570) = raw23740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23740; decide +kernel
    rw [ha]
    exact (canonical23740 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 2) (sourceB1570 + difference 2 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 749) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 2) (sourceB1570 + difference 2 3) sourceC1570) = raw23741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23741; decide +kernel
    rw [ha]
    exact (canonical23741 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 4) (sourceB1570 + difference 4 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 4) (sourceB1570 + difference 4 3) sourceC1570) = raw23742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23742; decide +kernel
    rw [ha]
    exact (canonical23742 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1570 + difference 3 5) (sourceB1570 + difference 5 3) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1570 + difference 3 5) (sourceB1570 + difference 5 3) sourceC1570) = raw23743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23743; decide +kernel
    rw [ha]
    exact (canonical23743 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 0) (sourceB1570 + difference 0 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 0) (sourceB1570 + difference 0 4) sourceC1570) = raw23744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23744; decide +kernel
    rw [ha]
    exact (canonical23744 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 1) (sourceB1570 + difference 1 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 843) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 1) (sourceB1570 + difference 1 4) sourceC1570) = raw23745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23745; decide +kernel
    rw [ha]
    exact (canonical23745 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 2) (sourceB1570 + difference 2 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 2) (sourceB1570 + difference 2 4) sourceC1570) = raw23746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23746; decide +kernel
    rw [ha]
    exact (canonical23746 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 3) (sourceB1570 + difference 3 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 3) (sourceB1570 + difference 3 4) sourceC1570) = raw23747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23747; decide +kernel
    rw [ha]
    exact (canonical23747 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1570 + difference 4 5) (sourceB1570 + difference 5 4) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1570 + difference 4 5) (sourceB1570 + difference 5 4) sourceC1570) = raw23748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23748; decide +kernel
    rw [ha]
    exact (canonical23748 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 0) (sourceB1570 + difference 0 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 685) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 0) (sourceB1570 + difference 0 5) sourceC1570) = raw23749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23749; decide +kernel
    rw [ha]
    exact (canonical23749 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 1) (sourceB1570 + difference 1 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 844) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 1) (sourceB1570 + difference 1 5) sourceC1570) = raw23750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23750; decide +kernel
    rw [ha]
    exact (canonical23750 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 2) (sourceB1570 + difference 2 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 2) (sourceB1570 + difference 2 5) sourceC1570) = raw23751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23751; decide +kernel
    rw [ha]
    exact (canonical23751 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 3) (sourceB1570 + difference 3 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 3) (sourceB1570 + difference 3 5) sourceC1570) = raw23752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23752; decide +kernel
    rw [ha]
    exact (canonical23752 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1570 + difference 5 4) (sourceB1570 + difference 4 5) sourceC1570) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1570 + difference 5 4) (sourceB1570 + difference 4 5) sourceC1570) = raw23753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1570 sourceB1570 sourceC1570 difference raw23753; decide +kernel
    rw [ha]
    exact (canonical23753 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1570 sourceB1570 sourceC1570
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1570, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 0) (sourceB1571 + difference 0 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 0) (sourceB1571 + difference 0 0) sourceC1571) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 1) (sourceB1571 + difference 1 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 1) (sourceB1571 + difference 1 0) sourceC1571) = raw23754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23754; decide +kernel
    rw [ha]
    exact (canonical23754 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 2) (sourceB1571 + difference 2 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 2) (sourceB1571 + difference 2 0) sourceC1571) = raw23755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23755; decide +kernel
    rw [ha]
    exact (canonical23755 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 3) (sourceB1571 + difference 3 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 3) (sourceB1571 + difference 3 0) sourceC1571) = raw23756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23756; decide +kernel
    rw [ha]
    exact (canonical23756 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 4) (sourceB1571 + difference 4 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 4) (sourceB1571 + difference 4 0) sourceC1571) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1571 + difference 0 5) (sourceB1571 + difference 5 0) sourceC1571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1571 + difference 0 5) (sourceB1571 + difference 5 0) sourceC1571) = raw23757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1571 sourceB1571 sourceC1571 difference raw23757; decide +kernel
    rw [ha]
    exact (canonical23757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1571 + sourceB1571) sourceC1571) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1571 + sourceB1571) sourceC1571) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1571 sourceB1571 sourceC1571 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1571 sourceB1571 sourceC1571
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1571, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1572 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1572 + difference 0 0) (sourceB1572 + difference 0 0) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1572 + difference 0 0) (sourceB1572 + difference 0 0) sourceC1572) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1572 + difference 1 0) (sourceB1572 + difference 0 1) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 561) := by
    have ha : (tripleCharges (sourceA1572 + difference 1 0) (sourceB1572 + difference 0 1) sourceC1572) = raw23758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23758; decide +kernel
    rw [ha]
    exact (canonical23758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1572 + difference 2 0) (sourceB1572 + difference 0 2) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1572 + difference 2 0) (sourceB1572 + difference 0 2) sourceC1572) = raw23759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23759; decide +kernel
    rw [ha]
    exact (canonical23759 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1572 + difference 3 0) (sourceB1572 + difference 0 3) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1572 + difference 3 0) (sourceB1572 + difference 0 3) sourceC1572) = raw23760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23760; decide +kernel
    rw [ha]
    exact (canonical23760 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1572 + difference 4 0) (sourceB1572 + difference 0 4) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1572 + difference 4 0) (sourceB1572 + difference 0 4) sourceC1572) = raw23761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw23761; decide +kernel
    rw [ha]
    exact (canonical23761 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1572 + difference 5 0) (sourceB1572 + difference 0 5) sourceC1572) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1572 + difference 5 0) (sourceB1572 + difference 0 5) sourceC1572) = raw22121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1572 sourceB1572 sourceC1572 difference raw22121; decide +kernel
    rw [ha]
    exact (canonical22121 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1572 + sourceB1572) sourceC1572) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1572 + sourceB1572) sourceC1572) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1572 sourceB1572 sourceC1572 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1572 sourceB1572 sourceC1572
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1572, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1573 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1573 + difference 0 1) (sourceB1573 + difference 1 0) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1573 + difference 0 1) (sourceB1573 + difference 1 0) sourceC1573) = raw23754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23754; decide +kernel
    rw [ha]
    exact (canonical23754 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1573 + difference 1 1) (sourceB1573 + difference 1 1) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1573 + difference 1 1) (sourceB1573 + difference 1 1) sourceC1573) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1573 + difference 2 1) (sourceB1573 + difference 1 2) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1573 + difference 2 1) (sourceB1573 + difference 1 2) sourceC1573) = raw23762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23762; decide +kernel
    rw [ha]
    exact (canonical23762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1573 + difference 3 1) (sourceB1573 + difference 1 3) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1573 + difference 3 1) (sourceB1573 + difference 1 3) sourceC1573) = raw23763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23763; decide +kernel
    rw [ha]
    exact (canonical23763 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1573 + difference 4 1) (sourceB1573 + difference 1 4) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA1573 + difference 4 1) (sourceB1573 + difference 1 4) sourceC1573) = raw23764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw23764; decide +kernel
    rw [ha]
    exact (canonical23764 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1573 + difference 5 1) (sourceB1573 + difference 1 5) sourceC1573) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA1573 + difference 5 1) (sourceB1573 + difference 1 5) sourceC1573) = raw22122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1573 sourceB1573 sourceC1573 difference raw22122; decide +kernel
    rw [ha]
    exact (canonical22122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1573 + sourceB1573) sourceC1573) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1573 + sourceB1573) sourceC1573) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1573 sourceB1573 sourceC1573 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1573 sourceB1573 sourceC1573
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1573, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1575 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 1) (sourceB1575 + difference 1 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 1) (sourceB1575 + difference 1 0) sourceC1575) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 2) (sourceB1575 + difference 2 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 2) (sourceB1575 + difference 2 0) sourceC1575) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 3) (sourceB1575 + difference 3 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 3) (sourceB1575 + difference 3 0) sourceC1575) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 4) (sourceB1575 + difference 4 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 4) (sourceB1575 + difference 4 0) sourceC1575) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1575 + difference 0 5) (sourceB1575 + difference 5 0) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1575 + difference 0 5) (sourceB1575 + difference 5 0) sourceC1575) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 0) (sourceB1575 + difference 0 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 0) (sourceB1575 + difference 0 1) sourceC1575) = raw23777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23777; decide +kernel
    rw [ha]
    exact (canonical23777 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 2) (sourceB1575 + difference 2 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 2) (sourceB1575 + difference 2 1) sourceC1575) = raw23778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23778; decide +kernel
    rw [ha]
    exact (canonical23778 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 3) (sourceB1575 + difference 3 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 3) (sourceB1575 + difference 3 1) sourceC1575) = raw23779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23779; decide +kernel
    rw [ha]
    exact (canonical23779 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 4) (sourceB1575 + difference 4 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 4) (sourceB1575 + difference 4 1) sourceC1575) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1575 + difference 1 5) (sourceB1575 + difference 5 1) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 1 5) (sourceB1575 + difference 5 1) sourceC1575) = raw23780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23780; decide +kernel
    rw [ha]
    exact (canonical23780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 0) (sourceB1575 + difference 0 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 0) (sourceB1575 + difference 0 2) sourceC1575) = raw23781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23781; decide +kernel
    rw [ha]
    exact (canonical23781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 1) (sourceB1575 + difference 1 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 1) (sourceB1575 + difference 1 2) sourceC1575) = raw23782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23782; decide +kernel
    rw [ha]
    exact (canonical23782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 3) (sourceB1575 + difference 3 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 3) (sourceB1575 + difference 3 2) sourceC1575) = raw23783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23783; decide +kernel
    rw [ha]
    exact (canonical23783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 4) (sourceB1575 + difference 4 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 4) (sourceB1575 + difference 4 2) sourceC1575) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1575 + difference 2 5) (sourceB1575 + difference 5 2) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 2 5) (sourceB1575 + difference 5 2) sourceC1575) = raw23784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23784; decide +kernel
    rw [ha]
    exact (canonical23784 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 0) (sourceB1575 + difference 0 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 0) (sourceB1575 + difference 0 3) sourceC1575) = raw23785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23785; decide +kernel
    rw [ha]
    exact (canonical23785 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 1) (sourceB1575 + difference 1 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 1) (sourceB1575 + difference 1 3) sourceC1575) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 2) (sourceB1575 + difference 2 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 2) (sourceB1575 + difference 2 3) sourceC1575) = raw23787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23787; decide +kernel
    rw [ha]
    exact (canonical23787 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 4) (sourceB1575 + difference 4 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 4) (sourceB1575 + difference 4 3) sourceC1575) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1575 + difference 3 5) (sourceB1575 + difference 5 3) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1575 + difference 3 5) (sourceB1575 + difference 5 3) sourceC1575) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 0) (sourceB1575 + difference 0 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 0) (sourceB1575 + difference 0 4) sourceC1575) = raw23788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23788; decide +kernel
    rw [ha]
    exact (canonical23788 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 1) (sourceB1575 + difference 1 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 1) (sourceB1575 + difference 1 4) sourceC1575) = raw23789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23789; decide +kernel
    rw [ha]
    exact (canonical23789 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 2) (sourceB1575 + difference 2 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 2) (sourceB1575 + difference 2 4) sourceC1575) = raw23790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23790; decide +kernel
    rw [ha]
    exact (canonical23790 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 3) (sourceB1575 + difference 3 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 3) (sourceB1575 + difference 3 4) sourceC1575) = raw23791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23791; decide +kernel
    rw [ha]
    exact (canonical23791 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1575 + difference 4 5) (sourceB1575 + difference 5 4) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1575 + difference 4 5) (sourceB1575 + difference 5 4) sourceC1575) = raw23792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw23792; decide +kernel
    rw [ha]
    exact (canonical23792 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 0) (sourceB1575 + difference 0 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 0) (sourceB1575 + difference 0 5) sourceC1575) = raw22310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22310; decide +kernel
    rw [ha]
    exact (canonical22310 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 1) (sourceB1575 + difference 1 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 1) (sourceB1575 + difference 1 5) sourceC1575) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 2) (sourceB1575 + difference 2 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 2) (sourceB1575 + difference 2 5) sourceC1575) = raw22312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22312; decide +kernel
    rw [ha]
    exact (canonical22312 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 3) (sourceB1575 + difference 3 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 3) (sourceB1575 + difference 3 5) sourceC1575) = raw22313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw22313; decide +kernel
    rw [ha]
    exact (canonical22313 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1575 + difference 5 4) (sourceB1575 + difference 4 5) sourceC1575) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1575 + difference 5 4) (sourceB1575 + difference 4 5) sourceC1575) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1575 sourceB1575 sourceC1575 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1575 sourceB1575 sourceC1575
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1575, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1576 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 0) (sourceB1576 + difference 0 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 0) (sourceB1576 + difference 0 0) sourceC1576) = raw23793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23793; decide +kernel
    rw [ha]
    exact (canonical23793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 1) (sourceB1576 + difference 1 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 1) (sourceB1576 + difference 1 0) sourceC1576) = raw23794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23794; decide +kernel
    rw [ha]
    exact (canonical23794 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 2) (sourceB1576 + difference 2 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 2) (sourceB1576 + difference 2 0) sourceC1576) = raw23795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23795; decide +kernel
    rw [ha]
    exact (canonical23795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 3) (sourceB1576 + difference 3 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 3) (sourceB1576 + difference 3 0) sourceC1576) = raw23796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23796; decide +kernel
    rw [ha]
    exact (canonical23796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 4) (sourceB1576 + difference 4 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 4) (sourceB1576 + difference 4 0) sourceC1576) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1576 + difference 0 5) (sourceB1576 + difference 5 0) sourceC1576) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA1576 + difference 0 5) (sourceB1576 + difference 5 0) sourceC1576) = raw23798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1576 sourceB1576 sourceC1576 difference raw23798; decide +kernel
    rw [ha]
    exact (canonical23798 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1576 + sourceB1576) sourceC1576) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1576 + sourceB1576) sourceC1576) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1576 sourceB1576 sourceC1576 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1576 sourceB1576 sourceC1576
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1576, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1577 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1577 + difference 0 4) (sourceB1577 + difference 4 0) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1577 + difference 0 4) (sourceB1577 + difference 4 0) sourceC1577) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1577 + difference 1 4) (sourceB1577 + difference 4 1) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1577 + difference 1 4) (sourceB1577 + difference 4 1) sourceC1577) = raw23800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23800; decide +kernel
    rw [ha]
    exact (canonical23800 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1577 + difference 2 4) (sourceB1577 + difference 4 2) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1577 + difference 2 4) (sourceB1577 + difference 4 2) sourceC1577) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1577 + difference 3 4) (sourceB1577 + difference 4 3) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1577 + difference 3 4) (sourceB1577 + difference 4 3) sourceC1577) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1577 + difference 4 4) (sourceB1577 + difference 4 4) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1577 + difference 4 4) (sourceB1577 + difference 4 4) sourceC1577) = raw23793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23793; decide +kernel
    rw [ha]
    exact (canonical23793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1577 + difference 5 4) (sourceB1577 + difference 4 5) sourceC1577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1577 + difference 5 4) (sourceB1577 + difference 4 5) sourceC1577) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1577 sourceB1577 sourceC1577 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1577 + sourceB1577) sourceC1577) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1577 + sourceB1577) sourceC1577) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1577 sourceB1577 sourceC1577 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1577 sourceB1577 sourceC1577
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1577, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1328 : Integer.Sparse.reindex keyMap MixedData.row1328 = numericRow1328 := by decide +kernel

theorem numericCheck1328 (x : Master → ℝ) : Integer.Sparse.eval numericRow1328 x =
    (1 : ℝ) * reducedSource1328 x := by
  norm_num [numericRow1328, reducedSource1328, Integer.Sparse.eval, Sparse.eval, nodeValue562, nodeValue724, nodeValue830, nodeValue852, nodeValue858, nodeValue4071]

theorem reindexCheck1329 : Integer.Sparse.reindex keyMap MixedData.row1329 = numericRow1329 := by decide +kernel

theorem numericCheck1329 (x : Master → ℝ) : Integer.Sparse.eval numericRow1329 x =
    (1 : ℝ) * reducedSource1329 x := by
  norm_num [numericRow1329, reducedSource1329, Integer.Sparse.eval, Sparse.eval, nodeValue831, nodeValue1612, nodeValue1661, nodeValue1739, nodeValue4069]

theorem reindexCheck1330 : Integer.Sparse.reindex keyMap MixedData.row1330 = numericRow1330 := by decide +kernel

theorem numericCheck1330 (x : Master → ℝ) : Integer.Sparse.eval numericRow1330 x =
    (1 : ℝ) * reducedSource1330 x := by
  norm_num [numericRow1330, reducedSource1330, Integer.Sparse.eval, Sparse.eval, nodeValue789, nodeValue1594, nodeValue1640, nodeValue1707, nodeValue1709, nodeValue4069]

theorem reindexCheck1331 : Integer.Sparse.reindex keyMap MixedData.row1331 = numericRow1331 := by decide +kernel

theorem numericCheck1331 (x : Master → ℝ) : Integer.Sparse.eval numericRow1331 x =
    (1 : ℝ) * reducedSource1331 x := by
  norm_num [numericRow1331, reducedSource1331, Integer.Sparse.eval, Sparse.eval, nodeValue543, nodeValue703, nodeValue738, nodeValue789, nodeValue806, nodeValue811, nodeValue4069]

theorem reindexCheck1332 : Integer.Sparse.reindex keyMap MixedData.row1332 = numericRow1332 := by decide +kernel

theorem numericCheck1332 (x : Master → ℝ) : Integer.Sparse.eval numericRow1332 x =
    (1 : ℝ) * reducedSource1332 x := by
  norm_num [numericRow1332, reducedSource1332, Integer.Sparse.eval, Sparse.eval, nodeValue552, nodeValue710, nodeValue823, nodeValue848, nodeValue852, nodeValue4071]

theorem reindexCheck1333 : Integer.Sparse.reindex keyMap MixedData.row1333 = numericRow1333 := by decide +kernel

theorem numericCheck1333 (x : Master → ℝ) : Integer.Sparse.eval numericRow1333 x =
    (1 : ℝ) * reducedSource1333 x := by
  norm_num [numericRow1333, reducedSource1333, Integer.Sparse.eval, Sparse.eval, nodeValue790, nodeValue1595, nodeValue1641, nodeValue1708, nodeValue4068]

theorem reindexCheck1334 : Integer.Sparse.reindex keyMap MixedData.row1334 = numericRow1334 := by decide +kernel

theorem numericCheck1334 (x : Master → ℝ) : Integer.Sparse.eval numericRow1334 x =
    (1 : ℝ) * reducedSource1334 x := by
  norm_num [numericRow1334, reducedSource1334, Integer.Sparse.eval, Sparse.eval, nodeValue544, nodeValue704, nodeValue739, nodeValue790, nodeValue810, nodeValue4068]

theorem reindexCheck1336 : Integer.Sparse.reindex keyMap MixedData.row1336 = numericRow1336 := by decide +kernel

theorem numericCheck1336 (x : Master → ℝ) : Integer.Sparse.eval numericRow1336 x =
    (1 : ℝ) * reducedSource1336 x := by
  norm_num [numericRow1336, reducedSource1336, Integer.Sparse.eval, Sparse.eval, nodeValue664, nodeValue684, nodeValue685, nodeValue689, nodeValue749, nodeValue763, nodeValue764, nodeValue768, nodeValue800, nodeValue806, nodeValue807, nodeValue843, nodeValue844, nodeValue851, nodeValue853, nodeValue856, nodeValue1000, nodeValue1075, nodeValue1082, nodeValue1083, nodeValue4069]

theorem reindexCheck1337 : Integer.Sparse.reindex keyMap MixedData.row1337 = numericRow1337 := by decide +kernel

theorem numericCheck1337 (x : Master → ℝ) : Integer.Sparse.eval numericRow1337 x =
    (1 : ℝ) * reducedSource1337 x := by
  norm_num [numericRow1337, reducedSource1337, Integer.Sparse.eval, Sparse.eval, nodeValue816, nodeValue1605, nodeValue1653, nodeValue1727, nodeValue1728, nodeValue4069]

theorem reindexCheck1338 : Integer.Sparse.reindex keyMap MixedData.row1338 = numericRow1338 := by decide +kernel

theorem numericCheck1338 (x : Master → ℝ) : Integer.Sparse.eval numericRow1338 x =
    (1 : ℝ) * reducedSource1338 x := by
  norm_num [numericRow1338, reducedSource1338, Integer.Sparse.eval, Sparse.eval, nodeValue539, nodeValue547, nodeValue548, nodeValue561, nodeValue816, nodeValue4069]

theorem reindexCheck1339 : Integer.Sparse.reindex keyMap MixedData.row1339 = numericRow1339 := by decide +kernel

theorem numericCheck1339 (x : Master → ℝ) : Integer.Sparse.eval numericRow1339 x =
    (1 : ℝ) * reducedSource1339 x := by
  norm_num [numericRow1339, reducedSource1339, Integer.Sparse.eval, Sparse.eval, nodeValue734, nodeValue742, nodeValue743, nodeValue816, nodeValue1653, nodeValue4069]

theorem reindexCheck1341 : Integer.Sparse.reindex keyMap MixedData.row1341 = numericRow1341 := by decide +kernel

theorem numericCheck1341 (x : Master → ℝ) : Integer.Sparse.eval numericRow1341 x =
    (1 : ℝ) * reducedSource1341 x := by
  norm_num [numericRow1341, reducedSource1341, Integer.Sparse.eval, Sparse.eval, nodeValue4059, nodeValue4061, nodeValue4065, nodeValue4067, nodeValue4069, nodeValue4070, nodeValue4082, nodeValue4084]

theorem reindexCheck1342 : Integer.Sparse.reindex keyMap MixedData.row1342 = numericRow1342 := by decide +kernel

theorem numericCheck1342 (x : Master → ℝ) : Integer.Sparse.eval numericRow1342 x =
    (1 : ℝ) * reducedSource1342 x := by
  norm_num [numericRow1342, reducedSource1342, Integer.Sparse.eval, Sparse.eval, nodeValue1716, nodeValue2521, nodeValue3022, nodeValue3049, nodeValue3305, nodeValue4069]

theorem reindexCheck1343 : Integer.Sparse.reindex keyMap MixedData.row1343 = numericRow1343 := by decide +kernel

theorem numericCheck1343 (x : Master → ℝ) : Integer.Sparse.eval numericRow1343 x =
    (1 : ℝ) * reducedSource1343 x := by
  norm_num [numericRow1343, reducedSource1343, Integer.Sparse.eval, Sparse.eval, nodeValue1714, nodeValue1716, nodeValue1728, nodeValue1739, nodeValue3305, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1328 (mixedVector B) = 0 := by
  have h562 : mixedVector B (Sum.inr 562) = Sparse.eval nodeValue562 (mixedVector B) := by
    change mixedMoment B node562 node562Labels = _
    exact sound562 B hB hF
  have h724 : mixedVector B (Sum.inr 724) = Sparse.eval nodeValue724 (mixedVector B) := by
    change mixedMoment B node724 node724Labels = _
    exact sound724 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1561, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h562, h724, h830, h852, h858, h4071, reducedSource1328] using sourceEq1561 B hB

theorem rowSound1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1328 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1328, numericCheck1328, reducedZero1328 B hB hF, mul_zero]

theorem reducedZero1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1329 (mixedVector B) = 0 := by
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h1612 : mixedVector B (Sum.inr 1612) = Sparse.eval nodeValue1612 (mixedVector B) := by
    change mixedMoment B node1612 node1612Labels = _
    exact sound1612 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1562, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h831, h1612, h1661, h1739, h4069, reducedSource1329] using sourceEq1562 B hB

theorem rowSound1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1329 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1329, numericCheck1329, reducedZero1329 B hB hF, mul_zero]

theorem reducedZero1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1330 (mixedVector B) = 0 := by
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h1594 : mixedVector B (Sum.inr 1594) = Sparse.eval nodeValue1594 (mixedVector B) := by
    change mixedMoment B node1594 node1594Labels = _
    exact sound1594 B hB hF
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1564, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h789, h1594, h1640, h1707, h1709, h4069, reducedSource1330] using sourceEq1564 B hB

theorem rowSound1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1330 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1330, numericCheck1330, reducedZero1330 B hB hF, mul_zero]

theorem reducedZero1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1331 (mixedVector B) = 0 := by
  have h543 : mixedVector B (Sum.inr 543) = Sparse.eval nodeValue543 (mixedVector B) := by
    change mixedMoment B node543 node543Labels = _
    exact sound543 B hB hF
  have h703 : mixedVector B (Sum.inr 703) = Sparse.eval nodeValue703 (mixedVector B) := by
    change mixedMoment B node703 node703Labels = _
    exact sound703 B hB hF
  have h738 : mixedVector B (Sum.inr 738) = Sparse.eval nodeValue738 (mixedVector B) := by
    change mixedMoment B node738 node738Labels = _
    exact sound738 B hB hF
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1565, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h543, h703, h738, h789, h806, h811, h4069, reducedSource1331] using sourceEq1565 B hB

theorem rowSound1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1331 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1331, numericCheck1331, reducedZero1331 B hB hF, mul_zero]

theorem reducedZero1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1332 (mixedVector B) = 0 := by
  have h552 : mixedVector B (Sum.inr 552) = Sparse.eval nodeValue552 (mixedVector B) := by
    change mixedMoment B node552 node552Labels = _
    exact sound552 B hB hF
  have h710 : mixedVector B (Sum.inr 710) = Sparse.eval nodeValue710 (mixedVector B) := by
    change mixedMoment B node710 node710Labels = _
    exact sound710 B hB hF
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1566, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h552, h710, h823, h848, h852, h4071, reducedSource1332] using sourceEq1566 B hB

theorem rowSound1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1332 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1332, numericCheck1332, reducedZero1332 B hB hF, mul_zero]

theorem reducedZero1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1333 (mixedVector B) = 0 := by
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h1595 : mixedVector B (Sum.inr 1595) = Sparse.eval nodeValue1595 (mixedVector B) := by
    change mixedMoment B node1595 node1595Labels = _
    exact sound1595 B hB hF
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1567, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h790, h1595, h1641, h1708, h4068, reducedSource1333] using sourceEq1567 B hB

theorem rowSound1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1333 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1333, numericCheck1333, reducedZero1333 B hB hF, mul_zero]

theorem reducedZero1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1334 (mixedVector B) = 0 := by
  have h544 : mixedVector B (Sum.inr 544) = Sparse.eval nodeValue544 (mixedVector B) := by
    change mixedMoment B node544 node544Labels = _
    exact sound544 B hB hF
  have h704 : mixedVector B (Sum.inr 704) = Sparse.eval nodeValue704 (mixedVector B) := by
    change mixedMoment B node704 node704Labels = _
    exact sound704 B hB hF
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1568, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h544, h704, h739, h790, h810, h4068, reducedSource1334] using sourceEq1568 B hB

theorem rowSound1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1334 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1334, numericCheck1334, reducedZero1334 B hB hF, mul_zero]

theorem reducedZero1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1336 (mixedVector B) = 0 := by
  have h664 : mixedVector B (Sum.inr 664) = Sparse.eval nodeValue664 (mixedVector B) := by
    change mixedMoment B node664 node664Labels = _
    exact sound664 B hB hF
  have h684 : mixedVector B (Sum.inr 684) = Sparse.eval nodeValue684 (mixedVector B) := by
    change mixedMoment B node684 node684Labels = _
    exact sound684 B hB hF
  have h685 : mixedVector B (Sum.inr 685) = Sparse.eval nodeValue685 (mixedVector B) := by
    change mixedMoment B node685 node685Labels = _
    exact sound685 B hB hF
  have h689 : mixedVector B (Sum.inr 689) = Sparse.eval nodeValue689 (mixedVector B) := by
    change mixedMoment B node689 node689Labels = _
    exact sound689 B hB hF
  have h749 : mixedVector B (Sum.inr 749) = Sparse.eval nodeValue749 (mixedVector B) := by
    change mixedMoment B node749 node749Labels = _
    exact sound749 B hB hF
  have h763 : mixedVector B (Sum.inr 763) = Sparse.eval nodeValue763 (mixedVector B) := by
    change mixedMoment B node763 node763Labels = _
    exact sound763 B hB hF
  have h764 : mixedVector B (Sum.inr 764) = Sparse.eval nodeValue764 (mixedVector B) := by
    change mixedMoment B node764 node764Labels = _
    exact sound764 B hB hF
  have h768 : mixedVector B (Sum.inr 768) = Sparse.eval nodeValue768 (mixedVector B) := by
    change mixedMoment B node768 node768Labels = _
    exact sound768 B hB hF
  have h800 : mixedVector B (Sum.inr 800) = Sparse.eval nodeValue800 (mixedVector B) := by
    change mixedMoment B node800 node800Labels = _
    exact sound800 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h843 : mixedVector B (Sum.inr 843) = Sparse.eval nodeValue843 (mixedVector B) := by
    change mixedMoment B node843 node843Labels = _
    exact sound843 B hB hF
  have h844 : mixedVector B (Sum.inr 844) = Sparse.eval nodeValue844 (mixedVector B) := by
    change mixedMoment B node844 node844Labels = _
    exact sound844 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1570, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h664, h684, h685, h689, h749, h763, h764, h768, h800, h806, h807, h843, h844, h851, h853, h856, h1000, h1075, h1082, h1083, h4069, reducedSource1336] using sourceEq1570 B hB

theorem rowSound1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1336 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1336, numericCheck1336, reducedZero1336 B hB hF, mul_zero]

theorem reducedZero1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1337 (mixedVector B) = 0 := by
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1571, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h816, h1605, h1653, h1727, h1728, h4069, reducedSource1337] using sourceEq1571 B hB

theorem rowSound1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1337 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1337, numericCheck1337, reducedZero1337 B hB hF, mul_zero]

theorem reducedZero1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1338 (mixedVector B) = 0 := by
  have h539 : mixedVector B (Sum.inr 539) = Sparse.eval nodeValue539 (mixedVector B) := by
    change mixedMoment B node539 node539Labels = _
    exact sound539 B hB hF
  have h547 : mixedVector B (Sum.inr 547) = Sparse.eval nodeValue547 (mixedVector B) := by
    change mixedMoment B node547 node547Labels = _
    exact sound547 B hB hF
  have h548 : mixedVector B (Sum.inr 548) = Sparse.eval nodeValue548 (mixedVector B) := by
    change mixedMoment B node548 node548Labels = _
    exact sound548 B hB hF
  have h561 : mixedVector B (Sum.inr 561) = Sparse.eval nodeValue561 (mixedVector B) := by
    change mixedMoment B node561 node561Labels = _
    exact sound561 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1572, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h539, h547, h548, h561, h816, h4069, reducedSource1338] using sourceEq1572 B hB

theorem rowSound1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1338 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1338, numericCheck1338, reducedZero1338 B hB hF, mul_zero]

theorem reducedZero1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1339 (mixedVector B) = 0 := by
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h742 : mixedVector B (Sum.inr 742) = Sparse.eval nodeValue742 (mixedVector B) := by
    change mixedMoment B node742 node742Labels = _
    exact sound742 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1573, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h734, h742, h743, h816, h1653, h4069, reducedSource1339] using sourceEq1573 B hB

theorem rowSound1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1339 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1339, numericCheck1339, reducedZero1339 B hB hF, mul_zero]

theorem reducedZero1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1341 (mixedVector B) = 0 := by
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1575, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4059, h4061, h4065, h4067, h4069, h4070, h4082, h4084, reducedSource1341] using sourceEq1575 B hB

theorem rowSound1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1341 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1341, numericCheck1341, reducedZero1341 B hB hF, mul_zero]

theorem reducedZero1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1342 (mixedVector B) = 0 := by
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1576, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1716, h2521, h3022, h3049, h3305, h4069, reducedSource1342] using sourceEq1576 B hB

theorem rowSound1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1342 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1342, numericCheck1342, reducedZero1342 B hB hF, mul_zero]

theorem reducedZero1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1343 (mixedVector B) = 0 := by
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1577, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1714, h1716, h1728, h1739, h3305, h4069, reducedSource1343] using sourceEq1577 B hB

theorem rowSound1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1343 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1343, numericCheck1343, reducedZero1343 B hB hF, mul_zero]

theorem sourceRowsAt1328 : MixedData.sourceRows (1328 : Fin 2425) =
    MixedData.row1328 := by decide +kernel

theorem sourceRowsAt1329 : MixedData.sourceRows (1329 : Fin 2425) =
    MixedData.row1329 := by decide +kernel

theorem sourceRowsAt1330 : MixedData.sourceRows (1330 : Fin 2425) =
    MixedData.row1330 := by decide +kernel

theorem sourceRowsAt1331 : MixedData.sourceRows (1331 : Fin 2425) =
    MixedData.row1331 := by decide +kernel

theorem sourceRowsAt1332 : MixedData.sourceRows (1332 : Fin 2425) =
    MixedData.row1332 := by decide +kernel

theorem sourceRowsAt1333 : MixedData.sourceRows (1333 : Fin 2425) =
    MixedData.row1333 := by decide +kernel

theorem sourceRowsAt1334 : MixedData.sourceRows (1334 : Fin 2425) =
    MixedData.row1334 := by decide +kernel

theorem sourceRowsAt1335 : MixedData.sourceRows (1335 : Fin 2425) =
    MixedData.row1335 := by decide +kernel

theorem sourceRowsAt1336 : MixedData.sourceRows (1336 : Fin 2425) =
    MixedData.row1336 := by decide +kernel

theorem sourceRowsAt1337 : MixedData.sourceRows (1337 : Fin 2425) =
    MixedData.row1337 := by decide +kernel

theorem sourceRowsAt1338 : MixedData.sourceRows (1338 : Fin 2425) =
    MixedData.row1338 := by decide +kernel

theorem sourceRowsAt1339 : MixedData.sourceRows (1339 : Fin 2425) =
    MixedData.row1339 := by decide +kernel

theorem sourceRowsAt1340 : MixedData.sourceRows (1340 : Fin 2425) =
    MixedData.row1340 := by decide +kernel

theorem sourceRowsAt1341 : MixedData.sourceRows (1341 : Fin 2425) =
    MixedData.row1341 := by decide +kernel

theorem sourceRowsAt1342 : MixedData.sourceRows (1342 : Fin 2425) =
    MixedData.row1342 := by decide +kernel

theorem sourceRowsAt1343 : MixedData.sourceRows (1343 : Fin 2425) =
    MixedData.row1343 := by decide +kernel

theorem chunkSound83_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 83) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1328 ∨ k.val = 1329 ∨ k.val = 1330 ∨ k.val = 1331 ∨ k.val = 1332 ∨ k.val = 1333 ∨ k.val = 1334 ∨ k.val = 1335 ∨ k.val = 1336 ∨ k.val = 1337 ∨ k.val = 1338 ∨ k.val = 1339 ∨ k.val = 1340 ∨ k.val = 1341 ∨ k.val = 1342 ∨ k.val = 1343 := by omega
  rcases heq with h1328 | h1329 | h1330 | h1331 | h1332 | h1333 | h1334 | h1335 | h1336 | h1337 | h1338 | h1339 | h1340 | h1341 | h1342 | h1343
  · have he : k = (1328 : Fin 2425) := Fin.ext h1328
    subst k
    rw [sourceRowsAt1328]
    exact rowSound1328 B hB hF
  · have he : k = (1329 : Fin 2425) := Fin.ext h1329
    subst k
    rw [sourceRowsAt1329]
    exact rowSound1329 B hB hF
  · have he : k = (1330 : Fin 2425) := Fin.ext h1330
    subst k
    rw [sourceRowsAt1330]
    exact rowSound1330 B hB hF
  · have he : k = (1331 : Fin 2425) := Fin.ext h1331
    subst k
    rw [sourceRowsAt1331]
    exact rowSound1331 B hB hF
  · have he : k = (1332 : Fin 2425) := Fin.ext h1332
    subst k
    rw [sourceRowsAt1332]
    exact rowSound1332 B hB hF
  · have he : k = (1333 : Fin 2425) := Fin.ext h1333
    subst k
    rw [sourceRowsAt1333]
    exact rowSound1333 B hB hF
  · have he : k = (1334 : Fin 2425) := Fin.ext h1334
    subst k
    rw [sourceRowsAt1334]
    exact rowSound1334 B hB hF
  · have he : k = (1335 : Fin 2425) := Fin.ext h1335
    subst k
    rw [sourceRowsAt1335]
    exact rowSound1335_e B hB hF
  · have he : k = (1336 : Fin 2425) := Fin.ext h1336
    subst k
    rw [sourceRowsAt1336]
    exact rowSound1336 B hB hF
  · have he : k = (1337 : Fin 2425) := Fin.ext h1337
    subst k
    rw [sourceRowsAt1337]
    exact rowSound1337 B hB hF
  · have he : k = (1338 : Fin 2425) := Fin.ext h1338
    subst k
    rw [sourceRowsAt1338]
    exact rowSound1338 B hB hF
  · have he : k = (1339 : Fin 2425) := Fin.ext h1339
    subst k
    rw [sourceRowsAt1339]
    exact rowSound1339 B hB hF
  · have he : k = (1340 : Fin 2425) := Fin.ext h1340
    subst k
    rw [sourceRowsAt1340]
    exact rowSound1340_e B hB hF
  · have he : k = (1341 : Fin 2425) := Fin.ext h1341
    subst k
    rw [sourceRowsAt1341]
    exact rowSound1341 B hB hF
  · have he : k = (1342 : Fin 2425) := Fin.ext h1342
    subst k
    rw [sourceRowsAt1342]
    exact rowSound1342 B hB hF
  · have he : k = (1343 : Fin 2425) := Fin.ext h1343
    subst k
    rw [sourceRowsAt1343]
    exact rowSound1343 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e_oai
