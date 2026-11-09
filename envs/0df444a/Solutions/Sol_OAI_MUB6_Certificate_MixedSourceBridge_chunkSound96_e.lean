-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:54:34.423304+00:00
-- url     : https://prove2.me/submissions/4e301657-6033-4ff7-ba57-e75ef1762946

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1536_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1539_e

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

theorem canonical14360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14360 raw14360Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14360 raw14360Labels = mixedMoment B raw14360step0 raw14360step0Labels := by
      have hz : ∀ j, raw14360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14360step0 = (fun i j => raw14360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14360step0 raw14360; decide +kernel
      have hl : raw14360step0Labels = raw14360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14360 raw14360Labels permutation346 hz
    mixedMoment B raw14360step0 raw14360step0Labels = mixedMoment B raw14360step1 raw14360step1Labels := by
      have hz : ∀ i, raw14360step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14360step1 = (fun i j => raw14360step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14360step1 raw14360step0; decide +kernel
      have hl : raw14360step1Labels = (fun j => raw14360step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14360step0 raw14360step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical14364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14364 raw14364Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14364 raw14364Labels = mixedMoment B raw14364step0 raw14364step0Labels := by
      have hz : ∀ j, raw14364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14364step0 = (fun i j => raw14364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14364step0 raw14364; decide +kernel
      have hl : raw14364step0Labels = raw14364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14364 raw14364Labels permutation265 hz
    mixedMoment B raw14364step0 raw14364step0Labels = mixedMoment B raw14364step1 raw14364step1Labels := by
      have hz : ∀ i, raw14364step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14364step1 = (fun i j => raw14364step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14364step1 raw14364step0; decide +kernel
      have hl : raw14364step1Labels = (fun j => raw14364step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14364step0 raw14364step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical14368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14368 raw14368Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14368 raw14368Labels = mixedMoment B raw14368step0 raw14368step0Labels := by
      have hz : ∀ j, raw14368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14368step0 = (fun i j => raw14368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14368step0 raw14368; decide +kernel
      have hl : raw14368step0Labels = raw14368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368 raw14368Labels permutation346 hz
    mixedMoment B raw14368step0 raw14368step0Labels = mixedMoment B raw14368step1 raw14368step1Labels := by
      have hz : ∀ j, raw14368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14368step1 = (fun i j => raw14368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14368step1 raw14368step0; decide +kernel
      have hl : raw14368step1Labels = raw14368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368step0 raw14368step0Labels permutation56 hz
    mixedMoment B raw14368step1 raw14368step1Labels = mixedMoment B raw14368step2 raw14368step2Labels := by
      have hz : ∀ i, raw14368step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14368step2 = (fun i j => raw14368step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14368step2 raw14368step1; decide +kernel
      have hl : raw14368step2Labels = (fun j => raw14368step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14368step1 raw14368step1Labels permutation6 hz
    mixedMoment B raw14368step2 raw14368step2Labels = mixedMoment B raw14368step3 raw14368step3Labels := by
      have ha : raw14368step3 = (fun i j => raw14368step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14368step3 raw14368step2; decide +kernel
      have hl : raw14368step3Labels = raw14368step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14368step2 raw14368step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19472 raw19472Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19472 raw19472Labels = mixedMoment B raw19472step0 raw19472step0Labels := by
      have hz : ∀ j, raw19472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19472step0 = (fun i j => raw19472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19472step0 raw19472; decide +kernel
      have hl : raw19472step0Labels = raw19472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472 raw19472Labels permutation434 hz
    mixedMoment B raw19472step0 raw19472step0Labels = mixedMoment B raw19472step1 raw19472step1Labels := by
      have hz : ∀ j, raw19472step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19472step1 = (fun i j => raw19472step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19472step1 raw19472step0; decide +kernel
      have hl : raw19472step1Labels = raw19472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472step0 raw19472step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21461 raw21461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21461 raw21461Labels = mixedMoment B raw21461step0 raw21461step0Labels := by
      have hz : ∀ j, raw21461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21461step0 = (fun i j => raw21461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21461step0 raw21461; decide +kernel
      have hl : raw21461step0Labels = raw21461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461 raw21461Labels permutation520 hz
    mixedMoment B raw21461step0 raw21461step0Labels = mixedMoment B raw21461step1 raw21461step1Labels := by
      have hz : ∀ j, raw21461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21461step1 = (fun i j => raw21461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21461step1 raw21461step0; decide +kernel
      have hl : raw21461step1Labels = raw21461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step0 raw21461step0Labels permutation104 hz
    mixedMoment B raw21461step1 raw21461step1Labels = mixedMoment B raw21461step2 raw21461step2Labels := by
      have hz : ∀ j, raw21461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21461step2 = (fun i j => raw21461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21461step2 raw21461step1; decide +kernel
      have hl : raw21461step2Labels = raw21461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step1 raw21461step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical22307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22307 raw22307Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22307 raw22307Labels = mixedMoment B raw22307step0 raw22307step0Labels := by
      have hz : ∀ j, raw22307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22307step0 = (fun i j => raw22307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22307step0 raw22307; decide +kernel
      have hl : raw22307step0Labels = raw22307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307 raw22307Labels permutation346 hz
    mixedMoment B raw22307step0 raw22307step0Labels = mixedMoment B raw22307step1 raw22307step1Labels := by
      have hz : ∀ j, raw22307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22307step1 = (fun i j => raw22307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22307step1 raw22307step0; decide +kernel
      have hl : raw22307step1Labels = raw22307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307step0 raw22307step0Labels permutation56 hz
    mixedMoment B raw22307step1 raw22307step1Labels = mixedMoment B raw22307step2 raw22307step2Labels := by
      have hz : ∀ i, raw22307step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22307step2 = (fun i j => raw22307step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22307step2 raw22307step1; decide +kernel
      have hl : raw22307step2Labels = (fun j => raw22307step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22307step1 raw22307step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

theorem canonical22308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22308 raw22308Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22308 raw22308Labels = mixedMoment B raw22308step0 raw22308step0Labels := by
      have hz : ∀ j, raw22308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22308step0 = (fun i j => raw22308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22308step0 raw22308; decide +kernel
      have hl : raw22308step0Labels = raw22308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22308 raw22308Labels permutation346 hz
    mixedMoment B raw22308step0 raw22308step0Labels = mixedMoment B raw22308step1 raw22308step1Labels := by
      have hz : ∀ i, raw22308step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22308step1 = (fun i j => raw22308step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22308step1 raw22308step0; decide +kernel
      have hl : raw22308step1Labels = (fun j => raw22308step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22308step0 raw22308step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical22309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22309 raw22309Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22309 raw22309Labels = mixedMoment B raw22309step0 raw22309step0Labels := by
      have hz : ∀ j, raw22309 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22309step0 = (fun i j => raw22309 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22309step0 raw22309; decide +kernel
      have hl : raw22309step0Labels = raw22309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22309 raw22309Labels permutation265 hz
    mixedMoment B raw22309step0 raw22309step0Labels = mixedMoment B raw22309step1 raw22309step1Labels := by
      have hz : ∀ i, raw22309step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22309step1 = (fun i j => raw22309step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22309step1 raw22309step0; decide +kernel
      have hl : raw22309step1Labels = (fun j => raw22309step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22309step0 raw22309step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25420 raw25420Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25420 raw25420Labels = mixedMoment B raw25420step0 raw25420step0Labels := by
      have hz : ∀ j, raw25420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25420step0 = (fun i j => raw25420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25420step0 raw25420; decide +kernel
      have hl : raw25420step0Labels = raw25420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25420 raw25420Labels permutation346 hz
    mixedMoment B raw25420step0 raw25420step0Labels = mixedMoment B raw25420step1 raw25420step1Labels := by
      have ha : raw25420step1 = (fun i j => raw25420step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25420step1 raw25420step0; decide +kernel
      have hl : raw25420step1Labels = raw25420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25420step0 raw25420step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical25426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25426 raw25426Labels = mixedMoment B node1038 node1038Labels := by
  calc
    _ = mixedMoment B node1038 node1038Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26244 raw26244Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26244 raw26244Labels = mixedMoment B raw26244step0 raw26244step0Labels := by
      have hz : ∀ j, raw26244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26244step0 = (fun i j => raw26244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26244step0 raw26244; decide +kernel
      have hl : raw26244step0Labels = raw26244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26244 raw26244Labels permutation346 hz
    mixedMoment B raw26244step0 raw26244step0Labels = mixedMoment B raw26244step1 raw26244step1Labels := by
      have ha : raw26244step1 = (fun i j => raw26244step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26244step1 raw26244step0; decide +kernel
      have hl : raw26244step1Labels = raw26244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26244step0 raw26244step0Labels permutation32 permutation7
    mixedMoment B raw26244step1 raw26244step1Labels = mixedMoment B raw26244step2 raw26244step2Labels := by
      have ha : raw26244step2 = -raw26244step1 := by apply Matrix.ext; change ∀ i j, raw26244step2 i j = -(raw26244step1 i j); unfold raw26244step2 raw26244step1; decide +kernel
      have hl : raw26244step2Labels = raw26244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26244step2 raw26244step2Labels = mixedMoment B raw26244step3 raw26244step3Labels := by
      have ha : raw26244step3 = raw26244step2 := by apply Matrix.ext; unfold raw26244step3 raw26244step2; decide +kernel
      have hl : raw26244step2Labels = labelEmbedding1 ∘ raw26244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26244step2 raw26244step2Labels raw26244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical26245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26245 raw26245Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26245 raw26245Labels = mixedMoment B raw26245step0 raw26245step0Labels := by
      have ha : raw26245step0 = (fun i j => raw26245 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26245step0 raw26245; decide +kernel
      have hl : raw26245step0Labels = raw26245Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26245 raw26245Labels permutation176 permutation7
    mixedMoment B raw26245step0 raw26245step0Labels = mixedMoment B raw26245step1 raw26245step1Labels := by
      have ha : raw26245step1 = -raw26245step0 := by apply Matrix.ext; change ∀ i j, raw26245step1 i j = -(raw26245step0 i j); unfold raw26245step1 raw26245step0; decide +kernel
      have hl : raw26245step1Labels = raw26245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26245step1 raw26245step1Labels = mixedMoment B raw26245step2 raw26245step2Labels := by
      have ha : raw26245step2 = raw26245step1 := by apply Matrix.ext; unfold raw26245step2 raw26245step1; decide +kernel
      have hl : raw26245step1Labels = labelEmbedding1 ∘ raw26245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26245step1 raw26245step1Labels raw26245step2Labels labelEmbedding1 hl
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical26246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26246 raw26246Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26246 raw26246Labels = mixedMoment B raw26246step0 raw26246step0Labels := by
      have hz : ∀ j, raw26246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26246step0 = (fun i j => raw26246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26246step0 raw26246; decide +kernel
      have hl : raw26246step0Labels = raw26246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26246 raw26246Labels permutation346 hz
    mixedMoment B raw26246step0 raw26246step0Labels = mixedMoment B raw26246step1 raw26246step1Labels := by
      have ha : raw26246step1 = (fun i j => raw26246step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26246step1 raw26246step0; decide +kernel
      have hl : raw26246step1Labels = raw26246step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26246step0 raw26246step0Labels permutation32 permutation7
    mixedMoment B raw26246step1 raw26246step1Labels = mixedMoment B raw26246step2 raw26246step2Labels := by
      have ha : raw26246step2 = -raw26246step1 := by apply Matrix.ext; change ∀ i j, raw26246step2 i j = -(raw26246step1 i j); unfold raw26246step2 raw26246step1; decide +kernel
      have hl : raw26246step2Labels = raw26246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26246step2 raw26246step2Labels = mixedMoment B raw26246step3 raw26246step3Labels := by
      have ha : raw26246step3 = raw26246step2 := by apply Matrix.ext; unfold raw26246step3 raw26246step2; decide +kernel
      have hl : raw26246step2Labels = labelEmbedding1 ∘ raw26246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26246step2 raw26246step2Labels raw26246step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical26247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26247 raw26247Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26247 raw26247Labels = mixedMoment B raw26247step0 raw26247step0Labels := by
      have hz : ∀ j, raw26247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26247step0 = (fun i j => raw26247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26247step0 raw26247; decide +kernel
      have hl : raw26247step0Labels = raw26247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26247 raw26247Labels permutation346 hz
    mixedMoment B raw26247step0 raw26247step0Labels = mixedMoment B raw26247step1 raw26247step1Labels := by
      have ha : raw26247step1 = (fun i j => raw26247step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26247step1 raw26247step0; decide +kernel
      have hl : raw26247step1Labels = raw26247step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26247step0 raw26247step0Labels permutation34 permutation7
    mixedMoment B raw26247step1 raw26247step1Labels = mixedMoment B raw26247step2 raw26247step2Labels := by
      have ha : raw26247step2 = -raw26247step1 := by apply Matrix.ext; change ∀ i j, raw26247step2 i j = -(raw26247step1 i j); unfold raw26247step2 raw26247step1; decide +kernel
      have hl : raw26247step2Labels = raw26247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26247step2 raw26247step2Labels = mixedMoment B raw26247step3 raw26247step3Labels := by
      have ha : raw26247step3 = raw26247step2 := by apply Matrix.ext; unfold raw26247step3 raw26247step2; decide +kernel
      have hl : raw26247step2Labels = labelEmbedding1 ∘ raw26247step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26247step2 raw26247step2Labels raw26247step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical26248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26248 raw26248Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26248 raw26248Labels = mixedMoment B raw26248step0 raw26248step0Labels := by
      have hz : ∀ j, raw26248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26248step0 = (fun i j => raw26248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26248step0 raw26248; decide +kernel
      have hl : raw26248step0Labels = raw26248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26248 raw26248Labels permutation346 hz
    mixedMoment B raw26248step0 raw26248step0Labels = mixedMoment B raw26248step1 raw26248step1Labels := by
      have ha : raw26248step1 = (fun i j => raw26248step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26248step1 raw26248step0; decide +kernel
      have hl : raw26248step1Labels = raw26248step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26248step0 raw26248step0Labels permutation32 permutation7
    mixedMoment B raw26248step1 raw26248step1Labels = mixedMoment B raw26248step2 raw26248step2Labels := by
      have ha : raw26248step2 = -raw26248step1 := by apply Matrix.ext; change ∀ i j, raw26248step2 i j = -(raw26248step1 i j); unfold raw26248step2 raw26248step1; decide +kernel
      have hl : raw26248step2Labels = raw26248step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26248step2 raw26248step2Labels = mixedMoment B raw26248step3 raw26248step3Labels := by
      have ha : raw26248step3 = raw26248step2 := by apply Matrix.ext; unfold raw26248step3 raw26248step2; decide +kernel
      have hl : raw26248step2Labels = labelEmbedding1 ∘ raw26248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26248step2 raw26248step2Labels raw26248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical26249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26249 raw26249Labels = mixedMoment B node687 node687Labels := by
  calc
    mixedMoment B raw26249 raw26249Labels = mixedMoment B raw26249step0 raw26249step0Labels := by
      have hz : ∀ j, raw26249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26249step0 = (fun i j => raw26249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26249step0 raw26249; decide +kernel
      have hl : raw26249step0Labels = raw26249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26249 raw26249Labels permutation346 hz
    mixedMoment B raw26249step0 raw26249step0Labels = mixedMoment B raw26249step1 raw26249step1Labels := by
      have ha : raw26249step1 = (fun i j => raw26249step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26249step1 raw26249step0; decide +kernel
      have hl : raw26249step1Labels = raw26249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26249step0 raw26249step0Labels permutation32 permutation7
    mixedMoment B raw26249step1 raw26249step1Labels = mixedMoment B raw26249step2 raw26249step2Labels := by
      have ha : raw26249step2 = -raw26249step1 := by apply Matrix.ext; change ∀ i j, raw26249step2 i j = -(raw26249step1 i j); unfold raw26249step2 raw26249step1; decide +kernel
      have hl : raw26249step2Labels = raw26249step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26249step2 raw26249step2Labels = mixedMoment B raw26249step3 raw26249step3Labels := by
      have ha : raw26249step3 = raw26249step2 := by apply Matrix.ext; unfold raw26249step3 raw26249step2; decide +kernel
      have hl : raw26249step2Labels = labelEmbedding1 ∘ raw26249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26249step2 raw26249step2Labels raw26249step3Labels labelEmbedding1 hl
    _ = mixedMoment B node687 node687Labels := by rfl

theorem canonical26250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26250 raw26250Labels = mixedMoment B node766 node766Labels := by
  calc
    mixedMoment B raw26250 raw26250Labels = mixedMoment B raw26250step0 raw26250step0Labels := by
      have ha : raw26250step0 = (fun i j => raw26250 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26250step0 raw26250; decide +kernel
      have hl : raw26250step0Labels = raw26250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26250 raw26250Labels permutation176 permutation7
    mixedMoment B raw26250step0 raw26250step0Labels = mixedMoment B raw26250step1 raw26250step1Labels := by
      have ha : raw26250step1 = -raw26250step0 := by apply Matrix.ext; change ∀ i j, raw26250step1 i j = -(raw26250step0 i j); unfold raw26250step1 raw26250step0; decide +kernel
      have hl : raw26250step1Labels = raw26250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26250step1 raw26250step1Labels = mixedMoment B raw26250step2 raw26250step2Labels := by
      have ha : raw26250step2 = raw26250step1 := by apply Matrix.ext; unfold raw26250step2 raw26250step1; decide +kernel
      have hl : raw26250step1Labels = labelEmbedding1 ∘ raw26250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26250step1 raw26250step1Labels raw26250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node766 node766Labels := by rfl

theorem canonical26251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26251 raw26251Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26251 raw26251Labels = mixedMoment B raw26251step0 raw26251step0Labels := by
      have hz : ∀ j, raw26251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26251step0 = (fun i j => raw26251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26251step0 raw26251; decide +kernel
      have hl : raw26251step0Labels = raw26251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26251 raw26251Labels permutation346 hz
    mixedMoment B raw26251step0 raw26251step0Labels = mixedMoment B raw26251step1 raw26251step1Labels := by
      have ha : raw26251step1 = (fun i j => raw26251step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26251step1 raw26251step0; decide +kernel
      have hl : raw26251step1Labels = raw26251step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26251step0 raw26251step0Labels permutation38 permutation7
    mixedMoment B raw26251step1 raw26251step1Labels = mixedMoment B raw26251step2 raw26251step2Labels := by
      have ha : raw26251step2 = -raw26251step1 := by apply Matrix.ext; change ∀ i j, raw26251step2 i j = -(raw26251step1 i j); unfold raw26251step2 raw26251step1; decide +kernel
      have hl : raw26251step2Labels = raw26251step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26251step2 raw26251step2Labels = mixedMoment B raw26251step3 raw26251step3Labels := by
      have ha : raw26251step3 = raw26251step2 := by apply Matrix.ext; unfold raw26251step3 raw26251step2; decide +kernel
      have hl : raw26251step2Labels = labelEmbedding1 ∘ raw26251step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26251step2 raw26251step2Labels raw26251step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

theorem canonical26252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26252 raw26252Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26252 raw26252Labels = mixedMoment B raw26252step0 raw26252step0Labels := by
      have hz : ∀ j, raw26252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26252step0 = (fun i j => raw26252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26252step0 raw26252; decide +kernel
      have hl : raw26252step0Labels = raw26252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26252 raw26252Labels permutation346 hz
    mixedMoment B raw26252step0 raw26252step0Labels = mixedMoment B raw26252step1 raw26252step1Labels := by
      have ha : raw26252step1 = (fun i j => raw26252step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26252step1 raw26252step0; decide +kernel
      have hl : raw26252step1Labels = raw26252step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26252step0 raw26252step0Labels permutation44 permutation7
    mixedMoment B raw26252step1 raw26252step1Labels = mixedMoment B raw26252step2 raw26252step2Labels := by
      have ha : raw26252step2 = -raw26252step1 := by apply Matrix.ext; change ∀ i j, raw26252step2 i j = -(raw26252step1 i j); unfold raw26252step2 raw26252step1; decide +kernel
      have hl : raw26252step2Labels = raw26252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26252step2 raw26252step2Labels = mixedMoment B raw26252step3 raw26252step3Labels := by
      have ha : raw26252step3 = raw26252step2 := by apply Matrix.ext; unfold raw26252step3 raw26252step2; decide +kernel
      have hl : raw26252step2Labels = labelEmbedding1 ∘ raw26252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26252step2 raw26252step2Labels raw26252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

theorem canonical26253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26253 raw26253Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26253 raw26253Labels = mixedMoment B raw26253step0 raw26253step0Labels := by
      have hz : ∀ j, raw26253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26253step0 = (fun i j => raw26253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26253step0 raw26253; decide +kernel
      have hl : raw26253step0Labels = raw26253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26253 raw26253Labels permutation346 hz
    mixedMoment B raw26253step0 raw26253step0Labels = mixedMoment B raw26253step1 raw26253step1Labels := by
      have hz : ∀ i, raw26253step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26253step1 = (fun i j => raw26253step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26253step1 raw26253step0; decide +kernel
      have hl : raw26253step1Labels = (fun j => raw26253step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26253step0 raw26253step0Labels permutation4 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical26254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26254 raw26254Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw26254 raw26254Labels = mixedMoment B raw26254step0 raw26254step0Labels := by
      have ha : raw26254step0 = (fun i j => raw26254 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26254step0 raw26254; decide +kernel
      have hl : raw26254step0Labels = raw26254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26254 raw26254Labels permutation176 permutation7
    mixedMoment B raw26254step0 raw26254step0Labels = mixedMoment B raw26254step1 raw26254step1Labels := by
      have ha : raw26254step1 = -raw26254step0 := by apply Matrix.ext; change ∀ i j, raw26254step1 i j = -(raw26254step0 i j); unfold raw26254step1 raw26254step0; decide +kernel
      have hl : raw26254step1Labels = raw26254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26254step1 raw26254step1Labels = mixedMoment B raw26254step2 raw26254step2Labels := by
      have ha : raw26254step2 = raw26254step1 := by apply Matrix.ext; unfold raw26254step2 raw26254step1; decide +kernel
      have hl : raw26254step1Labels = labelEmbedding1 ∘ raw26254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26254step1 raw26254step1Labels raw26254step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

theorem canonical26255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26255 raw26255Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw26255 raw26255Labels = mixedMoment B raw26255step0 raw26255step0Labels := by
      have ha : raw26255step0 = (fun i j => raw26255 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26255step0 raw26255; decide +kernel
      have hl : raw26255step0Labels = raw26255Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26255 raw26255Labels permutation176 permutation7
    mixedMoment B raw26255step0 raw26255step0Labels = mixedMoment B raw26255step1 raw26255step1Labels := by
      have ha : raw26255step1 = -raw26255step0 := by apply Matrix.ext; change ∀ i j, raw26255step1 i j = -(raw26255step0 i j); unfold raw26255step1 raw26255step0; decide +kernel
      have hl : raw26255step1Labels = raw26255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26255step1 raw26255step1Labels = mixedMoment B raw26255step2 raw26255step2Labels := by
      have ha : raw26255step2 = raw26255step1 := by apply Matrix.ext; unfold raw26255step2 raw26255step1; decide +kernel
      have hl : raw26255step1Labels = labelEmbedding1 ∘ raw26255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26255step1 raw26255step1Labels raw26255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

theorem canonical26256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26256 raw26256Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw26256 raw26256Labels = mixedMoment B raw26256step0 raw26256step0Labels := by
      have ha : raw26256step0 = (fun i j => raw26256 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26256step0 raw26256; decide +kernel
      have hl : raw26256step0Labels = raw26256Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26256 raw26256Labels permutation176 permutation7
    mixedMoment B raw26256step0 raw26256step0Labels = mixedMoment B raw26256step1 raw26256step1Labels := by
      have ha : raw26256step1 = -raw26256step0 := by apply Matrix.ext; change ∀ i j, raw26256step1 i j = -(raw26256step0 i j); unfold raw26256step1 raw26256step0; decide +kernel
      have hl : raw26256step1Labels = raw26256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26256step1 raw26256step1Labels = mixedMoment B raw26256step2 raw26256step2Labels := by
      have ha : raw26256step2 = raw26256step1 := by apply Matrix.ext; unfold raw26256step2 raw26256step1; decide +kernel
      have hl : raw26256step1Labels = labelEmbedding1 ∘ raw26256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26256step1 raw26256step1Labels raw26256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical26257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26257 raw26257Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw26257 raw26257Labels = mixedMoment B raw26257step0 raw26257step0Labels := by
      have ha : raw26257step0 = (fun i j => raw26257 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26257step0 raw26257; decide +kernel
      have hl : raw26257step0Labels = raw26257Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26257 raw26257Labels permutation178 permutation7
    mixedMoment B raw26257step0 raw26257step0Labels = mixedMoment B raw26257step1 raw26257step1Labels := by
      have ha : raw26257step1 = -raw26257step0 := by apply Matrix.ext; change ∀ i j, raw26257step1 i j = -(raw26257step0 i j); unfold raw26257step1 raw26257step0; decide +kernel
      have hl : raw26257step1Labels = raw26257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26257step1 raw26257step1Labels = mixedMoment B raw26257step2 raw26257step2Labels := by
      have ha : raw26257step2 = raw26257step1 := by apply Matrix.ext; unfold raw26257step2 raw26257step1; decide +kernel
      have hl : raw26257step1Labels = labelEmbedding1 ∘ raw26257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26257step1 raw26257step1Labels raw26257step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical26258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26258 raw26258Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26258 raw26258Labels = mixedMoment B raw26258step0 raw26258step0Labels := by
      have ha : raw26258step0 = (fun i j => raw26258 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26258step0 raw26258; decide +kernel
      have hl : raw26258step0Labels = raw26258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26258 raw26258Labels permutation176 permutation7
    mixedMoment B raw26258step0 raw26258step0Labels = mixedMoment B raw26258step1 raw26258step1Labels := by
      have ha : raw26258step1 = -raw26258step0 := by apply Matrix.ext; change ∀ i j, raw26258step1 i j = -(raw26258step0 i j); unfold raw26258step1 raw26258step0; decide +kernel
      have hl : raw26258step1Labels = raw26258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26258step1 raw26258step1Labels = mixedMoment B raw26258step2 raw26258step2Labels := by
      have ha : raw26258step2 = raw26258step1 := by apply Matrix.ext; unfold raw26258step2 raw26258step1; decide +kernel
      have hl : raw26258step1Labels = labelEmbedding1 ∘ raw26258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26258step1 raw26258step1Labels raw26258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node805 node805Labels := by rfl

theorem canonical26259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26259 raw26259Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw26259 raw26259Labels = mixedMoment B raw26259step0 raw26259step0Labels := by
      have hz : ∀ j, raw26259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26259step0 = (fun i j => raw26259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26259step0 raw26259; decide +kernel
      have hl : raw26259step0Labels = raw26259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26259 raw26259Labels permutation346 hz
    mixedMoment B raw26259step0 raw26259step0Labels = mixedMoment B raw26259step1 raw26259step1Labels := by
      have ha : raw26259step1 = (fun i j => raw26259step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26259step1 raw26259step0; decide +kernel
      have hl : raw26259step1Labels = raw26259step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26259step0 raw26259step0Labels permutation34 permutation7
    mixedMoment B raw26259step1 raw26259step1Labels = mixedMoment B raw26259step2 raw26259step2Labels := by
      have ha : raw26259step2 = -raw26259step1 := by apply Matrix.ext; change ∀ i j, raw26259step2 i j = -(raw26259step1 i j); unfold raw26259step2 raw26259step1; decide +kernel
      have hl : raw26259step2Labels = raw26259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26259step2 raw26259step2Labels = mixedMoment B raw26259step3 raw26259step3Labels := by
      have ha : raw26259step3 = raw26259step2 := by apply Matrix.ext; unfold raw26259step3 raw26259step2; decide +kernel
      have hl : raw26259step2Labels = labelEmbedding1 ∘ raw26259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26259step2 raw26259step2Labels raw26259step3Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

theorem canonical26260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26260 raw26260Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw26260 raw26260Labels = mixedMoment B raw26260step0 raw26260step0Labels := by
      have hz : ∀ j, raw26260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26260step0 = (fun i j => raw26260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26260step0 raw26260; decide +kernel
      have hl : raw26260step0Labels = raw26260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26260 raw26260Labels permutation346 hz
    mixedMoment B raw26260step0 raw26260step0Labels = mixedMoment B raw26260step1 raw26260step1Labels := by
      have ha : raw26260step1 = (fun i j => raw26260step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26260step1 raw26260step0; decide +kernel
      have hl : raw26260step1Labels = raw26260step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26260step0 raw26260step0Labels permutation34 permutation7
    mixedMoment B raw26260step1 raw26260step1Labels = mixedMoment B raw26260step2 raw26260step2Labels := by
      have ha : raw26260step2 = -raw26260step1 := by apply Matrix.ext; change ∀ i j, raw26260step2 i j = -(raw26260step1 i j); unfold raw26260step2 raw26260step1; decide +kernel
      have hl : raw26260step2Labels = raw26260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26260step2 raw26260step2Labels = mixedMoment B raw26260step3 raw26260step3Labels := by
      have ha : raw26260step3 = raw26260step2 := by apply Matrix.ext; unfold raw26260step3 raw26260step2; decide +kernel
      have hl : raw26260step2Labels = labelEmbedding1 ∘ raw26260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26260step2 raw26260step2Labels raw26260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

theorem canonical26261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26261 raw26261Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw26261 raw26261Labels = mixedMoment B raw26261step0 raw26261step0Labels := by
      have ha : raw26261step0 = (fun i j => raw26261 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26261step0 raw26261; decide +kernel
      have hl : raw26261step0Labels = raw26261Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26261 raw26261Labels permutation178 permutation7
    mixedMoment B raw26261step0 raw26261step0Labels = mixedMoment B raw26261step1 raw26261step1Labels := by
      have ha : raw26261step1 = -raw26261step0 := by apply Matrix.ext; change ∀ i j, raw26261step1 i j = -(raw26261step0 i j); unfold raw26261step1 raw26261step0; decide +kernel
      have hl : raw26261step1Labels = raw26261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26261step1 raw26261step1Labels = mixedMoment B raw26261step2 raw26261step2Labels := by
      have ha : raw26261step2 = raw26261step1 := by apply Matrix.ext; unfold raw26261step2 raw26261step1; decide +kernel
      have hl : raw26261step1Labels = labelEmbedding1 ∘ raw26261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26261step1 raw26261step1Labels raw26261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

theorem canonical26262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26262 raw26262Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw26262 raw26262Labels = mixedMoment B raw26262step0 raw26262step0Labels := by
      have hz : ∀ j, raw26262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26262step0 = (fun i j => raw26262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26262step0 raw26262; decide +kernel
      have hl : raw26262step0Labels = raw26262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26262 raw26262Labels permutation346 hz
    mixedMoment B raw26262step0 raw26262step0Labels = mixedMoment B raw26262step1 raw26262step1Labels := by
      have ha : raw26262step1 = (fun i j => raw26262step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26262step1 raw26262step0; decide +kernel
      have hl : raw26262step1Labels = raw26262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26262step0 raw26262step0Labels permutation34 permutation7
    mixedMoment B raw26262step1 raw26262step1Labels = mixedMoment B raw26262step2 raw26262step2Labels := by
      have ha : raw26262step2 = -raw26262step1 := by apply Matrix.ext; change ∀ i j, raw26262step2 i j = -(raw26262step1 i j); unfold raw26262step2 raw26262step1; decide +kernel
      have hl : raw26262step2Labels = raw26262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26262step2 raw26262step2Labels = mixedMoment B raw26262step3 raw26262step3Labels := by
      have ha : raw26262step3 = raw26262step2 := by apply Matrix.ext; unfold raw26262step3 raw26262step2; decide +kernel
      have hl : raw26262step2Labels = labelEmbedding1 ∘ raw26262step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26262step2 raw26262step2Labels raw26262step3Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical26263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26263 raw26263Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26263 raw26263Labels = mixedMoment B raw26263step0 raw26263step0Labels := by
      have hz : ∀ j, raw26263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26263step0 = (fun i j => raw26263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26263step0 raw26263; decide +kernel
      have hl : raw26263step0Labels = raw26263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26263 raw26263Labels permutation346 hz
    mixedMoment B raw26263step0 raw26263step0Labels = mixedMoment B raw26263step1 raw26263step1Labels := by
      have ha : raw26263step1 = (fun i j => raw26263step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26263step1 raw26263step0; decide +kernel
      have hl : raw26263step1Labels = raw26263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26263step0 raw26263step0Labels permutation35 permutation7
    mixedMoment B raw26263step1 raw26263step1Labels = mixedMoment B raw26263step2 raw26263step2Labels := by
      have ha : raw26263step2 = -raw26263step1 := by apply Matrix.ext; change ∀ i j, raw26263step2 i j = -(raw26263step1 i j); unfold raw26263step2 raw26263step1; decide +kernel
      have hl : raw26263step2Labels = raw26263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26263step2 raw26263step2Labels = mixedMoment B raw26263step3 raw26263step3Labels := by
      have ha : raw26263step3 = raw26263step2 := by apply Matrix.ext; unfold raw26263step3 raw26263step2; decide +kernel
      have hl : raw26263step2Labels = labelEmbedding1 ∘ raw26263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26263step2 raw26263step2Labels raw26263step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

theorem canonical26264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26264 raw26264Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw26264 raw26264Labels = mixedMoment B raw26264step0 raw26264step0Labels := by
      have hz : ∀ j, raw26264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26264step0 = (fun i j => raw26264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26264step0 raw26264; decide +kernel
      have hl : raw26264step0Labels = raw26264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26264 raw26264Labels permutation346 hz
    mixedMoment B raw26264step0 raw26264step0Labels = mixedMoment B raw26264step1 raw26264step1Labels := by
      have ha : raw26264step1 = (fun i j => raw26264step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26264step1 raw26264step0; decide +kernel
      have hl : raw26264step1Labels = raw26264step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26264step0 raw26264step0Labels permutation32 permutation7
    mixedMoment B raw26264step1 raw26264step1Labels = mixedMoment B raw26264step2 raw26264step2Labels := by
      have ha : raw26264step2 = -raw26264step1 := by apply Matrix.ext; change ∀ i j, raw26264step2 i j = -(raw26264step1 i j); unfold raw26264step2 raw26264step1; decide +kernel
      have hl : raw26264step2Labels = raw26264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26264step2 raw26264step2Labels = mixedMoment B raw26264step3 raw26264step3Labels := by
      have ha : raw26264step3 = raw26264step2 := by apply Matrix.ext; unfold raw26264step3 raw26264step2; decide +kernel
      have hl : raw26264step2Labels = labelEmbedding1 ∘ raw26264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26264step2 raw26264step2Labels raw26264step3Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

theorem canonical26265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26265 raw26265Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw26265 raw26265Labels = mixedMoment B raw26265step0 raw26265step0Labels := by
      have hz : ∀ j, raw26265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26265step0 = (fun i j => raw26265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26265step0 raw26265; decide +kernel
      have hl : raw26265step0Labels = raw26265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26265 raw26265Labels permutation346 hz
    mixedMoment B raw26265step0 raw26265step0Labels = mixedMoment B raw26265step1 raw26265step1Labels := by
      have ha : raw26265step1 = (fun i j => raw26265step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26265step1 raw26265step0; decide +kernel
      have hl : raw26265step1Labels = raw26265step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26265step0 raw26265step0Labels permutation32 permutation7
    mixedMoment B raw26265step1 raw26265step1Labels = mixedMoment B raw26265step2 raw26265step2Labels := by
      have ha : raw26265step2 = -raw26265step1 := by apply Matrix.ext; change ∀ i j, raw26265step2 i j = -(raw26265step1 i j); unfold raw26265step2 raw26265step1; decide +kernel
      have hl : raw26265step2Labels = raw26265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26265step2 raw26265step2Labels = mixedMoment B raw26265step3 raw26265step3Labels := by
      have ha : raw26265step3 = raw26265step2 := by apply Matrix.ext; unfold raw26265step3 raw26265step2; decide +kernel
      have hl : raw26265step2Labels = labelEmbedding1 ∘ raw26265step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26265step2 raw26265step2Labels raw26265step3Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

theorem canonical26266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26266 raw26266Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw26266 raw26266Labels = mixedMoment B raw26266step0 raw26266step0Labels := by
      have ha : raw26266step0 = (fun i j => raw26266 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26266step0 raw26266; decide +kernel
      have hl : raw26266step0Labels = raw26266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26266 raw26266Labels permutation176 permutation7
    mixedMoment B raw26266step0 raw26266step0Labels = mixedMoment B raw26266step1 raw26266step1Labels := by
      have ha : raw26266step1 = -raw26266step0 := by apply Matrix.ext; change ∀ i j, raw26266step1 i j = -(raw26266step0 i j); unfold raw26266step1 raw26266step0; decide +kernel
      have hl : raw26266step1Labels = raw26266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26266step1 raw26266step1Labels = mixedMoment B raw26266step2 raw26266step2Labels := by
      have ha : raw26266step2 = raw26266step1 := by apply Matrix.ext; unfold raw26266step2 raw26266step1; decide +kernel
      have hl : raw26266step1Labels = labelEmbedding1 ∘ raw26266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26266step1 raw26266step1Labels raw26266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

theorem canonical26267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26267 raw26267Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw26267 raw26267Labels = mixedMoment B raw26267step0 raw26267step0Labels := by
      have hz : ∀ j, raw26267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26267step0 = (fun i j => raw26267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26267step0 raw26267; decide +kernel
      have hl : raw26267step0Labels = raw26267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26267 raw26267Labels permutation346 hz
    mixedMoment B raw26267step0 raw26267step0Labels = mixedMoment B raw26267step1 raw26267step1Labels := by
      have ha : raw26267step1 = (fun i j => raw26267step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26267step1 raw26267step0; decide +kernel
      have hl : raw26267step1Labels = raw26267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26267step0 raw26267step0Labels permutation32 permutation7
    mixedMoment B raw26267step1 raw26267step1Labels = mixedMoment B raw26267step2 raw26267step2Labels := by
      have ha : raw26267step2 = -raw26267step1 := by apply Matrix.ext; change ∀ i j, raw26267step2 i j = -(raw26267step1 i j); unfold raw26267step2 raw26267step1; decide +kernel
      have hl : raw26267step2Labels = raw26267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26267step2 raw26267step2Labels = mixedMoment B raw26267step3 raw26267step3Labels := by
      have ha : raw26267step3 = raw26267step2 := by apply Matrix.ext; unfold raw26267step3 raw26267step2; decide +kernel
      have hl : raw26267step2Labels = labelEmbedding1 ∘ raw26267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26267step2 raw26267step2Labels raw26267step3Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical26268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26268 raw26268Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26268 raw26268Labels = mixedMoment B raw26268step0 raw26268step0Labels := by
      have hz : ∀ j, raw26268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26268step0 = (fun i j => raw26268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26268step0 raw26268; decide +kernel
      have hl : raw26268step0Labels = raw26268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26268 raw26268Labels permutation346 hz
    mixedMoment B raw26268step0 raw26268step0Labels = mixedMoment B raw26268step1 raw26268step1Labels := by
      have ha : raw26268step1 = (fun i j => raw26268step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26268step1 raw26268step0; decide +kernel
      have hl : raw26268step1Labels = raw26268step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26268step0 raw26268step0Labels permutation33 permutation7
    mixedMoment B raw26268step1 raw26268step1Labels = mixedMoment B raw26268step2 raw26268step2Labels := by
      have ha : raw26268step2 = -raw26268step1 := by apply Matrix.ext; change ∀ i j, raw26268step2 i j = -(raw26268step1 i j); unfold raw26268step2 raw26268step1; decide +kernel
      have hl : raw26268step2Labels = raw26268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26268step2 raw26268step2Labels = mixedMoment B raw26268step3 raw26268step3Labels := by
      have ha : raw26268step3 = raw26268step2 := by apply Matrix.ext; unfold raw26268step3 raw26268step2; decide +kernel
      have hl : raw26268step2Labels = labelEmbedding1 ∘ raw26268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26268step2 raw26268step2Labels raw26268step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

theorem canonical26269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26269 raw26269Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw26269 raw26269Labels = mixedMoment B raw26269step0 raw26269step0Labels := by
      have hz : ∀ j, raw26269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26269step0 = (fun i j => raw26269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26269step0 raw26269; decide +kernel
      have hl : raw26269step0Labels = raw26269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26269 raw26269Labels permutation346 hz
    mixedMoment B raw26269step0 raw26269step0Labels = mixedMoment B raw26269step1 raw26269step1Labels := by
      have ha : raw26269step1 = (fun i j => raw26269step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26269step1 raw26269step0; decide +kernel
      have hl : raw26269step1Labels = raw26269step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26269step0 raw26269step0Labels permutation32 permutation7
    mixedMoment B raw26269step1 raw26269step1Labels = mixedMoment B raw26269step2 raw26269step2Labels := by
      have ha : raw26269step2 = -raw26269step1 := by apply Matrix.ext; change ∀ i j, raw26269step2 i j = -(raw26269step1 i j); unfold raw26269step2 raw26269step1; decide +kernel
      have hl : raw26269step2Labels = raw26269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26269step2 raw26269step2Labels = mixedMoment B raw26269step3 raw26269step3Labels := by
      have ha : raw26269step3 = raw26269step2 := by apply Matrix.ext; unfold raw26269step3 raw26269step2; decide +kernel
      have hl : raw26269step2Labels = labelEmbedding1 ∘ raw26269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26269step2 raw26269step2Labels raw26269step3Labels labelEmbedding1 hl
    _ = mixedMoment B node681 node681Labels := by rfl

theorem canonical26270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26270 raw26270Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw26270 raw26270Labels = mixedMoment B raw26270step0 raw26270step0Labels := by
      have hz : ∀ j, raw26270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26270step0 = (fun i j => raw26270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26270step0 raw26270; decide +kernel
      have hl : raw26270step0Labels = raw26270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26270 raw26270Labels permutation346 hz
    mixedMoment B raw26270step0 raw26270step0Labels = mixedMoment B raw26270step1 raw26270step1Labels := by
      have ha : raw26270step1 = (fun i j => raw26270step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26270step1 raw26270step0; decide +kernel
      have hl : raw26270step1Labels = raw26270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26270step0 raw26270step0Labels permutation32 permutation7
    mixedMoment B raw26270step1 raw26270step1Labels = mixedMoment B raw26270step2 raw26270step2Labels := by
      have ha : raw26270step2 = -raw26270step1 := by apply Matrix.ext; change ∀ i j, raw26270step2 i j = -(raw26270step1 i j); unfold raw26270step2 raw26270step1; decide +kernel
      have hl : raw26270step2Labels = raw26270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26270step2 raw26270step2Labels = mixedMoment B raw26270step3 raw26270step3Labels := by
      have ha : raw26270step3 = raw26270step2 := by apply Matrix.ext; unfold raw26270step3 raw26270step2; decide +kernel
      have hl : raw26270step2Labels = labelEmbedding1 ∘ raw26270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26270step2 raw26270step2Labels raw26270step3Labels labelEmbedding1 hl
    _ = mixedMoment B node840 node840Labels := by rfl

theorem canonical26271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26271 raw26271Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw26271 raw26271Labels = mixedMoment B raw26271step0 raw26271step0Labels := by
      have ha : raw26271step0 = (fun i j => raw26271 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26271step0 raw26271; decide +kernel
      have hl : raw26271step0Labels = raw26271Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26271 raw26271Labels permutation176 permutation7
    mixedMoment B raw26271step0 raw26271step0Labels = mixedMoment B raw26271step1 raw26271step1Labels := by
      have ha : raw26271step1 = -raw26271step0 := by apply Matrix.ext; change ∀ i j, raw26271step1 i j = -(raw26271step0 i j); unfold raw26271step1 raw26271step0; decide +kernel
      have hl : raw26271step1Labels = raw26271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26271step1 raw26271step1Labels = mixedMoment B raw26271step2 raw26271step2Labels := by
      have ha : raw26271step2 = raw26271step1 := by apply Matrix.ext; unfold raw26271step2 raw26271step1; decide +kernel
      have hl : raw26271step1Labels = labelEmbedding1 ∘ raw26271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26271step1 raw26271step1Labels raw26271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node760 node760Labels := by rfl

theorem canonical26272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26272 raw26272Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw26272 raw26272Labels = mixedMoment B raw26272step0 raw26272step0Labels := by
      have hz : ∀ j, raw26272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26272step0 = (fun i j => raw26272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26272step0 raw26272; decide +kernel
      have hl : raw26272step0Labels = raw26272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26272 raw26272Labels permutation346 hz
    mixedMoment B raw26272step0 raw26272step0Labels = mixedMoment B raw26272step1 raw26272step1Labels := by
      have ha : raw26272step1 = (fun i j => raw26272step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26272step1 raw26272step0; decide +kernel
      have hl : raw26272step1Labels = raw26272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26272step0 raw26272step0Labels permutation32 permutation7
    mixedMoment B raw26272step1 raw26272step1Labels = mixedMoment B raw26272step2 raw26272step2Labels := by
      have ha : raw26272step2 = -raw26272step1 := by apply Matrix.ext; change ∀ i j, raw26272step2 i j = -(raw26272step1 i j); unfold raw26272step2 raw26272step1; decide +kernel
      have hl : raw26272step2Labels = raw26272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26272step2 raw26272step2Labels = mixedMoment B raw26272step3 raw26272step3Labels := by
      have ha : raw26272step3 = raw26272step2 := by apply Matrix.ext; unfold raw26272step3 raw26272step2; decide +kernel
      have hl : raw26272step2Labels = labelEmbedding1 ∘ raw26272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26272step2 raw26272step2Labels raw26272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical26273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26273 raw26273Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw26273 raw26273Labels = mixedMoment B raw26273step0 raw26273step0Labels := by
      have hz : ∀ j, raw26273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26273step0 = (fun i j => raw26273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26273step0 raw26273; decide +kernel
      have hl : raw26273step0Labels = raw26273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26273 raw26273Labels permutation346 hz
    mixedMoment B raw26273step0 raw26273step0Labels = mixedMoment B raw26273step1 raw26273step1Labels := by
      have ha : raw26273step1 = (fun i j => raw26273step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26273step1 raw26273step0; decide +kernel
      have hl : raw26273step1Labels = raw26273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26273step0 raw26273step0Labels permutation34 permutation7
    mixedMoment B raw26273step1 raw26273step1Labels = mixedMoment B raw26273step2 raw26273step2Labels := by
      have ha : raw26273step2 = -raw26273step1 := by apply Matrix.ext; change ∀ i j, raw26273step2 i j = -(raw26273step1 i j); unfold raw26273step2 raw26273step1; decide +kernel
      have hl : raw26273step2Labels = raw26273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26273step2 raw26273step2Labels = mixedMoment B raw26273step3 raw26273step3Labels := by
      have ha : raw26273step3 = raw26273step2 := by apply Matrix.ext; unfold raw26273step3 raw26273step2; decide +kernel
      have hl : raw26273step2Labels = labelEmbedding1 ∘ raw26273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26273step2 raw26273step2Labels raw26273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical26274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26274 raw26274Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26274 raw26274Labels = mixedMoment B raw26274step0 raw26274step0Labels := by
      have hz : ∀ j, raw26274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26274step0 = (fun i j => raw26274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26274step0 raw26274; decide +kernel
      have hl : raw26274step0Labels = raw26274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26274 raw26274Labels permutation346 hz
    _ = mixedMoment B node1648 node1648Labels := by rfl

theorem canonical26275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26275 raw26275Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw26275 raw26275Labels = mixedMoment B raw26275step0 raw26275step0Labels := by
      have hz : ∀ j, raw26275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26275step0 = (fun i j => raw26275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26275step0 raw26275; decide +kernel
      have hl : raw26275step0Labels = raw26275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26275 raw26275Labels permutation346 hz
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical26276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26276 raw26276Labels = mixedMoment B node732 node732Labels := by
  calc
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical26277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26277 raw26277Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw26277 raw26277Labels = mixedMoment B raw26277step0 raw26277step0Labels := by
      have hz : ∀ j, raw26277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26277step0 = (fun i j => raw26277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26277step0 raw26277; decide +kernel
      have hl : raw26277step0Labels = raw26277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26277 raw26277Labels permutation346 hz
    mixedMoment B raw26277step0 raw26277step0Labels = mixedMoment B raw26277step1 raw26277step1Labels := by
      have ha : raw26277step1 = (fun i j => raw26277step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26277step1 raw26277step0; decide +kernel
      have hl : raw26277step1Labels = raw26277step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26277step0 raw26277step0Labels permutation34 permutation2
    _ = mixedMoment B node739 node739Labels := by rfl

theorem canonical26278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26278 raw26278Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw26278 raw26278Labels = mixedMoment B raw26278step0 raw26278step0Labels := by
      have hz : ∀ j, raw26278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26278step0 = (fun i j => raw26278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26278step0 raw26278; decide +kernel
      have hl : raw26278step0Labels = raw26278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26278 raw26278Labels permutation346 hz
    _ = mixedMoment B node739 node739Labels := by rfl

theorem canonical26279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26279 raw26279Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw26279 raw26279Labels = mixedMoment B raw26279step0 raw26279step0Labels := by
      have hz : ∀ j, raw26279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26279step0 = (fun i j => raw26279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26279step0 raw26279; decide +kernel
      have hl : raw26279step0Labels = raw26279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26279 raw26279Labels permutation346 hz
    _ = mixedMoment B node737 node737Labels := by rfl

theorem canonical26280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26280 raw26280Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26280 raw26280Labels = mixedMoment B raw26280step0 raw26280step0Labels := by
      have hz : ∀ j, raw26280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26280step0 = (fun i j => raw26280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26280step0 raw26280; decide +kernel
      have hl : raw26280step0Labels = raw26280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26280 raw26280Labels permutation346 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical26354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26354 raw26354Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw26354 raw26354Labels = mixedMoment B raw26354step0 raw26354step0Labels := by
      have hz : ∀ j, raw26354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26354step0 = (fun i j => raw26354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26354step0 raw26354; decide +kernel
      have hl : raw26354step0Labels = raw26354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26354 raw26354Labels permutation346 hz
    mixedMoment B raw26354step0 raw26354step0Labels = mixedMoment B raw26354step1 raw26354step1Labels := by
      have hz : ∀ i, raw26354step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26354step1 = (fun i j => raw26354step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26354step1 raw26354step0; decide +kernel
      have hl : raw26354step1Labels = (fun j => raw26354step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26354step0 raw26354step0Labels permutation6 hz
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical26355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26355 raw26355Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26355 raw26355Labels = mixedMoment B raw26355step0 raw26355step0Labels := by
      have hz : ∀ i, raw26355 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26355step0 = (fun i j => raw26355 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26355step0 raw26355; decide +kernel
      have hl : raw26355step0Labels = (fun j => raw26355Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26355 raw26355Labels permutation6 hz
    mixedMoment B raw26355step0 raw26355step0Labels = mixedMoment B raw26355step1 raw26355step1Labels := by
      have ha : raw26355step1 = (fun i j => raw26355step0 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26355step1 raw26355step0; decide +kernel
      have hl : raw26355step1Labels = raw26355step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26355step0 raw26355step0Labels permutation176 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical26356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26356 raw26356Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26356 raw26356Labels = mixedMoment B raw26356step0 raw26356step0Labels := by
      have hz : ∀ j, raw26356 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26356step0 = (fun i j => raw26356 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26356step0 raw26356; decide +kernel
      have hl : raw26356step0Labels = raw26356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26356 raw26356Labels permutation520 hz
    mixedMoment B raw26356step0 raw26356step0Labels = mixedMoment B raw26356step1 raw26356step1Labels := by
      have hz : ∀ j, raw26356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26356step1 = (fun i j => raw26356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26356step1 raw26356step0; decide +kernel
      have hl : raw26356step1Labels = raw26356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26356step0 raw26356step0Labels permutation80 hz
    mixedMoment B raw26356step1 raw26356step1Labels = mixedMoment B raw26356step2 raw26356step2Labels := by
      have hz : ∀ i, raw26356step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26356step2 = (fun i j => raw26356step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26356step2 raw26356step1; decide +kernel
      have hl : raw26356step2Labels = (fun j => raw26356step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26356step1 raw26356step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical26357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26357 raw26357Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw26357 raw26357Labels = mixedMoment B raw26357step0 raw26357step0Labels := by
      have hz : ∀ j, raw26357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26357step0 = (fun i j => raw26357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26357step0 raw26357; decide +kernel
      have hl : raw26357step0Labels = raw26357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26357 raw26357Labels permutation265 hz
    mixedMoment B raw26357step0 raw26357step0Labels = mixedMoment B raw26357step1 raw26357step1Labels := by
      have hz : ∀ i, raw26357step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26357step1 = (fun i j => raw26357step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26357step1 raw26357step0; decide +kernel
      have hl : raw26357step1Labels = (fun j => raw26357step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26357step0 raw26357step0Labels permutation6 hz
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical26358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26358 raw26358Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26358 raw26358Labels = mixedMoment B raw26358step0 raw26358step0Labels := by
      have hz : ∀ i, raw26358 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26358step0 = (fun i j => raw26358 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26358step0 raw26358; decide +kernel
      have hl : raw26358step0Labels = (fun j => raw26358Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26358 raw26358Labels permutation6 hz
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical26359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26359 raw26359Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26359 raw26359Labels = mixedMoment B raw26359step0 raw26359step0Labels := by
      have hz : ∀ j, raw26359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26359step0 = (fun i j => raw26359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26359step0 raw26359; decide +kernel
      have hl : raw26359step0Labels = raw26359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359 raw26359Labels permutation520 hz
    mixedMoment B raw26359step0 raw26359step0Labels = mixedMoment B raw26359step1 raw26359step1Labels := by
      have hz : ∀ j, raw26359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26359step1 = (fun i j => raw26359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26359step1 raw26359step0; decide +kernel
      have hl : raw26359step1Labels = raw26359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359step0 raw26359step0Labels permutation56 hz
    mixedMoment B raw26359step1 raw26359step1Labels = mixedMoment B raw26359step2 raw26359step2Labels := by
      have hz : ∀ i, raw26359step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26359step2 = (fun i j => raw26359step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26359step2 raw26359step1; decide +kernel
      have hl : raw26359step2Labels = (fun j => raw26359step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26359step1 raw26359step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical26360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26360 raw26360Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw26360 raw26360Labels = mixedMoment B raw26360step0 raw26360step0Labels := by
      have hz : ∀ j, raw26360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26360step0 = (fun i j => raw26360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26360step0 raw26360; decide +kernel
      have hl : raw26360step0Labels = raw26360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26360 raw26360Labels permutation346 hz
    mixedMoment B raw26360step0 raw26360step0Labels = mixedMoment B raw26360step1 raw26360step1Labels := by
      have hz : ∀ j, raw26360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26360step1 = (fun i j => raw26360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26360step1 raw26360step0; decide +kernel
      have hl : raw26360step1Labels = raw26360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26360step0 raw26360step0Labels permutation56 hz
    mixedMoment B raw26360step1 raw26360step1Labels = mixedMoment B raw26360step2 raw26360step2Labels := by
      have hz : ∀ i, raw26360step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26360step2 = (fun i j => raw26360step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26360step2 raw26360step1; decide +kernel
      have hl : raw26360step2Labels = (fun j => raw26360step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26360step1 raw26360step1Labels permutation6 hz
    mixedMoment B raw26360step2 raw26360step2Labels = mixedMoment B raw26360step3 raw26360step3Labels := by
      have ha : raw26360step3 = (fun i j => raw26360step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26360step3 raw26360step2; decide +kernel
      have hl : raw26360step3Labels = raw26360step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26360step2 raw26360step2Labels permutation10 permutation0
    _ = mixedMoment B node4059 node4059Labels := by rfl

theorem canonical26361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26361 raw26361Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw26361 raw26361Labels = mixedMoment B raw26361step0 raw26361step0Labels := by
      have hz : ∀ j, raw26361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26361step0 = (fun i j => raw26361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26361step0 raw26361; decide +kernel
      have hl : raw26361step0Labels = raw26361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26361 raw26361Labels permutation346 hz
    mixedMoment B raw26361step0 raw26361step0Labels = mixedMoment B raw26361step1 raw26361step1Labels := by
      have hz : ∀ i, raw26361step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26361step1 = (fun i j => raw26361step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26361step1 raw26361step0; decide +kernel
      have hl : raw26361step1Labels = (fun j => raw26361step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26361step0 raw26361step0Labels permutation6 hz
    mixedMoment B raw26361step1 raw26361step1Labels = mixedMoment B raw26361step2 raw26361step2Labels := by
      have ha : raw26361step2 = (fun i j => raw26361step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26361step2 raw26361step1; decide +kernel
      have hl : raw26361step2Labels = raw26361step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26361step1 raw26361step1Labels permutation34 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical26362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26362 raw26362Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw26362 raw26362Labels = mixedMoment B raw26362step0 raw26362step0Labels := by
      have hz : ∀ j, raw26362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26362step0 = (fun i j => raw26362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26362step0 raw26362; decide +kernel
      have hl : raw26362step0Labels = raw26362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26362 raw26362Labels permutation265 hz
    mixedMoment B raw26362step0 raw26362step0Labels = mixedMoment B raw26362step1 raw26362step1Labels := by
      have hz : ∀ i, raw26362step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26362step1 = (fun i j => raw26362step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26362step1 raw26362step0; decide +kernel
      have hl : raw26362step1Labels = (fun j => raw26362step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26362step0 raw26362step0Labels permutation6 hz
    mixedMoment B raw26362step1 raw26362step1Labels = mixedMoment B raw26362step2 raw26362step2Labels := by
      have ha : raw26362step2 = (fun i j => raw26362step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26362step2 raw26362step1; decide +kernel
      have hl : raw26362step2Labels = raw26362step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26362step1 raw26362step1Labels permutation34 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

theorem canonical26363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26363 raw26363Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw26363 raw26363Labels = mixedMoment B raw26363step0 raw26363step0Labels := by
      have hz : ∀ j, raw26363 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26363step0 = (fun i j => raw26363 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26363step0 raw26363; decide +kernel
      have hl : raw26363step0Labels = raw26363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363 raw26363Labels permutation520 hz
    mixedMoment B raw26363step0 raw26363step0Labels = mixedMoment B raw26363step1 raw26363step1Labels := by
      have hz : ∀ j, raw26363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26363step1 = (fun i j => raw26363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26363step1 raw26363step0; decide +kernel
      have hl : raw26363step1Labels = raw26363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363step0 raw26363step0Labels permutation80 hz
    mixedMoment B raw26363step1 raw26363step1Labels = mixedMoment B raw26363step2 raw26363step2Labels := by
      have hz : ∀ j, raw26363step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw26363step2 = (fun i j => raw26363step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw26363step2 raw26363step1; decide +kernel
      have hl : raw26363step2Labels = raw26363step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363step1 raw26363step1Labels permutation14 hz
    mixedMoment B raw26363step2 raw26363step2Labels = mixedMoment B raw26363step3 raw26363step3Labels := by
      have hz : ∀ i, raw26363step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26363step3 = (fun i j => raw26363step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26363step3 raw26363step2; decide +kernel
      have hl : raw26363step3Labels = (fun j => raw26363step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26363step2 raw26363step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical26364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26364 raw26364Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw26364 raw26364Labels = mixedMoment B raw26364step0 raw26364step0Labels := by
      have hz : ∀ j, raw26364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26364step0 = (fun i j => raw26364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26364step0 raw26364; decide +kernel
      have hl : raw26364step0Labels = raw26364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26364 raw26364Labels permutation265 hz
    mixedMoment B raw26364step0 raw26364step0Labels = mixedMoment B raw26364step1 raw26364step1Labels := by
      have ha : raw26364step1 = (fun i j => raw26364step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26364step1 raw26364step0; decide +kernel
      have hl : raw26364step1Labels = raw26364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26364step0 raw26364step0Labels permutation32 permutation4
    mixedMoment B raw26364step1 raw26364step1Labels = mixedMoment B raw26364step2 raw26364step2Labels := by
      have ha : raw26364step2 = -raw26364step1 := by apply Matrix.ext; change ∀ i j, raw26364step2 i j = -(raw26364step1 i j); unfold raw26364step2 raw26364step1; decide +kernel
      have hl : raw26364step2Labels = raw26364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1700 node1700Labels := by rfl

theorem canonical26365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26365 raw26365Labels = mixedMoment B node3057 node3057Labels := by
  calc
    mixedMoment B raw26365 raw26365Labels = mixedMoment B raw26365step0 raw26365step0Labels := by
      have ha : raw26365step0 = (fun i j => raw26365 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26365step0 raw26365; decide +kernel
      have hl : raw26365step0Labels = raw26365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26365 raw26365Labels permutation640 permutation4
    _ = mixedMoment B node3057 node3057Labels := by rfl

theorem canonical26366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26366 raw26366Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26366 raw26366Labels = mixedMoment B raw26366step0 raw26366step0Labels := by
      have hz : ∀ j, raw26366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26366step0 = (fun i j => raw26366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26366step0 raw26366; decide +kernel
      have hl : raw26366step0Labels = raw26366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26366 raw26366Labels permutation265 hz
    mixedMoment B raw26366step0 raw26366step0Labels = mixedMoment B raw26366step1 raw26366step1Labels := by
      have ha : raw26366step1 = (fun i j => raw26366step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26366step1 raw26366step0; decide +kernel
      have hl : raw26366step1Labels = raw26366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26366step0 raw26366step0Labels permutation145 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

theorem canonical26367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26367 raw26367Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26367 raw26367Labels = mixedMoment B raw26367step0 raw26367step0Labels := by
      have hz : ∀ j, raw26367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26367step0 = (fun i j => raw26367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26367step0 raw26367; decide +kernel
      have hl : raw26367step0Labels = raw26367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26367 raw26367Labels permutation265 hz
    mixedMoment B raw26367step0 raw26367step0Labels = mixedMoment B raw26367step1 raw26367step1Labels := by
      have ha : raw26367step1 = (fun i j => raw26367step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26367step1 raw26367step0; decide +kernel
      have hl : raw26367step1Labels = raw26367step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26367step0 raw26367step0Labels permutation139 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26368 raw26368Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26368 raw26368Labels = mixedMoment B raw26368step0 raw26368step0Labels := by
      have hz : ∀ j, raw26368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26368step0 = (fun i j => raw26368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26368step0 raw26368; decide +kernel
      have hl : raw26368step0Labels = raw26368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26368 raw26368Labels permutation265 hz
    mixedMoment B raw26368step0 raw26368step0Labels = mixedMoment B raw26368step1 raw26368step1Labels := by
      have ha : raw26368step1 = (fun i j => raw26368step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26368step1 raw26368step0; decide +kernel
      have hl : raw26368step1Labels = raw26368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26368step0 raw26368step0Labels permutation137 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

theorem canonical26369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26369 raw26369Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw26369 raw26369Labels = mixedMoment B raw26369step0 raw26369step0Labels := by
      have hz : ∀ j, raw26369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26369step0 = (fun i j => raw26369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26369step0 raw26369; decide +kernel
      have hl : raw26369step0Labels = raw26369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26369 raw26369Labels permutation265 hz
    mixedMoment B raw26369step0 raw26369step0Labels = mixedMoment B raw26369step1 raw26369step1Labels := by
      have ha : raw26369step1 = (fun i j => raw26369step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26369step1 raw26369step0; decide +kernel
      have hl : raw26369step1Labels = raw26369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26369step0 raw26369step0Labels permutation50 permutation2
    mixedMoment B raw26369step1 raw26369step1Labels = mixedMoment B raw26369step2 raw26369step2Labels := by
      have ha : raw26369step2 = -raw26369step1 := by apply Matrix.ext; change ∀ i j, raw26369step2 i j = -(raw26369step1 i j); unfold raw26369step2 raw26369step1; decide +kernel
      have hl : raw26369step2Labels = raw26369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical26370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26370 raw26370Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26370 raw26370Labels = mixedMoment B raw26370step0 raw26370step0Labels := by
      have hz : ∀ j, raw26370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26370step0 = (fun i j => raw26370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26370step0 raw26370; decide +kernel
      have hl : raw26370step0Labels = raw26370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26370 raw26370Labels permutation265 hz
    mixedMoment B raw26370step0 raw26370step0Labels = mixedMoment B raw26370step1 raw26370step1Labels := by
      have ha : raw26370step1 = -raw26370step0 := by apply Matrix.ext; change ∀ i j, raw26370step1 i j = -(raw26370step0 i j); unfold raw26370step1 raw26370step0; decide +kernel
      have hl : raw26370step1Labels = raw26370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical26371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26371 raw26371Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw26371 raw26371Labels = mixedMoment B raw26371step0 raw26371step0Labels := by
      have ha : raw26371step0 = (fun i j => raw26371 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26371step0 raw26371; decide +kernel
      have hl : raw26371step0Labels = raw26371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26371 raw26371Labels permutation184 permutation4
    mixedMoment B raw26371step0 raw26371step0Labels = mixedMoment B raw26371step1 raw26371step1Labels := by
      have ha : raw26371step1 = -raw26371step0 := by apply Matrix.ext; change ∀ i j, raw26371step1 i j = -(raw26371step0 i j); unfold raw26371step1 raw26371step0; decide +kernel
      have hl : raw26371step1Labels = raw26371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1698 node1698Labels := by rfl

theorem canonical26372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26372 raw26372Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26372 raw26372Labels = mixedMoment B raw26372step0 raw26372step0Labels := by
      have hz : ∀ j, raw26372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26372step0 = (fun i j => raw26372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26372step0 raw26372; decide +kernel
      have hl : raw26372step0Labels = raw26372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26372 raw26372Labels permutation265 hz
    mixedMoment B raw26372step0 raw26372step0Labels = mixedMoment B raw26372step1 raw26372step1Labels := by
      have ha : raw26372step1 = (fun i j => raw26372step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26372step1 raw26372step0; decide +kernel
      have hl : raw26372step1Labels = raw26372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26372step0 raw26372step0Labels permutation40 permutation4
    mixedMoment B raw26372step1 raw26372step1Labels = mixedMoment B raw26372step2 raw26372step2Labels := by
      have ha : raw26372step2 = -raw26372step1 := by apply Matrix.ext; change ∀ i j, raw26372step2 i j = -(raw26372step1 i j); unfold raw26372step2 raw26372step1; decide +kernel
      have hl : raw26372step2Labels = raw26372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26373 raw26373Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26373 raw26373Labels = mixedMoment B raw26373step0 raw26373step0Labels := by
      have hz : ∀ j, raw26373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26373step0 = (fun i j => raw26373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26373step0 raw26373; decide +kernel
      have hl : raw26373step0Labels = raw26373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26373 raw26373Labels permutation265 hz
    mixedMoment B raw26373step0 raw26373step0Labels = mixedMoment B raw26373step1 raw26373step1Labels := by
      have ha : raw26373step1 = (fun i j => raw26373step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26373step1 raw26373step0; decide +kernel
      have hl : raw26373step1Labels = raw26373step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26373step0 raw26373step0Labels permutation34 permutation4
    mixedMoment B raw26373step1 raw26373step1Labels = mixedMoment B raw26373step2 raw26373step2Labels := by
      have ha : raw26373step2 = -raw26373step1 := by apply Matrix.ext; change ∀ i j, raw26373step2 i j = -(raw26373step1 i j); unfold raw26373step2 raw26373step1; decide +kernel
      have hl : raw26373step2Labels = raw26373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26374 raw26374Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26374 raw26374Labels = mixedMoment B raw26374step0 raw26374step0Labels := by
      have hz : ∀ j, raw26374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26374step0 = (fun i j => raw26374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26374step0 raw26374; decide +kernel
      have hl : raw26374step0Labels = raw26374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26374 raw26374Labels permutation265 hz
    mixedMoment B raw26374step0 raw26374step0Labels = mixedMoment B raw26374step1 raw26374step1Labels := by
      have ha : raw26374step1 = (fun i j => raw26374step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26374step1 raw26374step0; decide +kernel
      have hl : raw26374step1Labels = raw26374step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26374step0 raw26374step0Labels permutation32 permutation4
    mixedMoment B raw26374step1 raw26374step1Labels = mixedMoment B raw26374step2 raw26374step2Labels := by
      have ha : raw26374step2 = -raw26374step1 := by apply Matrix.ext; change ∀ i j, raw26374step2 i j = -(raw26374step1 i j); unfold raw26374step2 raw26374step1; decide +kernel
      have hl : raw26374step2Labels = raw26374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26375 raw26375Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw26375 raw26375Labels = mixedMoment B raw26375step0 raw26375step0Labels := by
      have ha : raw26375step0 = (fun i j => raw26375 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26375step0 raw26375; decide +kernel
      have hl : raw26375step0Labels = raw26375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26375 raw26375Labels permutation184 permutation2
    _ = mixedMoment B node597 node597Labels := by rfl

theorem canonical26376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26376 raw26376Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26376 raw26376Labels = mixedMoment B raw26376step0 raw26376step0Labels := by
      have hz : ∀ j, raw26376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26376step0 = (fun i j => raw26376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26376step0 raw26376; decide +kernel
      have hl : raw26376step0Labels = raw26376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26376 raw26376Labels permutation434 hz
    mixedMoment B raw26376step0 raw26376step0Labels = mixedMoment B raw26376step1 raw26376step1Labels := by
      have ha : raw26376step1 = (fun i j => raw26376step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26376step1 raw26376step0; decide +kernel
      have hl : raw26376step1Labels = raw26376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26376step0 raw26376step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical26377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26377 raw26377Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26377 raw26377Labels = mixedMoment B raw26377step0 raw26377step0Labels := by
      have hz : ∀ j, raw26377 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26377step0 = (fun i j => raw26377 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26377step0 raw26377; decide +kernel
      have hl : raw26377step0Labels = raw26377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26377 raw26377Labels permutation520 hz
    mixedMoment B raw26377step0 raw26377step0Labels = mixedMoment B raw26377step1 raw26377step1Labels := by
      have ha : raw26377step1 = (fun i j => raw26377step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26377step1 raw26377step0; decide +kernel
      have hl : raw26377step1Labels = raw26377step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26377step0 raw26377step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical26378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26378 raw26378Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw26378 raw26378Labels = mixedMoment B raw26378step0 raw26378step0Labels := by
      have ha : raw26378step0 = (fun i j => raw26378 (permutation255 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26378step0 raw26378; decide +kernel
      have hl : raw26378step0Labels = raw26378Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26378 raw26378Labels permutation255 permutation2
    _ = mixedMoment B node1056 node1056Labels := by rfl

theorem canonical26379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26379 raw26379Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26379 raw26379Labels = mixedMoment B raw26379step0 raw26379step0Labels := by
      have ha : raw26379step0 = (fun i j => raw26379 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26379step0 raw26379; decide +kernel
      have hl : raw26379step0Labels = raw26379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26379 raw26379Labels permutation173 permutation2
    mixedMoment B raw26379step0 raw26379step0Labels = mixedMoment B raw26379step1 raw26379step1Labels := by
      have ha : raw26379step1 = -raw26379step0 := by apply Matrix.ext; change ∀ i j, raw26379step1 i j = -(raw26379step0 i j); unfold raw26379step1 raw26379step0; decide +kernel
      have hl : raw26379step1Labels = raw26379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical26380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26380 raw26380Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26380 raw26380Labels = mixedMoment B raw26380step0 raw26380step0Labels := by
      have ha : raw26380step0 = (fun i j => raw26380 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26380step0 raw26380; decide +kernel
      have hl : raw26380step0Labels = raw26380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26380 raw26380Labels permutation171 permutation2
    mixedMoment B raw26380step0 raw26380step0Labels = mixedMoment B raw26380step1 raw26380step1Labels := by
      have ha : raw26380step1 = -raw26380step0 := by apply Matrix.ext; change ∀ i j, raw26380step1 i j = -(raw26380step0 i j); unfold raw26380step1 raw26380step0; decide +kernel
      have hl : raw26380step1Labels = raw26380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical26381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26381 raw26381Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26381 raw26381Labels = mixedMoment B raw26381step0 raw26381step0Labels := by
      have ha : raw26381step0 = (fun i j => raw26381 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26381step0 raw26381; decide +kernel
      have hl : raw26381step0Labels = raw26381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26381 raw26381Labels permutation170 permutation2
    mixedMoment B raw26381step0 raw26381step0Labels = mixedMoment B raw26381step1 raw26381step1Labels := by
      have ha : raw26381step1 = -raw26381step0 := by apply Matrix.ext; change ∀ i j, raw26381step1 i j = -(raw26381step0 i j); unfold raw26381step1 raw26381step0; decide +kernel
      have hl : raw26381step1Labels = raw26381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical26382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26382 raw26382Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26382 raw26382Labels = mixedMoment B raw26382step0 raw26382step0Labels := by
      have ha : raw26382step0 = (fun i j => raw26382 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26382step0 raw26382; decide +kernel
      have hl : raw26382step0Labels = raw26382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26382 raw26382Labels permutation170 permutation2
    mixedMoment B raw26382step0 raw26382step0Labels = mixedMoment B raw26382step1 raw26382step1Labels := by
      have ha : raw26382step1 = -raw26382step0 := by apply Matrix.ext; change ∀ i j, raw26382step1 i j = -(raw26382step0 i j); unfold raw26382step1 raw26382step0; decide +kernel
      have hl : raw26382step1Labels = raw26382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical26383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26383 raw26383Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26383 raw26383Labels = mixedMoment B raw26383step0 raw26383step0Labels := by
      have ha : raw26383step0 = (fun i j => raw26383 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26383step0 raw26383; decide +kernel
      have hl : raw26383step0Labels = raw26383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26383 raw26383Labels permutation185 permutation4
    mixedMoment B raw26383step0 raw26383step0Labels = mixedMoment B raw26383step1 raw26383step1Labels := by
      have ha : raw26383step1 = -raw26383step0 := by apply Matrix.ext; change ∀ i j, raw26383step1 i j = -(raw26383step0 i j); unfold raw26383step1 raw26383step0; decide +kernel
      have hl : raw26383step1Labels = raw26383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical26384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26384 raw26384Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26384 raw26384Labels = mixedMoment B raw26384step0 raw26384step0Labels := by
      have ha : raw26384step0 = (fun i j => raw26384 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26384step0 raw26384; decide +kernel
      have hl : raw26384step0Labels = raw26384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26384 raw26384Labels permutation212 permutation4
    mixedMoment B raw26384step0 raw26384step0Labels = mixedMoment B raw26384step1 raw26384step1Labels := by
      have ha : raw26384step1 = -raw26384step0 := by apply Matrix.ext; change ∀ i j, raw26384step1 i j = -(raw26384step0 i j); unfold raw26384step1 raw26384step0; decide +kernel
      have hl : raw26384step1Labels = raw26384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26385 raw26385Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26385 raw26385Labels = mixedMoment B raw26385step0 raw26385step0Labels := by
      have ha : raw26385step0 = (fun i j => raw26385 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26385step0 raw26385; decide +kernel
      have hl : raw26385step0Labels = raw26385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26385 raw26385Labels permutation188 permutation4
    mixedMoment B raw26385step0 raw26385step0Labels = mixedMoment B raw26385step1 raw26385step1Labels := by
      have ha : raw26385step1 = -raw26385step0 := by apply Matrix.ext; change ∀ i j, raw26385step1 i j = -(raw26385step0 i j); unfold raw26385step1 raw26385step0; decide +kernel
      have hl : raw26385step1Labels = raw26385step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26386 raw26386Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26386 raw26386Labels = mixedMoment B raw26386step0 raw26386step0Labels := by
      have ha : raw26386step0 = (fun i j => raw26386 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26386step0 raw26386; decide +kernel
      have hl : raw26386step0Labels = raw26386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26386 raw26386Labels permutation182 permutation4
    mixedMoment B raw26386step0 raw26386step0Labels = mixedMoment B raw26386step1 raw26386step1Labels := by
      have ha : raw26386step1 = -raw26386step0 := by apply Matrix.ext; change ∀ i j, raw26386step1 i j = -(raw26386step0 i j); unfold raw26386step1 raw26386step0; decide +kernel
      have hl : raw26386step1Labels = raw26386step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26387 raw26387Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw26387 raw26387Labels = mixedMoment B raw26387step0 raw26387step0Labels := by
      have ha : raw26387step0 = (fun i j => raw26387 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26387step0 raw26387; decide +kernel
      have hl : raw26387step0Labels = raw26387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26387 raw26387Labels permutation170 permutation2
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical26388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26388 raw26388Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw26388 raw26388Labels = mixedMoment B raw26388step0 raw26388step0Labels := by
      have ha : raw26388step0 = (fun i j => raw26388 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26388step0 raw26388; decide +kernel
      have hl : raw26388step0Labels = raw26388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26388 raw26388Labels permutation170 permutation2
    _ = mixedMoment B node1366 node1366Labels := by rfl

theorem canonical26389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26389 raw26389Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26389 raw26389Labels = mixedMoment B raw26389step0 raw26389step0Labels := by
      have ha : raw26389step0 = (fun i j => raw26389 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26389step0 raw26389; decide +kernel
      have hl : raw26389step0Labels = raw26389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26389 raw26389Labels permutation173 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

theorem canonical26390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26390 raw26390Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26390 raw26390Labels = mixedMoment B raw26390step0 raw26390step0Labels := by
      have ha : raw26390step0 = (fun i j => raw26390 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26390step0 raw26390; decide +kernel
      have hl : raw26390step0Labels = raw26390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26390 raw26390Labels permutation171 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

theorem canonical26391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26391 raw26391Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26391 raw26391Labels = mixedMoment B raw26391step0 raw26391step0Labels := by
      have ha : raw26391step0 = (fun i j => raw26391 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26391step0 raw26391; decide +kernel
      have hl : raw26391step0Labels = raw26391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26391 raw26391Labels permutation170 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

theorem canonical26392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26392 raw26392Labels = mixedMoment B node1319 node1319Labels := by
  calc
    _ = mixedMoment B node1319 node1319Labels := by rfl

theorem canonical26393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26393 raw26393Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw26393 raw26393Labels = mixedMoment B raw26393step0 raw26393step0Labels := by
      have hz : ∀ j, raw26393 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26393step0 = (fun i j => raw26393 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26393step0 raw26393; decide +kernel
      have hl : raw26393step0Labels = raw26393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26393 raw26393Labels permutation590 hz
    mixedMoment B raw26393step0 raw26393step0Labels = mixedMoment B raw26393step1 raw26393step1Labels := by
      have ha : raw26393step1 = (fun i j => raw26393step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26393step1 raw26393step0; decide +kernel
      have hl : raw26393step1Labels = raw26393step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26393step0 raw26393step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical26394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26394 raw26394Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26394 raw26394Labels = mixedMoment B raw26394step0 raw26394step0Labels := by
      have ha : raw26394step0 = (fun i j => raw26394 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26394step0 raw26394; decide +kernel
      have hl : raw26394step0Labels = raw26394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26394 raw26394Labels permutation173 permutation2
    mixedMoment B raw26394step0 raw26394step0Labels = mixedMoment B raw26394step1 raw26394step1Labels := by
      have ha : raw26394step1 = -raw26394step0 := by apply Matrix.ext; change ∀ i j, raw26394step1 i j = -(raw26394step0 i j); unfold raw26394step1 raw26394step0; decide +kernel
      have hl : raw26394step1Labels = raw26394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

theorem canonical26395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26395 raw26395Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26395 raw26395Labels = mixedMoment B raw26395step0 raw26395step0Labels := by
      have ha : raw26395step0 = (fun i j => raw26395 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26395step0 raw26395; decide +kernel
      have hl : raw26395step0Labels = raw26395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26395 raw26395Labels permutation171 permutation2
    mixedMoment B raw26395step0 raw26395step0Labels = mixedMoment B raw26395step1 raw26395step1Labels := by
      have ha : raw26395step1 = -raw26395step0 := by apply Matrix.ext; change ∀ i j, raw26395step1 i j = -(raw26395step0 i j); unfold raw26395step1 raw26395step0; decide +kernel
      have hl : raw26395step1Labels = raw26395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

theorem canonical26396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26396 raw26396Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26396 raw26396Labels = mixedMoment B raw26396step0 raw26396step0Labels := by
      have ha : raw26396step0 = (fun i j => raw26396 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26396step0 raw26396; decide +kernel
      have hl : raw26396step0Labels = raw26396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26396 raw26396Labels permutation170 permutation2
    mixedMoment B raw26396step0 raw26396step0Labels = mixedMoment B raw26396step1 raw26396step1Labels := by
      have ha : raw26396step1 = -raw26396step0 := by apply Matrix.ext; change ∀ i j, raw26396step1 i j = -(raw26396step0 i j); unfold raw26396step1 raw26396step0; decide +kernel
      have hl : raw26396step1Labels = raw26396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

theorem canonical26397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26397 raw26397Labels = mixedMoment B node3244 node3244Labels := by
  calc
    mixedMoment B raw26397 raw26397Labels = mixedMoment B raw26397step0 raw26397step0Labels := by
      have ha : raw26397step0 = -raw26397 := by apply Matrix.ext; change ∀ i j, raw26397step0 i j = -(raw26397 i j); unfold raw26397step0 raw26397; decide +kernel
      have hl : raw26397step0Labels = raw26397Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3244 node3244Labels := by rfl

theorem canonical26409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26409 raw26409Labels = mixedMoment B node1256 node1256Labels := by
  calc
    mixedMoment B raw26409 raw26409Labels = mixedMoment B raw26409step0 raw26409step0Labels := by
      have ha : raw26409step0 = (fun i j => raw26409 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26409step0 raw26409; decide +kernel
      have hl : raw26409step0Labels = raw26409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26409 raw26409Labels permutation170 permutation2
    _ = mixedMoment B node1256 node1256Labels := by rfl

theorem canonical26410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26410 raw26410Labels = mixedMoment B node2628 node2628Labels := by
  calc
    mixedMoment B raw26410 raw26410Labels = mixedMoment B raw26410step0 raw26410step0Labels := by
      have ha : raw26410step0 = (fun i j => raw26410 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26410step0 raw26410; decide +kernel
      have hl : raw26410step0Labels = raw26410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26410 raw26410Labels permutation170 permutation2
    _ = mixedMoment B node2628 node2628Labels := by rfl

theorem canonical26411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26411 raw26411Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26411 raw26411Labels = mixedMoment B raw26411step0 raw26411step0Labels := by
      have ha : raw26411step0 = (fun i j => raw26411 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26411step0 raw26411; decide +kernel
      have hl : raw26411step0Labels = raw26411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26411 raw26411Labels permutation156 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

theorem canonical26412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26412 raw26412Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26412 raw26412Labels = mixedMoment B raw26412step0 raw26412step0Labels := by
      have ha : raw26412step0 = (fun i j => raw26412 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26412step0 raw26412; decide +kernel
      have hl : raw26412step0Labels = raw26412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26412 raw26412Labels permutation162 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

theorem canonical26413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26413 raw26413Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26413 raw26413Labels = mixedMoment B raw26413step0 raw26413step0Labels := by
      have ha : raw26413step0 = (fun i j => raw26413 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26413step0 raw26413; decide +kernel
      have hl : raw26413step0Labels = raw26413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26413 raw26413Labels permutation168 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

theorem canonical26414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26414 raw26414Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26414 raw26414Labels = mixedMoment B raw26414step0 raw26414step0Labels := by
      have ha : raw26414step0 = (fun i j => raw26414 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26414step0 raw26414; decide +kernel
      have hl : raw26414step0Labels = raw26414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26414 raw26414Labels permutation246 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical26415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26415 raw26415Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw26415 raw26415Labels = mixedMoment B raw26415step0 raw26415step0Labels := by
      have ha : raw26415step0 = (fun i j => raw26415 (permutation246 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26415step0 raw26415; decide +kernel
      have hl : raw26415step0Labels = raw26415Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26415 raw26415Labels permutation246 permutation0
    _ = mixedMoment B node4087 node4087Labels := by rfl

theorem canonical26416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26416 raw26416Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw26416 raw26416Labels = mixedMoment B raw26416step0 raw26416step0Labels := by
      have ha : raw26416step0 = (fun i j => raw26416 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26416step0 raw26416; decide +kernel
      have hl : raw26416step0Labels = raw26416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26416 raw26416Labels permutation246 permutation2
    mixedMoment B raw26416step0 raw26416step0Labels = mixedMoment B raw26416step1 raw26416step1Labels := by
      have ha : raw26416step1 = -raw26416step0 := by apply Matrix.ext; change ∀ i j, raw26416step1 i j = -(raw26416step0 i j); unfold raw26416step1 raw26416step0; decide +kernel
      have hl : raw26416step1Labels = raw26416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1644 node1644Labels := by rfl

theorem canonical26417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26417 raw26417Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26417 raw26417Labels = mixedMoment B raw26417step0 raw26417step0Labels := by
      have ha : raw26417step0 = (fun i j => raw26417 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26417step0 raw26417; decide +kernel
      have hl : raw26417step0Labels = raw26417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26417 raw26417Labels permutation160 permutation4
    mixedMoment B raw26417step0 raw26417step0Labels = mixedMoment B raw26417step1 raw26417step1Labels := by
      have ha : raw26417step1 = -raw26417step0 := by apply Matrix.ext; change ∀ i j, raw26417step1 i j = -(raw26417step0 i j); unfold raw26417step1 raw26417step0; decide +kernel
      have hl : raw26417step1Labels = raw26417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26418 raw26418Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26418 raw26418Labels = mixedMoment B raw26418step0 raw26418step0Labels := by
      have ha : raw26418step0 = (fun i j => raw26418 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26418step0 raw26418; decide +kernel
      have hl : raw26418step0Labels = raw26418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26418 raw26418Labels permutation154 permutation4
    mixedMoment B raw26418step0 raw26418step0Labels = mixedMoment B raw26418step1 raw26418step1Labels := by
      have ha : raw26418step1 = -raw26418step0 := by apply Matrix.ext; change ∀ i j, raw26418step1 i j = -(raw26418step0 i j); unfold raw26418step1 raw26418step0; decide +kernel
      have hl : raw26418step1Labels = raw26418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26419 raw26419Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26419 raw26419Labels = mixedMoment B raw26419step0 raw26419step0Labels := by
      have ha : raw26419step0 = (fun i j => raw26419 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26419step0 raw26419; decide +kernel
      have hl : raw26419step0Labels = raw26419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26419 raw26419Labels permutation152 permutation4
    mixedMoment B raw26419step0 raw26419step0Labels = mixedMoment B raw26419step1 raw26419step1Labels := by
      have ha : raw26419step1 = -raw26419step0 := by apply Matrix.ext; change ∀ i j, raw26419step1 i j = -(raw26419step0 i j); unfold raw26419step1 raw26419step0; decide +kernel
      have hl : raw26419step1Labels = raw26419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26420 raw26420Labels = mixedMoment B node2508 node2508Labels := by
  calc
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical26421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26421 raw26421Labels = mixedMoment B node1233 node1233Labels := by
  calc
    _ = mixedMoment B node1233 node1233Labels := by rfl

theorem canonical26422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26422 raw26422Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw26422 raw26422Labels = mixedMoment B raw26422step0 raw26422step0Labels := by
      have ha : raw26422step0 = (fun i j => raw26422 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26422step0 raw26422; decide +kernel
      have hl : raw26422step0Labels = raw26422Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26422 raw26422Labels permutation161 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

theorem canonical26423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26423 raw26423Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw26423 raw26423Labels = mixedMoment B raw26423step0 raw26423step0Labels := by
      have ha : raw26423step0 = (fun i j => raw26423 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26423step0 raw26423; decide +kernel
      have hl : raw26423step0Labels = raw26423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26423 raw26423Labels permutation155 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

theorem canonical26424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26424 raw26424Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw26424 raw26424Labels = mixedMoment B raw26424step0 raw26424step0Labels := by
      have ha : raw26424step0 = (fun i j => raw26424 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26424step0 raw26424; decide +kernel
      have hl : raw26424step0Labels = raw26424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26424 raw26424Labels permutation153 permutation2
    _ = mixedMoment B node1127 node1127Labels := by rfl

theorem canonical26425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26425 raw26425Labels = mixedMoment B node1126 node1126Labels := by
  calc
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical26426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26426 raw26426Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26426 raw26426Labels = mixedMoment B raw26426step0 raw26426step0Labels := by
      have ha : raw26426step0 = (fun i j => raw26426 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26426step0 raw26426; decide +kernel
      have hl : raw26426step0Labels = raw26426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26426 raw26426Labels permutation260 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

theorem canonical26427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26427 raw26427Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26427 raw26427Labels = mixedMoment B raw26427step0 raw26427step0Labels := by
      have ha : raw26427step0 = (fun i j => raw26427 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26427step0 raw26427; decide +kernel
      have hl : raw26427step0Labels = raw26427Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26427 raw26427Labels permutation174 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical26428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26428 raw26428Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26428 raw26428Labels = mixedMoment B raw26428step0 raw26428step0Labels := by
      have ha : raw26428step0 = (fun i j => raw26428 (permutation198 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26428step0 raw26428; decide +kernel
      have hl : raw26428step0Labels = raw26428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26428 raw26428Labels permutation198 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical26429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26429 raw26429Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26429 raw26429Labels = mixedMoment B raw26429step0 raw26429step0Labels := by
      have ha : raw26429step0 = (fun i j => raw26429 (permutation222 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26429step0 raw26429; decide +kernel
      have hl : raw26429step0Labels = raw26429Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26429 raw26429Labels permutation222 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical26430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26430 raw26430Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26430 raw26430Labels = mixedMoment B raw26430step0 raw26430step0Labels := by
      have hz : ∀ j, raw26430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26430step0 = (fun i j => raw26430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26430step0 raw26430; decide +kernel
      have hl : raw26430step0Labels = raw26430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26430 raw26430Labels permutation520 hz
    mixedMoment B raw26430step0 raw26430step0Labels = mixedMoment B raw26430step1 raw26430step1Labels := by
      have ha : raw26430step1 = (fun i j => raw26430step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26430step1 raw26430step0; decide +kernel
      have hl : raw26430step1Labels = raw26430step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26430step0 raw26430step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical26431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26431 raw26431Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26431 raw26431Labels = mixedMoment B raw26431step0 raw26431step0Labels := by
      have ha : raw26431step0 = (fun i j => raw26431 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26431step0 raw26431; decide +kernel
      have hl : raw26431step0Labels = raw26431Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26431 raw26431Labels permutation260 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical26432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26432 raw26432Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw26432 raw26432Labels = mixedMoment B raw26432step0 raw26432step0Labels := by
      have hz : ∀ j, raw26432 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26432step0 = (fun i j => raw26432 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26432step0 raw26432; decide +kernel
      have hl : raw26432step0Labels = raw26432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26432 raw26432Labels permutation520 hz
    mixedMoment B raw26432step0 raw26432step0Labels = mixedMoment B raw26432step1 raw26432step1Labels := by
      have ha : raw26432step1 = (fun i j => raw26432step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26432step1 raw26432step0; decide +kernel
      have hl : raw26432step1Labels = raw26432step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26432step0 raw26432step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5205 raw5205Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5205 raw5205Labels = mixedMoment B raw5205step0 raw5205step0Labels := by
      have hz : ∀ j, raw5205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5205step0 = (fun i j => raw5205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5205step0 raw5205; decide +kernel
      have hl : raw5205step0Labels = raw5205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205 raw5205Labels permutation520 hz
    mixedMoment B raw5205step0 raw5205step0Labels = mixedMoment B raw5205step1 raw5205step1Labels := by
      have hz : ∀ j, raw5205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5205step1 = (fun i j => raw5205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5205step1 raw5205step0; decide +kernel
      have hl : raw5205step1Labels = raw5205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step0 raw5205step0Labels permutation80 hz
    mixedMoment B raw5205step1 raw5205step1Labels = mixedMoment B raw5205step2 raw5205step2Labels := by
      have hz : ∀ j, raw5205step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5205step2 = (fun i j => raw5205step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5205step2 raw5205step1; decide +kernel
      have hl : raw5205step2Labels = raw5205step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step1 raw5205step1Labels permutation14 hz
    mixedMoment B raw5205step2 raw5205step2Labels = mixedMoment B raw5205step3 raw5205step3Labels := by
      have hz : ∀ i, raw5205step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5205step3 = (fun i j => raw5205step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5205step3 raw5205step2; decide +kernel
      have hl : raw5205step3Labels = (fun j => raw5205step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5205step2 raw5205step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

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

theorem canonical11538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11538 raw11538Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11538 raw11538Labels = mixedMoment B raw11538step0 raw11538step0Labels := by
      have hz : ∀ j, raw11538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11538step0 = (fun i j => raw11538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11538step0 raw11538; decide +kernel
      have hl : raw11538step0Labels = raw11538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11538 raw11538Labels permutation346 hz
    mixedMoment B raw11538step0 raw11538step0Labels = mixedMoment B raw11538step1 raw11538step1Labels := by
      have hz : ∀ i, raw11538step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11538step1 = (fun i j => raw11538step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11538step1 raw11538step0; decide +kernel
      have hl : raw11538step1Labels = (fun j => raw11538step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11538step0 raw11538step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11539 raw11539Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11539 raw11539Labels = mixedMoment B raw11539step0 raw11539step0Labels := by
      have hz : ∀ j, raw11539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11539step0 = (fun i j => raw11539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11539step0 raw11539; decide +kernel
      have hl : raw11539step0Labels = raw11539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11539 raw11539Labels permutation265 hz
    mixedMoment B raw11539step0 raw11539step0Labels = mixedMoment B raw11539step1 raw11539step1Labels := by
      have hz : ∀ i, raw11539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11539step1 = (fun i j => raw11539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11539step1 raw11539step0; decide +kernel
      have hl : raw11539step1Labels = (fun j => raw11539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11539step0 raw11539step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11540 raw11540Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw11540 raw11540Labels = mixedMoment B raw11540step0 raw11540step0Labels := by
      have hz : ∀ j, raw11540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11540step0 = (fun i j => raw11540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11540step0 raw11540; decide +kernel
      have hl : raw11540step0Labels = raw11540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540 raw11540Labels permutation434 hz
    mixedMoment B raw11540step0 raw11540step0Labels = mixedMoment B raw11540step1 raw11540step1Labels := by
      have hz : ∀ j, raw11540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11540step1 = (fun i j => raw11540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11540step1 raw11540step0; decide +kernel
      have hl : raw11540step1Labels = raw11540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step0 raw11540step0Labels permutation80 hz
    mixedMoment B raw11540step1 raw11540step1Labels = mixedMoment B raw11540step2 raw11540step2Labels := by
      have hz : ∀ j, raw11540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11540step2 = (fun i j => raw11540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11540step2 raw11540step1; decide +kernel
      have hl : raw11540step2Labels = raw11540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step1 raw11540step1Labels permutation14 hz
    mixedMoment B raw11540step2 raw11540step2Labels = mixedMoment B raw11540step3 raw11540step3Labels := by
      have hz : ∀ i, raw11540step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11540step3 = (fun i j => raw11540step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11540step3 raw11540step2; decide +kernel
      have hl : raw11540step3Labels = (fun j => raw11540step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11540step2 raw11540step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

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

theorem zero687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node687 node687Labels = 0 := by
  exact mixedMoment_order_one B hB node687 node687Labels 1
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

theorem sound662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node662 node662Labels = Sparse.eval nodeValue662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 662) = mixedMoment B node662 node662Labels := rfl
  simpa [nodeValue662, Sparse.eval] using hc.symm

theorem sound681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node681 node681Labels = Sparse.eval nodeValue681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 681) = mixedMoment B node681 node681Labels := rfl
  simpa [nodeValue681, Sparse.eval] using hc.symm

theorem sound682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node682 node682Labels = Sparse.eval nodeValue682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 682) = mixedMoment B node682 node682Labels := rfl
  simpa [nodeValue682, Sparse.eval] using hc.symm

theorem sound687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node687 node687Labels = Sparse.eval nodeValue687 (mixedVector B) := by
  simpa only [nodeValue687, Sparse.eval_nil] using zero687 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node766 node766Labels = 0 := by
  exact mixedMoment_order_one B hB node766 node766Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

theorem sound737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node737 node737Labels = Sparse.eval nodeValue737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 737) = mixedMoment B node737 node737Labels := rfl
  simpa [nodeValue737, Sparse.eval] using hc.symm

theorem sound739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node739 node739Labels = Sparse.eval nodeValue739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 739) = mixedMoment B node739 node739Labels := rfl
  simpa [nodeValue739, Sparse.eval] using hc.symm

theorem sound760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node760 node760Labels = Sparse.eval nodeValue760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 760) = mixedMoment B node760 node760Labels := rfl
  simpa [nodeValue760, Sparse.eval] using hc.symm

theorem sound761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node761 node761Labels = Sparse.eval nodeValue761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 761) = mixedMoment B node761 node761Labels := rfl
  simpa [nodeValue761, Sparse.eval] using hc.symm

theorem sound766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node766 node766Labels = Sparse.eval nodeValue766 (mixedVector B) := by
  simpa only [nodeValue766, Sparse.eval_nil] using zero766 B _hB _hF

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

theorem zero805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = 0 := by
  exact mixedMoment_order_one B hB node805 node805Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = 0 := by
  exact mixedMoment_order_one B hB node810 node810Labels 1
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

theorem sound798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node798 node798Labels = Sparse.eval nodeValue798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 798) = mixedMoment B node798 node798Labels := rfl
  simpa [nodeValue798, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = Sparse.eval nodeValue805 (mixedVector B) := by
  simpa only [nodeValue805, Sparse.eval_nil] using zero805 B _hB _hF

theorem sound810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = Sparse.eval nodeValue810 (mixedVector B) := by
  simpa only [nodeValue810, Sparse.eval_nil] using zero810 B _hB _hF

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

theorem zero850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node850 node850Labels = 0 := by
  exact mixedMoment_order_one B hB node850 node850Labels 1
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

theorem sound840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node840 node840Labels = Sparse.eval nodeValue840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 840) = mixedMoment B node840 node840Labels := rfl
  simpa [nodeValue840, Sparse.eval] using hc.symm

theorem sound841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node841 node841Labels = Sparse.eval nodeValue841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 841) = mixedMoment B node841 node841Labels := rfl
  simpa [nodeValue841, Sparse.eval] using hc.symm

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

theorem sound850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node850 node850Labels = Sparse.eval nodeValue850 (mixedVector B) := by
  simpa only [nodeValue850, Sparse.eval_nil] using zero850 B _hB _hF

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

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

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

theorem zero1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = 0 := by
  exact mixedMoment_alpha B hF node1038 node1038Labels 1 permutation161
    (by decide +kernel)

theorem zero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = 0 := by
  exact mixedMoment_order_one B hB node1081 node1081Labels 1
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

theorem sound1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = Sparse.eval nodeValue1038 (mixedVector B) := by
  simpa only [nodeValue1038, Sparse.eval_nil] using zero1038 B _hB _hF

theorem sound1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1056 node1056Labels = Sparse.eval nodeValue1056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1056) = mixedMoment B node1056 node1056Labels := rfl
  simpa [nodeValue1056, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = Sparse.eval nodeValue1081 (mixedVector B) := by
  simpa only [nodeValue1081, Sparse.eval_nil] using zero1081 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1126 node1126Labels = Sparse.eval nodeValue1126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1126) = mixedMoment B node1126 node1126Labels := rfl
  simpa [nodeValue1126, Sparse.eval] using hc.symm

theorem sound1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1127 node1127Labels = Sparse.eval nodeValue1127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1127) = mixedMoment B node1127 node1127Labels := rfl
  simpa [nodeValue1127, Sparse.eval] using hc.symm

theorem sound1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1130 node1130Labels = Sparse.eval nodeValue1130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1130) = mixedMoment B node1130 node1130Labels := rfl
  simpa [nodeValue1130, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1233 node1233Labels = Sparse.eval nodeValue1233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1233) = mixedMoment B node1233 node1233Labels := rfl
  simpa [nodeValue1233, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1256 node1256Labels = Sparse.eval nodeValue1256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1256) = mixedMoment B node1256 node1256Labels := rfl
  simpa [nodeValue1256, Sparse.eval] using hc.symm

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

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

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

theorem sound1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1316 node1316Labels = Sparse.eval nodeValue1316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1316) = mixedMoment B node1316 node1316Labels := rfl
  simpa [nodeValue1316, Sparse.eval] using hc.symm

theorem sound1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1319 node1319Labels = Sparse.eval nodeValue1319 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1319) = mixedMoment B node1319 node1319Labels := rfl
  simpa [nodeValue1319, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1366 node1366Labels = Sparse.eval nodeValue1366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1366) = mixedMoment B node1366 node1366Labels := rfl
  simpa [nodeValue1366, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

theorem sound1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1648 node1648Labels = Sparse.eval nodeValue1648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1648) = mixedMoment B node1648 node1648Labels := rfl
  simpa [nodeValue1648, Sparse.eval] using hc.symm

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

theorem zero1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = 0 := by
  exact mixedMoment_alpha B hF node1698 node1698Labels 1 permutation434
    (by decide +kernel)

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

theorem sound1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = Sparse.eval nodeValue1698 (mixedVector B) := by
  simpa only [nodeValue1698, Sparse.eval_nil] using zero1698 B _hB _hF

theorem sound1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1699 node1699Labels = Sparse.eval nodeValue1699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1699) = mixedMoment B node1699 node1699Labels := rfl
  simpa [nodeValue1699, Sparse.eval] using hc.symm

theorem sound1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1700 node1700Labels = Sparse.eval nodeValue1700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1700) = mixedMoment B node1700 node1700Labels := rfl
  simpa [nodeValue1700, Sparse.eval] using hc.symm

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

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

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound2628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2628 node2628Labels = Sparse.eval nodeValue2628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2628) = mixedMoment B node2628 node2628Labels := rfl
  simpa [nodeValue2628, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

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

theorem sound2747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2747 node2747Labels = Sparse.eval nodeValue2747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2747) = mixedMoment B node2747 node2747Labels := rfl
  simpa [nodeValue2747, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

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

theorem sound3057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3057 node3057Labels = Sparse.eval nodeValue3057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3057) = mixedMoment B node3057 node3057Labels := rfl
  simpa [nodeValue3057, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3072 node3072Labels = Sparse.eval nodeValue3072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3072) = mixedMoment B node3072 node3072Labels := rfl
  simpa [nodeValue3072, Sparse.eval] using hc.symm

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

theorem sound3239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3239 node3239Labels = Sparse.eval nodeValue3239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3239) = mixedMoment B node3239 node3239Labels := rfl
  simpa [nodeValue3239, Sparse.eval] using hc.symm

theorem sound3244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3244 node3244Labels = Sparse.eval nodeValue3244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3244) = mixedMoment B node3244 node3244Labels := rfl
  simpa [nodeValue3244, Sparse.eval] using hc.symm

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

theorem sound3286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3286 node3286Labels = Sparse.eval nodeValue3286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3286) = mixedMoment B node3286 node3286Labels := rfl
  simpa [nodeValue3286, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

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

theorem sound4057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4057 node4057Labels = Sparse.eval nodeValue4057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4057) = mixedMoment B node4057 node4057Labels := rfl
  simpa [nodeValue4057, Sparse.eval] using hc.symm

theorem sound4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4058 node4058Labels = Sparse.eval nodeValue4058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4058) = mixedMoment B node4058 node4058Labels := rfl
  simpa [nodeValue4058, Sparse.eval] using hc.symm

theorem sound4059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4059 node4059Labels = Sparse.eval nodeValue4059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4059) = mixedMoment B node4059 node4059Labels := rfl
  simpa [nodeValue4059, Sparse.eval] using hc.symm

theorem sound4063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4063 node4063Labels = Sparse.eval nodeValue4063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4063) = mixedMoment B node4063 node4063Labels := rfl
  simpa [nodeValue4063, Sparse.eval] using hc.symm

theorem sound4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4064 node4064Labels = Sparse.eval nodeValue4064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4064) = mixedMoment B node4064 node4064Labels := rfl
  simpa [nodeValue4064, Sparse.eval] using hc.symm

theorem sound4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4065 node4065Labels = Sparse.eval nodeValue4065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4065) = mixedMoment B node4065 node4065Labels := rfl
  simpa [nodeValue4065, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node597 node597Labels = Sparse.eval nodeValue597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 597) = mixedMoment B node597 node597Labels := rfl
  simpa [nodeValue597, Sparse.eval] using hc.symm

theorem sound637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node637 node637Labels = Sparse.eval nodeValue637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 637) = mixedMoment B node637 node637Labels := rfl
  simpa [nodeValue637, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1816 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 1) (sourceB1816 + difference 1 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 1) (sourceB1816 + difference 1 0) sourceC1816) = raw26244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26244; decide +kernel
    rw [ha]
    exact (canonical26244 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 2) (sourceB1816 + difference 2 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 2) (sourceB1816 + difference 2 0) sourceC1816) = raw26245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26245; decide +kernel
    rw [ha]
    exact (canonical26245 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 3) (sourceB1816 + difference 3 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 3) (sourceB1816 + difference 3 0) sourceC1816) = raw26246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26246; decide +kernel
    rw [ha]
    exact (canonical26246 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 4) (sourceB1816 + difference 4 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 4) (sourceB1816 + difference 4 0) sourceC1816) = raw26247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26247; decide +kernel
    rw [ha]
    exact (canonical26247 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1816 + difference 0 5) (sourceB1816 + difference 5 0) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1816 + difference 0 5) (sourceB1816 + difference 5 0) sourceC1816) = raw26248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26248; decide +kernel
    rw [ha]
    exact (canonical26248 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 0) (sourceB1816 + difference 0 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 0) (sourceB1816 + difference 0 1) sourceC1816) = raw26249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26249; decide +kernel
    rw [ha]
    exact (canonical26249 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 2) (sourceB1816 + difference 2 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 766) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 2) (sourceB1816 + difference 2 1) sourceC1816) = raw26250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26250; decide +kernel
    rw [ha]
    exact (canonical26250 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 3) (sourceB1816 + difference 3 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 3) (sourceB1816 + difference 3 1) sourceC1816) = raw26251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26251; decide +kernel
    rw [ha]
    exact (canonical26251 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 4) (sourceB1816 + difference 4 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 4) (sourceB1816 + difference 4 1) sourceC1816) = raw26252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26252; decide +kernel
    rw [ha]
    exact (canonical26252 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1816 + difference 1 5) (sourceB1816 + difference 5 1) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1816 + difference 1 5) (sourceB1816 + difference 5 1) sourceC1816) = raw26253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26253; decide +kernel
    rw [ha]
    exact (canonical26253 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 0) (sourceB1816 + difference 0 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 0) (sourceB1816 + difference 0 2) sourceC1816) = raw26254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26254; decide +kernel
    rw [ha]
    exact (canonical26254 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 1) (sourceB1816 + difference 1 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 798) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 1) (sourceB1816 + difference 1 2) sourceC1816) = raw26255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26255; decide +kernel
    rw [ha]
    exact (canonical26255 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 3) (sourceB1816 + difference 3 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 3) (sourceB1816 + difference 3 2) sourceC1816) = raw26256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26256; decide +kernel
    rw [ha]
    exact (canonical26256 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 4) (sourceB1816 + difference 4 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 4) (sourceB1816 + difference 4 2) sourceC1816) = raw26257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26257; decide +kernel
    rw [ha]
    exact (canonical26257 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1816 + difference 2 5) (sourceB1816 + difference 5 2) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1816 + difference 2 5) (sourceB1816 + difference 5 2) sourceC1816) = raw26258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26258; decide +kernel
    rw [ha]
    exact (canonical26258 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 0) (sourceB1816 + difference 0 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 0) (sourceB1816 + difference 0 3) sourceC1816) = raw26259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26259; decide +kernel
    rw [ha]
    exact (canonical26259 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 1) (sourceB1816 + difference 1 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 841) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 1) (sourceB1816 + difference 1 3) sourceC1816) = raw26260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26260; decide +kernel
    rw [ha]
    exact (canonical26260 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 2) (sourceB1816 + difference 2 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 761) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 2) (sourceB1816 + difference 2 3) sourceC1816) = raw26261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26261; decide +kernel
    rw [ha]
    exact (canonical26261 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 4) (sourceB1816 + difference 4 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 4) (sourceB1816 + difference 4 3) sourceC1816) = raw26262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26262; decide +kernel
    rw [ha]
    exact (canonical26262 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1816 + difference 3 5) (sourceB1816 + difference 5 3) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 3 5) (sourceB1816 + difference 5 3) sourceC1816) = raw26263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26263; decide +kernel
    rw [ha]
    exact (canonical26263 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 0) (sourceB1816 + difference 0 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 0) (sourceB1816 + difference 0 4) sourceC1816) = raw26264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26264; decide +kernel
    rw [ha]
    exact (canonical26264 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 1) (sourceB1816 + difference 1 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 841) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 1) (sourceB1816 + difference 1 4) sourceC1816) = raw26265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26265; decide +kernel
    rw [ha]
    exact (canonical26265 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 2) (sourceB1816 + difference 2 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 761) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 2) (sourceB1816 + difference 2 4) sourceC1816) = raw26266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26266; decide +kernel
    rw [ha]
    exact (canonical26266 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 3) (sourceB1816 + difference 3 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 3) (sourceB1816 + difference 3 4) sourceC1816) = raw26267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26267; decide +kernel
    rw [ha]
    exact (canonical26267 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1816 + difference 4 5) (sourceB1816 + difference 5 4) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1816 + difference 4 5) (sourceB1816 + difference 5 4) sourceC1816) = raw26268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26268; decide +kernel
    rw [ha]
    exact (canonical26268 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 0) (sourceB1816 + difference 0 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 681) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 0) (sourceB1816 + difference 0 5) sourceC1816) = raw26269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26269; decide +kernel
    rw [ha]
    exact (canonical26269 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 1) (sourceB1816 + difference 1 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 840) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 1) (sourceB1816 + difference 1 5) sourceC1816) = raw26270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26270; decide +kernel
    rw [ha]
    exact (canonical26270 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 2) (sourceB1816 + difference 2 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 760) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 2) (sourceB1816 + difference 2 5) sourceC1816) = raw26271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26271; decide +kernel
    rw [ha]
    exact (canonical26271 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 3) (sourceB1816 + difference 3 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 3) (sourceB1816 + difference 3 5) sourceC1816) = raw26272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26272; decide +kernel
    rw [ha]
    exact (canonical26272 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1816 + difference 5 4) (sourceB1816 + difference 4 5) sourceC1816) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1816 + difference 5 4) (sourceB1816 + difference 4 5) sourceC1816) = raw26273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1816 sourceB1816 sourceC1816 difference raw26273; decide +kernel
    rw [ha]
    exact (canonical26273 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1816 sourceB1816 sourceC1816
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1816, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1817 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1817 + difference 0 1) (sourceB1817 + difference 1 0) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1817 + difference 0 1) (sourceB1817 + difference 1 0) sourceC1817) = raw26274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26274; decide +kernel
    rw [ha]
    exact (canonical26274 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1817 + difference 1 1) (sourceB1817 + difference 1 1) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1817 + difference 1 1) (sourceB1817 + difference 1 1) sourceC1817) = raw26275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26275; decide +kernel
    rw [ha]
    exact (canonical26275 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1817 + difference 2 1) (sourceB1817 + difference 1 2) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1817 + difference 2 1) (sourceB1817 + difference 1 2) sourceC1817) = raw26276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26276; decide +kernel
    rw [ha]
    exact (canonical26276 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1817 + difference 3 1) (sourceB1817 + difference 1 3) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1817 + difference 3 1) (sourceB1817 + difference 1 3) sourceC1817) = raw26277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26277; decide +kernel
    rw [ha]
    exact (canonical26277 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1817 + difference 4 1) (sourceB1817 + difference 1 4) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA1817 + difference 4 1) (sourceB1817 + difference 1 4) sourceC1817) = raw26278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26278; decide +kernel
    rw [ha]
    exact (canonical26278 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1817 + difference 5 1) (sourceB1817 + difference 1 5) sourceC1817) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1817 + difference 5 1) (sourceB1817 + difference 1 5) sourceC1817) = raw26279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1817 sourceB1817 sourceC1817 difference raw26279; decide +kernel
    rw [ha]
    exact (canonical26279 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1817 + sourceB1817) sourceC1817) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1817 + sourceB1817) sourceC1817) = raw26280 := by
      apply Matrix.ext; unfold doubleCharges sourceA1817 sourceB1817 sourceC1817 raw26280; decide +kernel
    rw [ha]
    exact (canonical26280 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1817 sourceB1817 sourceC1817
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1817, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1821 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 1) (sourceB1821 + difference 1 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 1) (sourceB1821 + difference 1 0) sourceC1821) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 2) (sourceB1821 + difference 2 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 2) (sourceB1821 + difference 2 0) sourceC1821) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 3) (sourceB1821 + difference 3 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 3) (sourceB1821 + difference 3 0) sourceC1821) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 4) (sourceB1821 + difference 4 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 4) (sourceB1821 + difference 4 0) sourceC1821) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1821 + difference 0 5) (sourceB1821 + difference 5 0) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1821 + difference 0 5) (sourceB1821 + difference 5 0) sourceC1821) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 0) (sourceB1821 + difference 0 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 0) (sourceB1821 + difference 0 1) sourceC1821) = raw26354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26354; decide +kernel
    rw [ha]
    exact (canonical26354 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 2) (sourceB1821 + difference 2 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 2) (sourceB1821 + difference 2 1) sourceC1821) = raw26355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26355; decide +kernel
    rw [ha]
    exact (canonical26355 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 3) (sourceB1821 + difference 3 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 3) (sourceB1821 + difference 3 1) sourceC1821) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 4) (sourceB1821 + difference 4 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 4) (sourceB1821 + difference 4 1) sourceC1821) = raw26356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26356; decide +kernel
    rw [ha]
    exact (canonical26356 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1821 + difference 1 5) (sourceB1821 + difference 5 1) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1821 + difference 1 5) (sourceB1821 + difference 5 1) sourceC1821) = raw14360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14360; decide +kernel
    rw [ha]
    exact (canonical14360 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 0) (sourceB1821 + difference 0 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 0) (sourceB1821 + difference 0 2) sourceC1821) = raw26357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26357; decide +kernel
    rw [ha]
    exact (canonical26357 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 1) (sourceB1821 + difference 1 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 1) (sourceB1821 + difference 1 2) sourceC1821) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 3) (sourceB1821 + difference 3 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 3) (sourceB1821 + difference 3 2) sourceC1821) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 4) (sourceB1821 + difference 4 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 4) (sourceB1821 + difference 4 2) sourceC1821) = raw26359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26359; decide +kernel
    rw [ha]
    exact (canonical26359 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1821 + difference 2 5) (sourceB1821 + difference 5 2) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1821 + difference 2 5) (sourceB1821 + difference 5 2) sourceC1821) = raw14364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14364; decide +kernel
    rw [ha]
    exact (canonical14364 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 0) (sourceB1821 + difference 0 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 0) (sourceB1821 + difference 0 3) sourceC1821) = raw26360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26360; decide +kernel
    rw [ha]
    exact (canonical26360 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 1) (sourceB1821 + difference 1 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 1) (sourceB1821 + difference 1 3) sourceC1821) = raw26361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26361; decide +kernel
    rw [ha]
    exact (canonical26361 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 2) (sourceB1821 + difference 2 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 2) (sourceB1821 + difference 2 3) sourceC1821) = raw26362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26362; decide +kernel
    rw [ha]
    exact (canonical26362 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 4) (sourceB1821 + difference 4 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 4) (sourceB1821 + difference 4 3) sourceC1821) = raw26363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw26363; decide +kernel
    rw [ha]
    exact (canonical26363 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1821 + difference 3 5) (sourceB1821 + difference 5 3) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 3 5) (sourceB1821 + difference 5 3) sourceC1821) = raw14368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14368; decide +kernel
    rw [ha]
    exact (canonical14368 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 0) (sourceB1821 + difference 0 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 0) (sourceB1821 + difference 0 4) sourceC1821) = raw23785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23785; decide +kernel
    rw [ha]
    exact (canonical23785 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 1) (sourceB1821 + difference 1 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 1) (sourceB1821 + difference 1 4) sourceC1821) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 2) (sourceB1821 + difference 2 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 2) (sourceB1821 + difference 2 4) sourceC1821) = raw23787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw23787; decide +kernel
    rw [ha]
    exact (canonical23787 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 3) (sourceB1821 + difference 3 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 3) (sourceB1821 + difference 3 4) sourceC1821) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1821 + difference 4 5) (sourceB1821 + difference 5 4) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1821 + difference 4 5) (sourceB1821 + difference 5 4) sourceC1821) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 0) (sourceB1821 + difference 0 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 0) (sourceB1821 + difference 0 5) sourceC1821) = raw22307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22307; decide +kernel
    rw [ha]
    exact (canonical22307 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 1) (sourceB1821 + difference 1 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 1) (sourceB1821 + difference 1 5) sourceC1821) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 2) (sourceB1821 + difference 2 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 2) (sourceB1821 + difference 2 5) sourceC1821) = raw22309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw22309; decide +kernel
    rw [ha]
    exact (canonical22309 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 3) (sourceB1821 + difference 3 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 3) (sourceB1821 + difference 3 5) sourceC1821) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1821 + difference 5 4) (sourceB1821 + difference 4 5) sourceC1821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1821 + difference 5 4) (sourceB1821 + difference 4 5) sourceC1821) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1821 sourceB1821 sourceC1821 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1821 sourceB1821 sourceC1821
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1821, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1822 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 0) (sourceB1822 + difference 0 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 0) (sourceB1822 + difference 0 0) sourceC1822) = raw26364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26364; decide +kernel
    rw [ha]
    exact (canonical26364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 1) (sourceB1822 + difference 1 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3057) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 1) (sourceB1822 + difference 1 0) sourceC1822) = raw26365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26365; decide +kernel
    rw [ha]
    exact (canonical26365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 2) (sourceB1822 + difference 2 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 2) (sourceB1822 + difference 2 0) sourceC1822) = raw26366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26366; decide +kernel
    rw [ha]
    exact (canonical26366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 3) (sourceB1822 + difference 3 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 3) (sourceB1822 + difference 3 0) sourceC1822) = raw26367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26367; decide +kernel
    rw [ha]
    exact (canonical26367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 4) (sourceB1822 + difference 4 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 4) (sourceB1822 + difference 4 0) sourceC1822) = raw26368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26368; decide +kernel
    rw [ha]
    exact (canonical26368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1822 + difference 0 5) (sourceB1822 + difference 5 0) sourceC1822) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1822 + difference 0 5) (sourceB1822 + difference 5 0) sourceC1822) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1822 sourceB1822 sourceC1822 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1822 + sourceB1822) sourceC1822) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1822 + sourceB1822) sourceC1822) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1822 sourceB1822 sourceC1822 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1822 sourceB1822 sourceC1822
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1822, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1823 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1823 + difference 0 5) (sourceB1823 + difference 5 0) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1823 + difference 0 5) (sourceB1823 + difference 5 0) sourceC1823) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1823 + difference 1 5) (sourceB1823 + difference 5 1) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1823 + difference 1 5) (sourceB1823 + difference 5 1) sourceC1823) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1823 + difference 2 5) (sourceB1823 + difference 5 2) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 2 5) (sourceB1823 + difference 5 2) sourceC1823) = raw26372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26372; decide +kernel
    rw [ha]
    exact (canonical26372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1823 + difference 3 5) (sourceB1823 + difference 5 3) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 3 5) (sourceB1823 + difference 5 3) sourceC1823) = raw26373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26373; decide +kernel
    rw [ha]
    exact (canonical26373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1823 + difference 4 5) (sourceB1823 + difference 5 4) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1823 + difference 4 5) (sourceB1823 + difference 5 4) sourceC1823) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1823 + difference 5 5) (sourceB1823 + difference 5 5) sourceC1823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1823 + difference 5 5) (sourceB1823 + difference 5 5) sourceC1823) = raw26364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1823 sourceB1823 sourceC1823 difference raw26364; decide +kernel
    rw [ha]
    exact (canonical26364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1823 + sourceB1823) sourceC1823) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1823 + sourceB1823) sourceC1823) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1823 sourceB1823 sourceC1823 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1823 sourceB1823 sourceC1823
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1823, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1824 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 0) (sourceB1824 + difference 0 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 597) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 0) (sourceB1824 + difference 0 1) sourceC1824) = raw26375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26375; decide +kernel
    rw [ha]
    exact (canonical26375 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 1) (sourceB1824 + difference 1 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 1) (sourceB1824 + difference 1 1) sourceC1824) = raw25426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw25426; decide +kernel
    rw [ha]
    exact (canonical25426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 2) (sourceB1824 + difference 2 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 2) (sourceB1824 + difference 2 1) sourceC1824) = raw25420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw25420; decide +kernel
    rw [ha]
    exact (canonical25420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 3) (sourceB1824 + difference 3 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 3) (sourceB1824 + difference 3 1) sourceC1824) = raw26376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26376; decide +kernel
    rw [ha]
    exact (canonical26376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 4) (sourceB1824 + difference 4 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 4) (sourceB1824 + difference 4 1) sourceC1824) = raw26377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26377; decide +kernel
    rw [ha]
    exact (canonical26377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 5) (sourceB1824 + difference 5 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 5) (sourceB1824 + difference 5 1) sourceC1824) = raw26378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26378; decide +kernel
    rw [ha]
    exact (canonical26378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1824 + sourceB1824) sourceC1824) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1824 + sourceB1824) sourceC1824) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1824 sourceB1824 sourceC1824 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1824 sourceB1824 sourceC1824
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1824, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1825 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 0) (sourceB1825 + difference 0 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 0) (sourceB1825 + difference 0 0) sourceC1825) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 1) (sourceB1825 + difference 1 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 1) (sourceB1825 + difference 1 0) sourceC1825) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 2) (sourceB1825 + difference 2 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 2) (sourceB1825 + difference 2 0) sourceC1825) = raw26379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26379; decide +kernel
    rw [ha]
    exact (canonical26379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 3) (sourceB1825 + difference 3 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 3) (sourceB1825 + difference 3 0) sourceC1825) = raw26380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26380; decide +kernel
    rw [ha]
    exact (canonical26380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 4) (sourceB1825 + difference 4 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 4) (sourceB1825 + difference 4 0) sourceC1825) = raw26381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26381; decide +kernel
    rw [ha]
    exact (canonical26381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 5) (sourceB1825 + difference 5 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 5) (sourceB1825 + difference 5 0) sourceC1825) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1825 + sourceB1825) sourceC1825) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1825 + sourceB1825) sourceC1825) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1825 sourceB1825 sourceC1825 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1825 sourceB1825 sourceC1825
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1825, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1826 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1826 + difference 0 5) (sourceB1826 + difference 5 0) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1826 + difference 0 5) (sourceB1826 + difference 5 0) sourceC1826) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1826 + difference 1 5) (sourceB1826 + difference 5 1) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1826 + difference 1 5) (sourceB1826 + difference 5 1) sourceC1826) = raw26383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26383; decide +kernel
    rw [ha]
    exact (canonical26383 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1826 + difference 2 5) (sourceB1826 + difference 5 2) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 2 5) (sourceB1826 + difference 5 2) sourceC1826) = raw26384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26384; decide +kernel
    rw [ha]
    exact (canonical26384 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1826 + difference 3 5) (sourceB1826 + difference 5 3) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 3 5) (sourceB1826 + difference 5 3) sourceC1826) = raw26385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26385; decide +kernel
    rw [ha]
    exact (canonical26385 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1826 + difference 4 5) (sourceB1826 + difference 5 4) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 4 5) (sourceB1826 + difference 5 4) sourceC1826) = raw26386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26386; decide +kernel
    rw [ha]
    exact (canonical26386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1826 + difference 5 5) (sourceB1826 + difference 5 5) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1826 + difference 5 5) (sourceB1826 + difference 5 5) sourceC1826) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1826 + sourceB1826) sourceC1826) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1826 + sourceB1826) sourceC1826) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1826 sourceB1826 sourceC1826 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1826 sourceB1826 sourceC1826
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1826, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1827 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1827 + difference 0 1) (sourceB1827 + difference 1 0) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA1827 + difference 0 1) (sourceB1827 + difference 1 0) sourceC1827) = raw26387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26387; decide +kernel
    rw [ha]
    exact (canonical26387 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1827 + difference 1 1) (sourceB1827 + difference 1 1) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA1827 + difference 1 1) (sourceB1827 + difference 1 1) sourceC1827) = raw26388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26388; decide +kernel
    rw [ha]
    exact (canonical26388 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1827 + difference 2 1) (sourceB1827 + difference 1 2) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 2 1) (sourceB1827 + difference 1 2) sourceC1827) = raw26389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26389; decide +kernel
    rw [ha]
    exact (canonical26389 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1827 + difference 3 1) (sourceB1827 + difference 1 3) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 3 1) (sourceB1827 + difference 1 3) sourceC1827) = raw26390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26390; decide +kernel
    rw [ha]
    exact (canonical26390 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1827 + difference 4 1) (sourceB1827 + difference 1 4) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 4 1) (sourceB1827 + difference 1 4) sourceC1827) = raw26391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26391; decide +kernel
    rw [ha]
    exact (canonical26391 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1827 + difference 5 1) (sourceB1827 + difference 1 5) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1319) := by
    have ha : (tripleCharges (sourceA1827 + difference 5 1) (sourceB1827 + difference 1 5) sourceC1827) = raw26392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26392; decide +kernel
    rw [ha]
    exact (canonical26392 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1827 + sourceB1827) sourceC1827) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1827 + sourceB1827) sourceC1827) = raw26393 := by
      apply Matrix.ext; unfold doubleCharges sourceA1827 sourceB1827 sourceC1827 raw26393; decide +kernel
    rw [ha]
    exact (canonical26393 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1827 sourceB1827 sourceC1827
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1827, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1828 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 0) (sourceB1828 + difference 0 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 0) (sourceB1828 + difference 0 0) sourceC1828) = raw26383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26383; decide +kernel
    rw [ha]
    exact (canonical26383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 1) (sourceB1828 + difference 1 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 1) (sourceB1828 + difference 1 0) sourceC1828) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 2) (sourceB1828 + difference 2 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 2) (sourceB1828 + difference 2 0) sourceC1828) = raw26394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26394; decide +kernel
    rw [ha]
    exact (canonical26394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 3) (sourceB1828 + difference 3 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 3) (sourceB1828 + difference 3 0) sourceC1828) = raw26395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26395; decide +kernel
    rw [ha]
    exact (canonical26395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 4) (sourceB1828 + difference 4 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 4) (sourceB1828 + difference 4 0) sourceC1828) = raw26396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26396; decide +kernel
    rw [ha]
    exact (canonical26396 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 5) (sourceB1828 + difference 5 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3244) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 5) (sourceB1828 + difference 5 0) sourceC1828) = raw26397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26397; decide +kernel
    rw [ha]
    exact (canonical26397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1828 + sourceB1828) sourceC1828) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1828 + sourceB1828) sourceC1828) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1828 sourceB1828 sourceC1828 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1828 sourceB1828 sourceC1828
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1828, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1831 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 0) (sourceB1831 + difference 0 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 0) (sourceB1831 + difference 0 0) sourceC1831) = raw26409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26409; decide +kernel
    rw [ha]
    exact (canonical26409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 1) (sourceB1831 + difference 1 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2628) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 1) (sourceB1831 + difference 1 0) sourceC1831) = raw26410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26410; decide +kernel
    rw [ha]
    exact (canonical26410 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 2) (sourceB1831 + difference 2 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 2) (sourceB1831 + difference 2 0) sourceC1831) = raw26411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26411; decide +kernel
    rw [ha]
    exact (canonical26411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 3) (sourceB1831 + difference 3 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 3) (sourceB1831 + difference 3 0) sourceC1831) = raw26412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26412; decide +kernel
    rw [ha]
    exact (canonical26412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 4) (sourceB1831 + difference 4 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 4) (sourceB1831 + difference 4 0) sourceC1831) = raw26413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26413; decide +kernel
    rw [ha]
    exact (canonical26413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 5) (sourceB1831 + difference 5 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 5) (sourceB1831 + difference 5 0) sourceC1831) = raw26414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26414; decide +kernel
    rw [ha]
    exact (canonical26414 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1831 + sourceB1831) sourceC1831) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1831 + sourceB1831) sourceC1831) = raw26415 := by
      apply Matrix.ext; unfold doubleCharges sourceA1831 sourceB1831 sourceC1831 raw26415; decide +kernel
    rw [ha]
    exact (canonical26415 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1831 sourceB1831 sourceC1831
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1831, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1832 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1832 + difference 0 5) (sourceB1832 + difference 5 0) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1832 + difference 0 5) (sourceB1832 + difference 5 0) sourceC1832) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1832 + difference 1 5) (sourceB1832 + difference 5 1) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1832 + difference 1 5) (sourceB1832 + difference 5 1) sourceC1832) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1832 + difference 2 5) (sourceB1832 + difference 5 2) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 2 5) (sourceB1832 + difference 5 2) sourceC1832) = raw26417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26417; decide +kernel
    rw [ha]
    exact (canonical26417 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1832 + difference 3 5) (sourceB1832 + difference 5 3) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 3 5) (sourceB1832 + difference 5 3) sourceC1832) = raw26418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26418; decide +kernel
    rw [ha]
    exact (canonical26418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1832 + difference 4 5) (sourceB1832 + difference 5 4) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 4 5) (sourceB1832 + difference 5 4) sourceC1832) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1832 + difference 5 5) (sourceB1832 + difference 5 5) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3057) := by
    have ha : (tripleCharges (sourceA1832 + difference 5 5) (sourceB1832 + difference 5 5) sourceC1832) = raw26365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26365; decide +kernel
    rw [ha]
    exact (canonical26365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1832 + sourceB1832) sourceC1832) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1832 + sourceB1832) sourceC1832) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1832 sourceB1832 sourceC1832 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1832 sourceB1832 sourceC1832
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1832, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1833 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1833 + difference 0 1) (sourceB1833 + difference 1 0) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA1833 + difference 0 1) (sourceB1833 + difference 1 0) sourceC1833) = raw26420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26420; decide +kernel
    rw [ha]
    exact (canonical26420 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1833 + difference 1 1) (sourceB1833 + difference 1 1) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1833 + difference 1 1) (sourceB1833 + difference 1 1) sourceC1833) = raw26421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26421; decide +kernel
    rw [ha]
    exact (canonical26421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1833 + difference 2 1) (sourceB1833 + difference 1 2) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1833 + difference 2 1) (sourceB1833 + difference 1 2) sourceC1833) = raw26422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26422; decide +kernel
    rw [ha]
    exact (canonical26422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1833 + difference 3 1) (sourceB1833 + difference 1 3) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1833 + difference 3 1) (sourceB1833 + difference 1 3) sourceC1833) = raw26423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26423; decide +kernel
    rw [ha]
    exact (canonical26423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1833 + difference 4 1) (sourceB1833 + difference 1 4) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1833 + difference 4 1) (sourceB1833 + difference 1 4) sourceC1833) = raw26424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26424; decide +kernel
    rw [ha]
    exact (canonical26424 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1833 + difference 5 1) (sourceB1833 + difference 1 5) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1833 + difference 5 1) (sourceB1833 + difference 1 5) sourceC1833) = raw26425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26425; decide +kernel
    rw [ha]
    exact (canonical26425 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1833 + sourceB1833) sourceC1833) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1833 + sourceB1833) sourceC1833) = raw19472 := by
      apply Matrix.ext; unfold doubleCharges sourceA1833 sourceB1833 sourceC1833 raw19472; decide +kernel
    rw [ha]
    exact (canonical19472 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1833 sourceB1833 sourceC1833
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1833, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1834 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 0) (sourceB1834 + difference 0 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 0) (sourceB1834 + difference 0 1) sourceC1834) = raw26426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26426; decide +kernel
    rw [ha]
    exact (canonical26426 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 1) (sourceB1834 + difference 1 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 1) (sourceB1834 + difference 1 1) sourceC1834) = raw26427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26427; decide +kernel
    rw [ha]
    exact (canonical26427 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 2) (sourceB1834 + difference 2 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 2) (sourceB1834 + difference 2 1) sourceC1834) = raw26428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26428; decide +kernel
    rw [ha]
    exact (canonical26428 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 3) (sourceB1834 + difference 3 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 3) (sourceB1834 + difference 3 1) sourceC1834) = raw26429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26429; decide +kernel
    rw [ha]
    exact (canonical26429 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 4) (sourceB1834 + difference 4 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 4) (sourceB1834 + difference 4 1) sourceC1834) = raw26430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26430; decide +kernel
    rw [ha]
    exact (canonical26430 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 5) (sourceB1834 + difference 5 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 5) (sourceB1834 + difference 5 1) sourceC1834) = raw26431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26431; decide +kernel
    rw [ha]
    exact (canonical26431 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1834 + sourceB1834) sourceC1834) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1834 + sourceB1834) sourceC1834) = raw26432 := by
      apply Matrix.ext; unfold doubleCharges sourceA1834 sourceB1834 sourceC1834 raw26432; decide +kernel
    rw [ha]
    exact (canonical26432 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1834 sourceB1834 sourceC1834
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1834, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1537 : Integer.Sparse.reindex keyMap MixedData.row1537 = numericRow1537 := by decide +kernel

theorem numericCheck1537 (x : Master → ℝ) : Integer.Sparse.eval numericRow1537 x =
    (1 : ℝ) * reducedSource1537 x := by
  norm_num [numericRow1537, reducedSource1537, Integer.Sparse.eval, Sparse.eval, nodeValue662, nodeValue681, nodeValue682, nodeValue687, nodeValue760, nodeValue761, nodeValue766, nodeValue798, nodeValue803, nodeValue805, nodeValue840, nodeValue841, nodeValue847, nodeValue848, nodeValue850, nodeValue998, nodeValue1073, nodeValue1079, nodeValue1081, nodeValue4068]

theorem reindexCheck1538 : Integer.Sparse.reindex keyMap MixedData.row1538 = numericRow1538 := by decide +kernel

theorem numericCheck1538 (x : Master → ℝ) : Integer.Sparse.eval numericRow1538 x =
    (1 : ℝ) * reducedSource1538 x := by
  norm_num [numericRow1538, reducedSource1538, Integer.Sparse.eval, Sparse.eval, nodeValue732, nodeValue737, nodeValue739, nodeValue810, nodeValue1648, nodeValue4068]

theorem reindexCheck1540 : Integer.Sparse.reindex keyMap MixedData.row1540 = numericRow1540 := by decide +kernel

theorem numericCheck1540 (x : Master → ℝ) : Integer.Sparse.eval numericRow1540 x =
    (1 : ℝ) * reducedSource1540 x := by
  norm_num [numericRow1540, reducedSource1540, Integer.Sparse.eval, Sparse.eval, nodeValue4057, nodeValue4058, nodeValue4059, nodeValue4063, nodeValue4064, nodeValue4065, nodeValue4068, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4080, nodeValue4083, nodeValue4084]

theorem reindexCheck1541 : Integer.Sparse.reindex keyMap MixedData.row1541 = numericRow1541 := by decide +kernel

theorem numericCheck1541 (x : Master → ℝ) : Integer.Sparse.eval numericRow1541 x =
    (1 : ℝ) * reducedSource1541 x := by
  norm_num [numericRow1541, reducedSource1541, Integer.Sparse.eval, Sparse.eval, nodeValue1700, nodeValue3057, nodeValue3072, nodeValue3304, nodeValue4068]

theorem reindexCheck1542 : Integer.Sparse.reindex keyMap MixedData.row1542 = numericRow1542 := by decide +kernel

theorem numericCheck1542 (x : Master → ℝ) : Integer.Sparse.eval numericRow1542 x =
    (1 : ℝ) * reducedSource1542 x := by
  norm_num [numericRow1542, reducedSource1542, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue1700, nodeValue1708, nodeValue3304, nodeValue4068]

theorem reindexCheck1543 : Integer.Sparse.reindex keyMap MixedData.row1543 = numericRow1543 := by decide +kernel

theorem numericCheck1543 (x : Master → ℝ) : Integer.Sparse.eval numericRow1543 x =
    (1 : ℝ) * reducedSource1543 x := by
  norm_num [numericRow1543, reducedSource1543, Integer.Sparse.eval, Sparse.eval, nodeValue597, nodeValue1038, nodeValue1056, nodeValue1079, nodeValue4084]

theorem reindexCheck1544 : Integer.Sparse.reindex keyMap MixedData.row1544 = numericRow1544 := by decide +kernel

theorem numericCheck1544 (x : Master → ℝ) : Integer.Sparse.eval numericRow1544 x =
    (1 : ℝ) * reducedSource1544 x := by
  norm_num [numericRow1544, reducedSource1544, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue3286, nodeValue3292, nodeValue3304, nodeValue4068]

theorem reindexCheck1545 : Integer.Sparse.reindex keyMap MixedData.row1545 = numericRow1545 := by decide +kernel

theorem numericCheck1545 (x : Master → ℝ) : Integer.Sparse.eval numericRow1545 x =
    (1 : ℝ) * reducedSource1545 x := by
  norm_num [numericRow1545, reducedSource1545, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue1699, nodeValue1706, nodeValue3292, nodeValue4068]

theorem reindexCheck1546 : Integer.Sparse.reindex keyMap MixedData.row1546 = numericRow1546 := by decide +kernel

theorem numericCheck1546 (x : Master → ℝ) : Integer.Sparse.eval numericRow1546 x =
    (1 : ℝ) * reducedSource1546 x := by
  norm_num [numericRow1546, reducedSource1546, Integer.Sparse.eval, Sparse.eval, nodeValue1316, nodeValue1319, nodeValue1366, nodeValue2880, nodeValue4091]

theorem reindexCheck1547 : Integer.Sparse.reindex keyMap MixedData.row1547 = numericRow1547 := by decide +kernel

theorem numericCheck1547 (x : Master → ℝ) : Integer.Sparse.eval numericRow1547 x =
    (1 : ℝ) * reducedSource1547 x := by
  norm_num [numericRow1547, reducedSource1547, Integer.Sparse.eval, Sparse.eval, nodeValue1699, nodeValue3239, nodeValue3244, nodeValue3292, nodeValue4068]

theorem reindexCheck1548 : Integer.Sparse.reindex keyMap MixedData.row1548 = numericRow1548 := by decide +kernel

theorem numericCheck1548 (x : Master → ℝ) : Integer.Sparse.eval numericRow1548 x =
    (1 : ℝ) * reducedSource1548 x := by
  norm_num [numericRow1548, reducedSource1548, Integer.Sparse.eval, Sparse.eval, nodeValue1256, nodeValue2628, nodeValue2671, nodeValue2747, nodeValue4087]

theorem reindexCheck1549 : Integer.Sparse.reindex keyMap MixedData.row1549 = numericRow1549 := by decide +kernel

theorem numericCheck1549 (x : Master → ℝ) : Integer.Sparse.eval numericRow1549 x =
    (1 : ℝ) * reducedSource1549 x := by
  norm_num [numericRow1549, reducedSource1549, Integer.Sparse.eval, Sparse.eval, nodeValue1644, nodeValue3057, nodeValue3289, nodeValue3304, nodeValue4068]

theorem reindexCheck1550 : Integer.Sparse.reindex keyMap MixedData.row1550 = numericRow1550 := by decide +kernel

theorem numericCheck1550 (x : Master → ℝ) : Integer.Sparse.eval numericRow1550 x =
    (1 : ℝ) * reducedSource1550 x := by
  norm_num [numericRow1550, reducedSource1550, Integer.Sparse.eval, Sparse.eval, nodeValue1126, nodeValue1127, nodeValue1130, nodeValue1233, nodeValue2508, nodeValue4092]

theorem reindexCheck1551 : Integer.Sparse.reindex keyMap MixedData.row1551 = numericRow1551 := by decide +kernel

theorem numericCheck1551 (x : Master → ℝ) : Integer.Sparse.eval numericRow1551 x =
    (1 : ℝ) * reducedSource1551 x := by
  norm_num [numericRow1551, reducedSource1551, Integer.Sparse.eval, Sparse.eval, nodeValue637, nodeValue1235, nodeValue1260, nodeValue1293, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1537 (mixedVector B) = 0 := by
  have h662 : mixedVector B (Sum.inr 662) = Sparse.eval nodeValue662 (mixedVector B) := by
    change mixedMoment B node662 node662Labels = _
    exact sound662 B hB hF
  have h681 : mixedVector B (Sum.inr 681) = Sparse.eval nodeValue681 (mixedVector B) := by
    change mixedMoment B node681 node681Labels = _
    exact sound681 B hB hF
  have h682 : mixedVector B (Sum.inr 682) = Sparse.eval nodeValue682 (mixedVector B) := by
    change mixedMoment B node682 node682Labels = _
    exact sound682 B hB hF
  have h687 : mixedVector B (Sum.inr 687) = Sparse.eval nodeValue687 (mixedVector B) := by
    change mixedMoment B node687 node687Labels = _
    exact sound687 B hB hF
  have h760 : mixedVector B (Sum.inr 760) = Sparse.eval nodeValue760 (mixedVector B) := by
    change mixedMoment B node760 node760Labels = _
    exact sound760 B hB hF
  have h761 : mixedVector B (Sum.inr 761) = Sparse.eval nodeValue761 (mixedVector B) := by
    change mixedMoment B node761 node761Labels = _
    exact sound761 B hB hF
  have h766 : mixedVector B (Sum.inr 766) = Sparse.eval nodeValue766 (mixedVector B) := by
    change mixedMoment B node766 node766Labels = _
    exact sound766 B hB hF
  have h798 : mixedVector B (Sum.inr 798) = Sparse.eval nodeValue798 (mixedVector B) := by
    change mixedMoment B node798 node798Labels = _
    exact sound798 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h840 : mixedVector B (Sum.inr 840) = Sparse.eval nodeValue840 (mixedVector B) := by
    change mixedMoment B node840 node840Labels = _
    exact sound840 B hB hF
  have h841 : mixedVector B (Sum.inr 841) = Sparse.eval nodeValue841 (mixedVector B) := by
    change mixedMoment B node841 node841Labels = _
    exact sound841 B hB hF
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h850 : mixedVector B (Sum.inr 850) = Sparse.eval nodeValue850 (mixedVector B) := by
    change mixedMoment B node850 node850Labels = _
    exact sound850 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1816, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h662, h681, h682, h687, h760, h761, h766, h798, h803, h805, h840, h841, h847, h848, h850, h998, h1073, h1079, h1081, h4068, reducedSource1537] using sourceEq1816 B hB

theorem rowSound1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1537 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1537, numericCheck1537, reducedZero1537 B hB hF, mul_zero]

theorem reducedZero1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1538 (mixedVector B) = 0 := by
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h737 : mixedVector B (Sum.inr 737) = Sparse.eval nodeValue737 (mixedVector B) := by
    change mixedMoment B node737 node737Labels = _
    exact sound737 B hB hF
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1817, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h732, h737, h739, h810, h1648, h4068, reducedSource1538] using sourceEq1817 B hB

theorem rowSound1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1538 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1538, numericCheck1538, reducedZero1538 B hB hF, mul_zero]

theorem reducedZero1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1540 (mixedVector B) = 0 := by
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1821, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4057, h4058, h4059, h4063, h4064, h4065, h4068, h4069, h4070, h4071, h4080, h4083, h4084, reducedSource1540] using sourceEq1821 B hB

theorem rowSound1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1540 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1540, numericCheck1540, reducedZero1540 B hB hF, mul_zero]

theorem reducedZero1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1541 (mixedVector B) = 0 := by
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h3057 : mixedVector B (Sum.inr 3057) = Sparse.eval nodeValue3057 (mixedVector B) := by
    change mixedMoment B node3057 node3057Labels = _
    exact sound3057 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1822, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1700, h3057, h3072, h3304, h4068, reducedSource1541] using sourceEq1822 B hB

theorem rowSound1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1541 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1541, numericCheck1541, reducedZero1541 B hB hF, mul_zero]

theorem reducedZero1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1542 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1823, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h1700, h1708, h3304, h4068, reducedSource1542] using sourceEq1823 B hB

theorem rowSound1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1542 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1542, numericCheck1542, reducedZero1542 B hB hF, mul_zero]

theorem reducedZero1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1543 (mixedVector B) = 0 := by
  have h597 : mixedVector B (Sum.inr 597) = Sparse.eval nodeValue597 (mixedVector B) := by
    change mixedMoment B node597 node597Labels = _
    exact sound597 B hB hF
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1824, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h597, h1038, h1056, h1079, h4084, reducedSource1543] using sourceEq1824 B hB

theorem rowSound1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1543 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1543, numericCheck1543, reducedZero1543 B hB hF, mul_zero]

theorem reducedZero1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1544 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1825, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h3286, h3292, h3304, h4068, reducedSource1544] using sourceEq1825 B hB

theorem rowSound1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1544 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1544, numericCheck1544, reducedZero1544 B hB hF, mul_zero]

theorem reducedZero1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1545 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1826, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h1699, h1706, h3292, h4068, reducedSource1545] using sourceEq1826 B hB

theorem rowSound1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1545 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1545, numericCheck1545, reducedZero1545 B hB hF, mul_zero]

theorem reducedZero1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1546 (mixedVector B) = 0 := by
  have h1316 : mixedVector B (Sum.inr 1316) = Sparse.eval nodeValue1316 (mixedVector B) := by
    change mixedMoment B node1316 node1316Labels = _
    exact sound1316 B hB hF
  have h1319 : mixedVector B (Sum.inr 1319) = Sparse.eval nodeValue1319 (mixedVector B) := by
    change mixedMoment B node1319 node1319Labels = _
    exact sound1319 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1827, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1316, h1319, h1366, h2880, h4091, reducedSource1546] using sourceEq1827 B hB

theorem rowSound1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1546 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1546, numericCheck1546, reducedZero1546 B hB hF, mul_zero]

theorem reducedZero1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1547 (mixedVector B) = 0 := by
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3244 : mixedVector B (Sum.inr 3244) = Sparse.eval nodeValue3244 (mixedVector B) := by
    change mixedMoment B node3244 node3244Labels = _
    exact sound3244 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1828, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1699, h3239, h3244, h3292, h4068, reducedSource1547] using sourceEq1828 B hB

theorem rowSound1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1547 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1547, numericCheck1547, reducedZero1547 B hB hF, mul_zero]

theorem reducedZero1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1548 (mixedVector B) = 0 := by
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h2628 : mixedVector B (Sum.inr 2628) = Sparse.eval nodeValue2628 (mixedVector B) := by
    change mixedMoment B node2628 node2628Labels = _
    exact sound2628 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1831, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1256, h2628, h2671, h2747, h4087, reducedSource1548] using sourceEq1831 B hB

theorem rowSound1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1548 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1548, numericCheck1548, reducedZero1548 B hB hF, mul_zero]

theorem reducedZero1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1549 (mixedVector B) = 0 := by
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h3057 : mixedVector B (Sum.inr 3057) = Sparse.eval nodeValue3057 (mixedVector B) := by
    change mixedMoment B node3057 node3057Labels = _
    exact sound3057 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1832, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1644, h3057, h3289, h3304, h4068, reducedSource1549] using sourceEq1832 B hB

theorem rowSound1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1549 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1549, numericCheck1549, reducedZero1549 B hB hF, mul_zero]

theorem reducedZero1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1550 (mixedVector B) = 0 := by
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1833, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1126, h1127, h1130, h1233, h2508, h4092, reducedSource1550] using sourceEq1833 B hB

theorem rowSound1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1550 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1550, numericCheck1550, reducedZero1550 B hB hF, mul_zero]

theorem reducedZero1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1551 (mixedVector B) = 0 := by
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1834, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h637, h1235, h1260, h1293, h4091, reducedSource1551] using sourceEq1834 B hB

theorem rowSound1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1551 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1551, numericCheck1551, reducedZero1551 B hB hF, mul_zero]

theorem sourceRowsAt1536 : MixedData.sourceRows (1536 : Fin 2425) =
    MixedData.row1536 := by decide +kernel

theorem sourceRowsAt1537 : MixedData.sourceRows (1537 : Fin 2425) =
    MixedData.row1537 := by decide +kernel

theorem sourceRowsAt1538 : MixedData.sourceRows (1538 : Fin 2425) =
    MixedData.row1538 := by decide +kernel

theorem sourceRowsAt1539 : MixedData.sourceRows (1539 : Fin 2425) =
    MixedData.row1539 := by decide +kernel

theorem sourceRowsAt1540 : MixedData.sourceRows (1540 : Fin 2425) =
    MixedData.row1540 := by decide +kernel

theorem sourceRowsAt1541 : MixedData.sourceRows (1541 : Fin 2425) =
    MixedData.row1541 := by decide +kernel

theorem sourceRowsAt1542 : MixedData.sourceRows (1542 : Fin 2425) =
    MixedData.row1542 := by decide +kernel

theorem sourceRowsAt1543 : MixedData.sourceRows (1543 : Fin 2425) =
    MixedData.row1543 := by decide +kernel

theorem sourceRowsAt1544 : MixedData.sourceRows (1544 : Fin 2425) =
    MixedData.row1544 := by decide +kernel

theorem sourceRowsAt1545 : MixedData.sourceRows (1545 : Fin 2425) =
    MixedData.row1545 := by decide +kernel

theorem sourceRowsAt1546 : MixedData.sourceRows (1546 : Fin 2425) =
    MixedData.row1546 := by decide +kernel

theorem sourceRowsAt1547 : MixedData.sourceRows (1547 : Fin 2425) =
    MixedData.row1547 := by decide +kernel

theorem sourceRowsAt1548 : MixedData.sourceRows (1548 : Fin 2425) =
    MixedData.row1548 := by decide +kernel

theorem sourceRowsAt1549 : MixedData.sourceRows (1549 : Fin 2425) =
    MixedData.row1549 := by decide +kernel

theorem sourceRowsAt1550 : MixedData.sourceRows (1550 : Fin 2425) =
    MixedData.row1550 := by decide +kernel

theorem sourceRowsAt1551 : MixedData.sourceRows (1551 : Fin 2425) =
    MixedData.row1551 := by decide +kernel

theorem chunkSound96_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 96) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1536 ∨ k.val = 1537 ∨ k.val = 1538 ∨ k.val = 1539 ∨ k.val = 1540 ∨ k.val = 1541 ∨ k.val = 1542 ∨ k.val = 1543 ∨ k.val = 1544 ∨ k.val = 1545 ∨ k.val = 1546 ∨ k.val = 1547 ∨ k.val = 1548 ∨ k.val = 1549 ∨ k.val = 1550 ∨ k.val = 1551 := by omega
  rcases heq with h1536 | h1537 | h1538 | h1539 | h1540 | h1541 | h1542 | h1543 | h1544 | h1545 | h1546 | h1547 | h1548 | h1549 | h1550 | h1551
  · have he : k = (1536 : Fin 2425) := Fin.ext h1536
    subst k
    rw [sourceRowsAt1536]
    exact rowSound1536_e B hB hF
  · have he : k = (1537 : Fin 2425) := Fin.ext h1537
    subst k
    rw [sourceRowsAt1537]
    exact rowSound1537 B hB hF
  · have he : k = (1538 : Fin 2425) := Fin.ext h1538
    subst k
    rw [sourceRowsAt1538]
    exact rowSound1538 B hB hF
  · have he : k = (1539 : Fin 2425) := Fin.ext h1539
    subst k
    rw [sourceRowsAt1539]
    exact rowSound1539_e B hB hF
  · have he : k = (1540 : Fin 2425) := Fin.ext h1540
    subst k
    rw [sourceRowsAt1540]
    exact rowSound1540 B hB hF
  · have he : k = (1541 : Fin 2425) := Fin.ext h1541
    subst k
    rw [sourceRowsAt1541]
    exact rowSound1541 B hB hF
  · have he : k = (1542 : Fin 2425) := Fin.ext h1542
    subst k
    rw [sourceRowsAt1542]
    exact rowSound1542 B hB hF
  · have he : k = (1543 : Fin 2425) := Fin.ext h1543
    subst k
    rw [sourceRowsAt1543]
    exact rowSound1543 B hB hF
  · have he : k = (1544 : Fin 2425) := Fin.ext h1544
    subst k
    rw [sourceRowsAt1544]
    exact rowSound1544 B hB hF
  · have he : k = (1545 : Fin 2425) := Fin.ext h1545
    subst k
    rw [sourceRowsAt1545]
    exact rowSound1545 B hB hF
  · have he : k = (1546 : Fin 2425) := Fin.ext h1546
    subst k
    rw [sourceRowsAt1546]
    exact rowSound1546 B hB hF
  · have he : k = (1547 : Fin 2425) := Fin.ext h1547
    subst k
    rw [sourceRowsAt1547]
    exact rowSound1547 B hB hF
  · have he : k = (1548 : Fin 2425) := Fin.ext h1548
    subst k
    rw [sourceRowsAt1548]
    exact rowSound1548 B hB hF
  · have he : k = (1549 : Fin 2425) := Fin.ext h1549
    subst k
    rw [sourceRowsAt1549]
    exact rowSound1549 B hB hF
  · have he : k = (1550 : Fin 2425) := Fin.ext h1550
    subst k
    rw [sourceRowsAt1550]
    exact rowSound1550 B hB hF
  · have he : k = (1551 : Fin 2425) := Fin.ext h1551
    subst k
    rw [sourceRowsAt1551]
    exact rowSound1551 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e_oai
