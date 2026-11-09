-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:56:46.008566+00:00
-- url     : https://prove2.me/submissions/88444cf0-2b9f-433c-92fd-402ec0c9117a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1715_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1716_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1717_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1723_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20738 raw20738Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20738 raw20738Labels = mixedMoment B raw20738step0 raw20738step0Labels := by
      have hz : ∀ j, raw20738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20738step0 = (fun i j => raw20738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20738step0 raw20738; decide +kernel
      have hl : raw20738step0Labels = raw20738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738 raw20738Labels permutation346 hz
    mixedMoment B raw20738step0 raw20738step0Labels = mixedMoment B raw20738step1 raw20738step1Labels := by
      have hz : ∀ j, raw20738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20738step1 = (fun i j => raw20738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20738step1 raw20738step0; decide +kernel
      have hl : raw20738step1Labels = raw20738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738step0 raw20738step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical20739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20739 raw20739Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw20739 raw20739Labels = mixedMoment B raw20739step0 raw20739step0Labels := by
      have hz : ∀ j, raw20739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20739step0 = (fun i j => raw20739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20739step0 raw20739; decide +kernel
      have hl : raw20739step0Labels = raw20739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20739 raw20739Labels permutation346 hz
    mixedMoment B raw20739step0 raw20739step0Labels = mixedMoment B raw20739step1 raw20739step1Labels := by
      have ha : raw20739step1 = (fun i j => raw20739step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20739step1 raw20739step0; decide +kernel
      have hl : raw20739step1Labels = raw20739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20739step0 raw20739step0Labels permutation151 permutation2
    mixedMoment B raw20739step1 raw20739step1Labels = mixedMoment B raw20739step2 raw20739step2Labels := by
      have ha : raw20739step2 = -raw20739step1 := by apply Matrix.ext; change ∀ i j, raw20739step2 i j = -(raw20739step1 i j); unfold raw20739step2 raw20739step1; decide +kernel
      have hl : raw20739step2Labels = raw20739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical20744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20744 raw20744Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw20744 raw20744Labels = mixedMoment B raw20744step0 raw20744step0Labels := by
      have hz : ∀ j, raw20744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20744step0 = (fun i j => raw20744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20744step0 raw20744; decide +kernel
      have hl : raw20744step0Labels = raw20744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744 raw20744Labels permutation346 hz
    mixedMoment B raw20744step0 raw20744step0Labels = mixedMoment B raw20744step1 raw20744step1Labels := by
      have hz : ∀ j, raw20744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20744step1 = (fun i j => raw20744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20744step1 raw20744step0; decide +kernel
      have hl : raw20744step1Labels = raw20744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744step0 raw20744step0Labels permutation56 hz
    _ = mixedMoment B node2517 node2517Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20888 raw20888Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw20888 raw20888Labels = mixedMoment B raw20888step0 raw20888step0Labels := by
      have hz : ∀ j, raw20888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20888step0 = (fun i j => raw20888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20888step0 raw20888; decide +kernel
      have hl : raw20888step0Labels = raw20888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888 raw20888Labels permutation346 hz
    mixedMoment B raw20888step0 raw20888step0Labels = mixedMoment B raw20888step1 raw20888step1Labels := by
      have hz : ∀ j, raw20888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20888step1 = (fun i j => raw20888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20888step1 raw20888step0; decide +kernel
      have hl : raw20888step1Labels = raw20888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888step0 raw20888step0Labels permutation56 hz
    mixedMoment B raw20888step1 raw20888step1Labels = mixedMoment B raw20888step2 raw20888step2Labels := by
      have ha : raw20888step2 = (fun i j => raw20888step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20888step2 raw20888step1; decide +kernel
      have hl : raw20888step2Labels = raw20888step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20888step1 raw20888step1Labels permutation31 permutation7
    mixedMoment B raw20888step2 raw20888step2Labels = mixedMoment B raw20888step3 raw20888step3Labels := by
      have ha : raw20888step3 = raw20888step2 := by apply Matrix.ext; unfold raw20888step3 raw20888step2; decide +kernel
      have hl : raw20888step2Labels = labelEmbedding1 ∘ raw20888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20888step2 raw20888step2Labels raw20888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical20894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20894 raw20894Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw20894 raw20894Labels = mixedMoment B raw20894step0 raw20894step0Labels := by
      have ha : raw20894step0 = (fun i j => raw20894 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20894step0 raw20894; decide +kernel
      have hl : raw20894step0Labels = raw20894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20894 raw20894Labels permutation644 permutation7
    mixedMoment B raw20894step0 raw20894step0Labels = mixedMoment B raw20894step1 raw20894step1Labels := by
      have ha : raw20894step1 = raw20894step0 := by apply Matrix.ext; unfold raw20894step1 raw20894step0; decide +kernel
      have hl : raw20894step0Labels = labelEmbedding1 ∘ raw20894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20894step0 raw20894step0Labels raw20894step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

theorem canonical20898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20898 raw20898Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20898 raw20898Labels = mixedMoment B raw20898step0 raw20898step0Labels := by
      have hz : ∀ j, raw20898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20898step0 = (fun i j => raw20898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20898step0 raw20898; decide +kernel
      have hl : raw20898step0Labels = raw20898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20898 raw20898Labels permutation346 hz
    mixedMoment B raw20898step0 raw20898step0Labels = mixedMoment B raw20898step1 raw20898step1Labels := by
      have ha : raw20898step1 = (fun i j => raw20898step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20898step1 raw20898step0; decide +kernel
      have hl : raw20898step1Labels = raw20898step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20898step0 raw20898step0Labels permutation149 permutation7
    mixedMoment B raw20898step1 raw20898step1Labels = mixedMoment B raw20898step2 raw20898step2Labels := by
      have ha : raw20898step2 = raw20898step1 := by apply Matrix.ext; unfold raw20898step2 raw20898step1; decide +kernel
      have hl : raw20898step1Labels = labelEmbedding1 ∘ raw20898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20898step1 raw20898step1Labels raw20898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20902 raw20902Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw20902 raw20902Labels = mixedMoment B raw20902step0 raw20902step0Labels := by
      have hz : ∀ j, raw20902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20902step0 = (fun i j => raw20902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20902step0 raw20902; decide +kernel
      have hl : raw20902step0Labels = raw20902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20902 raw20902Labels permutation346 hz
    mixedMoment B raw20902step0 raw20902step0Labels = mixedMoment B raw20902step1 raw20902step1Labels := by
      have ha : raw20902step1 = (fun i j => raw20902step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20902step1 raw20902step0; decide +kernel
      have hl : raw20902step1Labels = raw20902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20902step0 raw20902step0Labels permutation149 permutation7
    mixedMoment B raw20902step1 raw20902step1Labels = mixedMoment B raw20902step2 raw20902step2Labels := by
      have ha : raw20902step2 = raw20902step1 := by apply Matrix.ext; unfold raw20902step2 raw20902step1; decide +kernel
      have hl : raw20902step1Labels = labelEmbedding1 ∘ raw20902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20902step1 raw20902step1Labels raw20902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical20906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20906 raw20906Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw20906 raw20906Labels = mixedMoment B raw20906step0 raw20906step0Labels := by
      have hz : ∀ j, raw20906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20906step0 = (fun i j => raw20906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20906step0 raw20906; decide +kernel
      have hl : raw20906step0Labels = raw20906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20906 raw20906Labels permutation346 hz
    mixedMoment B raw20906step0 raw20906step0Labels = mixedMoment B raw20906step1 raw20906step1Labels := by
      have ha : raw20906step1 = (fun i j => raw20906step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20906step1 raw20906step0; decide +kernel
      have hl : raw20906step1Labels = raw20906step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20906step0 raw20906step0Labels permutation149 permutation7
    mixedMoment B raw20906step1 raw20906step1Labels = mixedMoment B raw20906step2 raw20906step2Labels := by
      have ha : raw20906step2 = raw20906step1 := by apply Matrix.ext; unfold raw20906step2 raw20906step1; decide +kernel
      have hl : raw20906step1Labels = labelEmbedding1 ∘ raw20906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20906step1 raw20906step1Labels raw20906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical20916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20916 raw20916Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20916 raw20916Labels = mixedMoment B raw20916step0 raw20916step0Labels := by
      have hz : ∀ j, raw20916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20916step0 = (fun i j => raw20916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20916step0 raw20916; decide +kernel
      have hl : raw20916step0Labels = raw20916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916 raw20916Labels permutation520 hz
    mixedMoment B raw20916step0 raw20916step0Labels = mixedMoment B raw20916step1 raw20916step1Labels := by
      have hz : ∀ j, raw20916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20916step1 = (fun i j => raw20916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20916step1 raw20916step0; decide +kernel
      have hl : raw20916step1Labels = raw20916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step0 raw20916step0Labels permutation80 hz
    mixedMoment B raw20916step1 raw20916step1Labels = mixedMoment B raw20916step2 raw20916step2Labels := by
      have hz : ∀ j, raw20916step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20916step2 = (fun i j => raw20916step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20916step2 raw20916step1; decide +kernel
      have hl : raw20916step2Labels = raw20916step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step1 raw20916step1Labels permutation14 hz
    mixedMoment B raw20916step2 raw20916step2Labels = mixedMoment B raw20916step3 raw20916step3Labels := by
      have ha : raw20916step3 = (fun i j => raw20916step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20916step3 raw20916step2; decide +kernel
      have hl : raw20916step3Labels = raw20916step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20916step2 raw20916step2Labels permutation7 permutation0
    mixedMoment B raw20916step3 raw20916step3Labels = mixedMoment B raw20916step4 raw20916step4Labels := by
      have ha : raw20916step4 = -raw20916step3 := by apply Matrix.ext; change ∀ i j, raw20916step4 i j = -(raw20916step3 i j); unfold raw20916step4 raw20916step3; decide +kernel
      have hl : raw20916step4Labels = raw20916step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical20921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20921 raw20921Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw20921 raw20921Labels = mixedMoment B raw20921step0 raw20921step0Labels := by
      have hz : ∀ j, raw20921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20921step0 = (fun i j => raw20921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20921step0 raw20921; decide +kernel
      have hl : raw20921step0Labels = raw20921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20921 raw20921Labels permutation346 hz
    mixedMoment B raw20921step0 raw20921step0Labels = mixedMoment B raw20921step1 raw20921step1Labels := by
      have ha : raw20921step1 = (fun i j => raw20921step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20921step1 raw20921step0; decide +kernel
      have hl : raw20921step1Labels = raw20921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20921step0 raw20921step0Labels permutation151 permutation2
    mixedMoment B raw20921step1 raw20921step1Labels = mixedMoment B raw20921step2 raw20921step2Labels := by
      have ha : raw20921step2 = -raw20921step1 := by apply Matrix.ext; change ∀ i j, raw20921step2 i j = -(raw20921step1 i j); unfold raw20921step2 raw20921step1; decide +kernel
      have hl : raw20921step2Labels = raw20921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical20922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20922 raw20922Labels = mixedMoment B node1147 node1147Labels := by
  calc
    mixedMoment B raw20922 raw20922Labels = mixedMoment B raw20922step0 raw20922step0Labels := by
      have ha : raw20922step0 = (fun i j => raw20922 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20922step0 raw20922; decide +kernel
      have hl : raw20922step0Labels = raw20922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20922 raw20922Labels permutation158 permutation2
    _ = mixedMoment B node1147 node1147Labels := by rfl

theorem canonical20926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20926 raw20926Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw20926 raw20926Labels = mixedMoment B raw20926step0 raw20926step0Labels := by
      have hz : ∀ j, raw20926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20926step0 = (fun i j => raw20926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20926step0 raw20926; decide +kernel
      have hl : raw20926step0Labels = raw20926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926 raw20926Labels permutation346 hz
    mixedMoment B raw20926step0 raw20926step0Labels = mixedMoment B raw20926step1 raw20926step1Labels := by
      have hz : ∀ j, raw20926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20926step1 = (fun i j => raw20926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20926step1 raw20926step0; decide +kernel
      have hl : raw20926step1Labels = raw20926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926step0 raw20926step0Labels permutation56 hz
    mixedMoment B raw20926step1 raw20926step1Labels = mixedMoment B raw20926step2 raw20926step2Labels := by
      have ha : raw20926step2 = (fun i j => raw20926step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20926step2 raw20926step1; decide +kernel
      have hl : raw20926step2Labels = raw20926step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20926step1 raw20926step1Labels permutation31 permutation2
    mixedMoment B raw20926step2 raw20926step2Labels = mixedMoment B raw20926step3 raw20926step3Labels := by
      have ha : raw20926step3 = -raw20926step2 := by apply Matrix.ext; change ∀ i j, raw20926step3 i j = -(raw20926step2 i j); unfold raw20926step3 raw20926step2; decide +kernel
      have hl : raw20926step3Labels = raw20926step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2060 node2060Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21003 raw21003Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw21003 raw21003Labels = mixedMoment B raw21003step0 raw21003step0Labels := by
      have hz : ∀ j, raw21003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21003step0 = (fun i j => raw21003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21003step0 raw21003; decide +kernel
      have hl : raw21003step0Labels = raw21003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21003 raw21003Labels permutation346 hz
    mixedMoment B raw21003step0 raw21003step0Labels = mixedMoment B raw21003step1 raw21003step1Labels := by
      have ha : raw21003step1 = (fun i j => raw21003step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21003step1 raw21003step0; decide +kernel
      have hl : raw21003step1Labels = raw21003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21003step0 raw21003step0Labels permutation151 permutation2
    mixedMoment B raw21003step1 raw21003step1Labels = mixedMoment B raw21003step2 raw21003step2Labels := by
      have ha : raw21003step2 = -raw21003step1 := by apply Matrix.ext; change ∀ i j, raw21003step2 i j = -(raw21003step1 i j); unfold raw21003step2 raw21003step1; decide +kernel
      have hl : raw21003step2Labels = raw21003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2391 node2391Labels := by rfl

theorem canonical21007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21007 raw21007Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw21007 raw21007Labels = mixedMoment B raw21007step0 raw21007step0Labels := by
      have hz : ∀ j, raw21007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21007step0 = (fun i j => raw21007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21007step0 raw21007; decide +kernel
      have hl : raw21007step0Labels = raw21007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007 raw21007Labels permutation346 hz
    mixedMoment B raw21007step0 raw21007step0Labels = mixedMoment B raw21007step1 raw21007step1Labels := by
      have hz : ∀ j, raw21007step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21007step1 = (fun i j => raw21007step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21007step1 raw21007step0; decide +kernel
      have hl : raw21007step1Labels = raw21007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007step0 raw21007step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical21008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21008 raw21008Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw21008 raw21008Labels = mixedMoment B raw21008step0 raw21008step0Labels := by
      have hz : ∀ j, raw21008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21008step0 = (fun i j => raw21008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21008step0 raw21008; decide +kernel
      have hl : raw21008step0Labels = raw21008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008 raw21008Labels permutation346 hz
    mixedMoment B raw21008step0 raw21008step0Labels = mixedMoment B raw21008step1 raw21008step1Labels := by
      have hz : ∀ j, raw21008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21008step1 = (fun i j => raw21008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21008step1 raw21008step0; decide +kernel
      have hl : raw21008step1Labels = raw21008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008step0 raw21008step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical21014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21014 raw21014Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21014 raw21014Labels = mixedMoment B raw21014step0 raw21014step0Labels := by
      have hz : ∀ j, raw21014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21014step0 = (fun i j => raw21014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21014step0 raw21014; decide +kernel
      have hl : raw21014step0Labels = raw21014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21014 raw21014Labels permutation346 hz
    mixedMoment B raw21014step0 raw21014step0Labels = mixedMoment B raw21014step1 raw21014step1Labels := by
      have ha : raw21014step1 = (fun i j => raw21014step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21014step1 raw21014step0; decide +kernel
      have hl : raw21014step1Labels = raw21014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21014step0 raw21014step0Labels permutation151 permutation2
    mixedMoment B raw21014step1 raw21014step1Labels = mixedMoment B raw21014step2 raw21014step2Labels := by
      have ha : raw21014step2 = -raw21014step1 := by apply Matrix.ext; change ∀ i j, raw21014step2 i j = -(raw21014step1 i j); unfold raw21014step2 raw21014step1; decide +kernel
      have hl : raw21014step2Labels = raw21014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

theorem canonical21018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21018 raw21018Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw21018 raw21018Labels = mixedMoment B raw21018step0 raw21018step0Labels := by
      have hz : ∀ j, raw21018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21018step0 = (fun i j => raw21018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21018step0 raw21018; decide +kernel
      have hl : raw21018step0Labels = raw21018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018 raw21018Labels permutation346 hz
    mixedMoment B raw21018step0 raw21018step0Labels = mixedMoment B raw21018step1 raw21018step1Labels := by
      have hz : ∀ j, raw21018step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21018step1 = (fun i j => raw21018step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21018step1 raw21018step0; decide +kernel
      have hl : raw21018step1Labels = raw21018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018step0 raw21018step0Labels permutation56 hz
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical21019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21019 raw21019Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21019 raw21019Labels = mixedMoment B raw21019step0 raw21019step0Labels := by
      have hz : ∀ j, raw21019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21019step0 = (fun i j => raw21019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21019step0 raw21019; decide +kernel
      have hl : raw21019step0Labels = raw21019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019 raw21019Labels permutation346 hz
    mixedMoment B raw21019step0 raw21019step0Labels = mixedMoment B raw21019step1 raw21019step1Labels := by
      have hz : ∀ j, raw21019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21019step1 = (fun i j => raw21019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21019step1 raw21019step0; decide +kernel
      have hl : raw21019step1Labels = raw21019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019step0 raw21019step0Labels permutation56 hz
    mixedMoment B raw21019step1 raw21019step1Labels = mixedMoment B raw21019step2 raw21019step2Labels := by
      have ha : raw21019step2 = (fun i j => raw21019step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21019step2 raw21019step1; decide +kernel
      have hl : raw21019step2Labels = raw21019step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21019step1 raw21019step1Labels permutation30 permutation0
    mixedMoment B raw21019step2 raw21019step2Labels = mixedMoment B raw21019step3 raw21019step3Labels := by
      have ha : raw21019step3 = -raw21019step2 := by apply Matrix.ext; change ∀ i j, raw21019step3 i j = -(raw21019step2 i j); unfold raw21019step3 raw21019step2; decide +kernel
      have hl : raw21019step3Labels = raw21019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21041 raw21041Labels = mixedMoment B node2377 node2377Labels := by
  calc
    mixedMoment B raw21041 raw21041Labels = mixedMoment B raw21041step0 raw21041step0Labels := by
      have ha : raw21041step0 = (fun i j => raw21041 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21041step0 raw21041; decide +kernel
      have hl : raw21041step0Labels = raw21041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21041 raw21041Labels permutation682 permutation2
    mixedMoment B raw21041step0 raw21041step0Labels = mixedMoment B raw21041step1 raw21041step1Labels := by
      have ha : raw21041step1 = -raw21041step0 := by apply Matrix.ext; change ∀ i j, raw21041step1 i j = -(raw21041step0 i j); unfold raw21041step1 raw21041step0; decide +kernel
      have hl : raw21041step1Labels = raw21041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2377 node2377Labels := by rfl

theorem canonical21046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21046 raw21046Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw21046 raw21046Labels = mixedMoment B raw21046step0 raw21046step0Labels := by
      have hz : ∀ j, raw21046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21046step0 = (fun i j => raw21046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21046step0 raw21046; decide +kernel
      have hl : raw21046step0Labels = raw21046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21046 raw21046Labels permutation265 hz
    mixedMoment B raw21046step0 raw21046step0Labels = mixedMoment B raw21046step1 raw21046step1Labels := by
      have ha : raw21046step1 = (fun i j => raw21046step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21046step1 raw21046step0; decide +kernel
      have hl : raw21046step1Labels = raw21046step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21046step0 raw21046step0Labels permutation125 permutation0
    mixedMoment B raw21046step1 raw21046step1Labels = mixedMoment B raw21046step2 raw21046step2Labels := by
      have ha : raw21046step2 = -raw21046step1 := by apply Matrix.ext; change ∀ i j, raw21046step2 i j = -(raw21046step1 i j); unfold raw21046step2 raw21046step1; decide +kernel
      have hl : raw21046step2Labels = raw21046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22850 raw22850Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw22850 raw22850Labels = mixedMoment B raw22850step0 raw22850step0Labels := by
      have hz : ∀ j, raw22850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22850step0 = (fun i j => raw22850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22850step0 raw22850; decide +kernel
      have hl : raw22850step0Labels = raw22850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22850 raw22850Labels permutation346 hz
    _ = mixedMoment B node2539 node2539Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28750 raw28750Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw28750 raw28750Labels = mixedMoment B raw28750step0 raw28750step0Labels := by
      have hz : ∀ j, raw28750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28750step0 = (fun i j => raw28750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28750step0 raw28750; decide +kernel
      have hl : raw28750step0Labels = raw28750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28750 raw28750Labels permutation346 hz
    mixedMoment B raw28750step0 raw28750step0Labels = mixedMoment B raw28750step1 raw28750step1Labels := by
      have ha : raw28750step1 = (fun i j => raw28750step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28750step1 raw28750step0; decide +kernel
      have hl : raw28750step1Labels = raw28750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28750step0 raw28750step0Labels permutation151 permutation2
    mixedMoment B raw28750step1 raw28750step1Labels = mixedMoment B raw28750step2 raw28750step2Labels := by
      have ha : raw28750step2 = -raw28750step1 := by apply Matrix.ext; change ∀ i j, raw28750step2 i j = -(raw28750step1 i j); unfold raw28750step2 raw28750step1; decide +kernel
      have hl : raw28750step2Labels = raw28750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical28751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28751 raw28751Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw28751 raw28751Labels = mixedMoment B raw28751step0 raw28751step0Labels := by
      have ha : raw28751step0 = (fun i j => raw28751 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28751step0 raw28751; decide +kernel
      have hl : raw28751step0Labels = raw28751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28751 raw28751Labels permutation158 permutation2
    _ = mixedMoment B node2347 node2347Labels := by rfl

theorem canonical28752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28752 raw28752Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw28752 raw28752Labels = mixedMoment B raw28752step0 raw28752step0Labels := by
      have hz : ∀ j, raw28752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28752step0 = (fun i j => raw28752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28752step0 raw28752; decide +kernel
      have hl : raw28752step0Labels = raw28752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28752 raw28752Labels permutation346 hz
    _ = mixedMoment B node2355 node2355Labels := by rfl

theorem canonical28753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28753 raw28753Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw28753 raw28753Labels = mixedMoment B raw28753step0 raw28753step0Labels := by
      have hz : ∀ j, raw28753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28753step0 = (fun i j => raw28753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28753step0 raw28753; decide +kernel
      have hl : raw28753step0Labels = raw28753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28753 raw28753Labels permutation346 hz
    mixedMoment B raw28753step0 raw28753step0Labels = mixedMoment B raw28753step1 raw28753step1Labels := by
      have ha : raw28753step1 = (fun i j => raw28753step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28753step1 raw28753step0; decide +kernel
      have hl : raw28753step1Labels = raw28753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28753step0 raw28753step0Labels permutation151 permutation2
    mixedMoment B raw28753step1 raw28753step1Labels = mixedMoment B raw28753step2 raw28753step2Labels := by
      have ha : raw28753step2 = -raw28753step1 := by apply Matrix.ext; change ∀ i j, raw28753step2 i j = -(raw28753step1 i j); unfold raw28753step2 raw28753step1; decide +kernel
      have hl : raw28753step2Labels = raw28753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2325 node2325Labels := by rfl

theorem canonical28754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28754 raw28754Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw28754 raw28754Labels = mixedMoment B raw28754step0 raw28754step0Labels := by
      have hz : ∀ j, raw28754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28754step0 = (fun i j => raw28754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28754step0 raw28754; decide +kernel
      have hl : raw28754step0Labels = raw28754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28754 raw28754Labels permutation346 hz
    mixedMoment B raw28754step0 raw28754step0Labels = mixedMoment B raw28754step1 raw28754step1Labels := by
      have ha : raw28754step1 = (fun i j => raw28754step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28754step1 raw28754step0; decide +kernel
      have hl : raw28754step1Labels = raw28754step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28754step0 raw28754step0Labels permutation151 permutation2
    mixedMoment B raw28754step1 raw28754step1Labels = mixedMoment B raw28754step2 raw28754step2Labels := by
      have ha : raw28754step2 = -raw28754step1 := by apply Matrix.ext; change ∀ i j, raw28754step2 i j = -(raw28754step1 i j); unfold raw28754step2 raw28754step1; decide +kernel
      have hl : raw28754step2Labels = raw28754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1119 node1119Labels := by rfl

theorem canonical28755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28755 raw28755Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw28755 raw28755Labels = mixedMoment B raw28755step0 raw28755step0Labels := by
      have ha : raw28755step0 = (fun i j => raw28755 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28755step0 raw28755; decide +kernel
      have hl : raw28755step0Labels = raw28755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28755 raw28755Labels permutation686 permutation2
    mixedMoment B raw28755step0 raw28755step0Labels = mixedMoment B raw28755step1 raw28755step1Labels := by
      have ha : raw28755step1 = -raw28755step0 := by apply Matrix.ext; change ∀ i j, raw28755step1 i j = -(raw28755step0 i j); unfold raw28755step1 raw28755step0; decide +kernel
      have hl : raw28755step1Labels = raw28755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical28756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28756 raw28756Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw28756 raw28756Labels = mixedMoment B raw28756step0 raw28756step0Labels := by
      have hz : ∀ j, raw28756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28756step0 = (fun i j => raw28756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28756step0 raw28756; decide +kernel
      have hl : raw28756step0Labels = raw28756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28756 raw28756Labels permutation265 hz
    mixedMoment B raw28756step0 raw28756step0Labels = mixedMoment B raw28756step1 raw28756step1Labels := by
      have ha : raw28756step1 = (fun i j => raw28756step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28756step1 raw28756step0; decide +kernel
      have hl : raw28756step1Labels = raw28756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28756step0 raw28756step0Labels permutation151 permutation2
    mixedMoment B raw28756step1 raw28756step1Labels = mixedMoment B raw28756step2 raw28756step2Labels := by
      have ha : raw28756step2 = -raw28756step1 := by apply Matrix.ext; change ∀ i j, raw28756step2 i j = -(raw28756step1 i j); unfold raw28756step2 raw28756step1; decide +kernel
      have hl : raw28756step2Labels = raw28756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical28757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28757 raw28757Labels = mixedMoment B node2436 node2436Labels := by
  calc
    mixedMoment B raw28757 raw28757Labels = mixedMoment B raw28757step0 raw28757step0Labels := by
      have ha : raw28757step0 = (fun i j => raw28757 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28757step0 raw28757; decide +kernel
      have hl : raw28757step0Labels = raw28757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28757 raw28757Labels permutation686 permutation2
    mixedMoment B raw28757step0 raw28757step0Labels = mixedMoment B raw28757step1 raw28757step1Labels := by
      have ha : raw28757step1 = -raw28757step0 := by apply Matrix.ext; change ∀ i j, raw28757step1 i j = -(raw28757step0 i j); unfold raw28757step1 raw28757step0; decide +kernel
      have hl : raw28757step1Labels = raw28757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2436 node2436Labels := by rfl

theorem canonical28758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28758 raw28758Labels = mixedMoment B node2319 node2319Labels := by
  calc
    mixedMoment B raw28758 raw28758Labels = mixedMoment B raw28758step0 raw28758step0Labels := by
      have ha : raw28758step0 = (fun i j => raw28758 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28758step0 raw28758; decide +kernel
      have hl : raw28758step0Labels = raw28758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28758 raw28758Labels permutation686 permutation2
    mixedMoment B raw28758step0 raw28758step0Labels = mixedMoment B raw28758step1 raw28758step1Labels := by
      have ha : raw28758step1 = -raw28758step0 := by apply Matrix.ext; change ∀ i j, raw28758step1 i j = -(raw28758step0 i j); unfold raw28758step1 raw28758step0; decide +kernel
      have hl : raw28758step1Labels = raw28758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2319 node2319Labels := by rfl

theorem canonical28759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28759 raw28759Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw28759 raw28759Labels = mixedMoment B raw28759step0 raw28759step0Labels := by
      have ha : raw28759step0 = (fun i j => raw28759 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28759step0 raw28759; decide +kernel
      have hl : raw28759step0Labels = raw28759Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28759 raw28759Labels permutation686 permutation2
    mixedMoment B raw28759step0 raw28759step0Labels = mixedMoment B raw28759step1 raw28759step1Labels := by
      have ha : raw28759step1 = -raw28759step0 := by apply Matrix.ext; change ∀ i j, raw28759step1 i j = -(raw28759step0 i j); unfold raw28759step1 raw28759step0; decide +kernel
      have hl : raw28759step1Labels = raw28759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1111 node1111Labels := by rfl

theorem canonical28760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28760 raw28760Labels = mixedMoment B node2511 node2511Labels := by
  calc
    mixedMoment B raw28760 raw28760Labels = mixedMoment B raw28760step0 raw28760step0Labels := by
      have hz : ∀ j, raw28760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28760step0 = (fun i j => raw28760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28760step0 raw28760; decide +kernel
      have hl : raw28760step0Labels = raw28760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28760 raw28760Labels permutation346 hz
    mixedMoment B raw28760step0 raw28760step0Labels = mixedMoment B raw28760step1 raw28760step1Labels := by
      have ha : raw28760step1 = (fun i j => raw28760step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28760step1 raw28760step0; decide +kernel
      have hl : raw28760step1Labels = raw28760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28760step0 raw28760step0Labels permutation149 permutation2
    mixedMoment B raw28760step1 raw28760step1Labels = mixedMoment B raw28760step2 raw28760step2Labels := by
      have ha : raw28760step2 = -raw28760step1 := by apply Matrix.ext; change ∀ i j, raw28760step2 i j = -(raw28760step1 i j); unfold raw28760step2 raw28760step1; decide +kernel
      have hl : raw28760step2Labels = raw28760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2511 node2511Labels := by rfl

theorem canonical28761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28761 raw28761Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw28761 raw28761Labels = mixedMoment B raw28761step0 raw28761step0Labels := by
      have ha : raw28761step0 = (fun i j => raw28761 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28761step0 raw28761; decide +kernel
      have hl : raw28761step0Labels = raw28761Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28761 raw28761Labels permutation200 permutation2
    _ = mixedMoment B node2425 node2425Labels := by rfl

theorem canonical28762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28762 raw28762Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw28762 raw28762Labels = mixedMoment B raw28762step0 raw28762step0Labels := by
      have hz : ∀ j, raw28762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28762step0 = (fun i j => raw28762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28762step0 raw28762; decide +kernel
      have hl : raw28762step0Labels = raw28762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28762 raw28762Labels permutation346 hz
    mixedMoment B raw28762step0 raw28762step0Labels = mixedMoment B raw28762step1 raw28762step1Labels := by
      have ha : raw28762step1 = (fun i j => raw28762step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28762step1 raw28762step0; decide +kernel
      have hl : raw28762step1Labels = raw28762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28762step0 raw28762step0Labels permutation149 permutation2
    mixedMoment B raw28762step1 raw28762step1Labels = mixedMoment B raw28762step2 raw28762step2Labels := by
      have ha : raw28762step2 = -raw28762step1 := by apply Matrix.ext; change ∀ i j, raw28762step2 i j = -(raw28762step1 i j); unfold raw28762step2 raw28762step1; decide +kernel
      have hl : raw28762step2Labels = raw28762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

theorem canonical28763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28763 raw28763Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw28763 raw28763Labels = mixedMoment B raw28763step0 raw28763step0Labels := by
      have hz : ∀ j, raw28763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28763step0 = (fun i j => raw28763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28763step0 raw28763; decide +kernel
      have hl : raw28763step0Labels = raw28763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28763 raw28763Labels permutation346 hz
    mixedMoment B raw28763step0 raw28763step0Labels = mixedMoment B raw28763step1 raw28763step1Labels := by
      have ha : raw28763step1 = (fun i j => raw28763step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28763step1 raw28763step0; decide +kernel
      have hl : raw28763step1Labels = raw28763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28763step0 raw28763step0Labels permutation149 permutation2
    mixedMoment B raw28763step1 raw28763step1Labels = mixedMoment B raw28763step2 raw28763step2Labels := by
      have ha : raw28763step2 = -raw28763step1 := by apply Matrix.ext; change ∀ i j, raw28763step2 i j = -(raw28763step1 i j); unfold raw28763step2 raw28763step1; decide +kernel
      have hl : raw28763step2Labels = raw28763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1131 node1131Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28852 raw28852Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28852 raw28852Labels = mixedMoment B raw28852step0 raw28852step0Labels := by
      have hz : ∀ j, raw28852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28852step0 = (fun i j => raw28852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28852step0 raw28852; decide +kernel
      have hl : raw28852step0Labels = raw28852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28852 raw28852Labels permutation346 hz
    mixedMoment B raw28852step0 raw28852step0Labels = mixedMoment B raw28852step1 raw28852step1Labels := by
      have ha : raw28852step1 = (fun i j => raw28852step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28852step1 raw28852step0; decide +kernel
      have hl : raw28852step1Labels = raw28852step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28852step0 raw28852step0Labels permutation149 permutation7
    mixedMoment B raw28852step1 raw28852step1Labels = mixedMoment B raw28852step2 raw28852step2Labels := by
      have ha : raw28852step2 = raw28852step1 := by apply Matrix.ext; unfold raw28852step2 raw28852step1; decide +kernel
      have hl : raw28852step1Labels = labelEmbedding1 ∘ raw28852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28852step1 raw28852step1Labels raw28852step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical28853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28853 raw28853Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw28853 raw28853Labels = mixedMoment B raw28853step0 raw28853step0Labels := by
      have ha : raw28853step0 = (fun i j => raw28853 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28853step0 raw28853; decide +kernel
      have hl : raw28853step0Labels = raw28853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28853 raw28853Labels permutation674 permutation7
    mixedMoment B raw28853step0 raw28853step0Labels = mixedMoment B raw28853step1 raw28853step1Labels := by
      have ha : raw28853step1 = raw28853step0 := by apply Matrix.ext; unfold raw28853step1 raw28853step0; decide +kernel
      have hl : raw28853step0Labels = labelEmbedding1 ∘ raw28853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28853step0 raw28853step0Labels raw28853step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical28854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28854 raw28854Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw28854 raw28854Labels = mixedMoment B raw28854step0 raw28854step0Labels := by
      have hz : ∀ j, raw28854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28854step0 = (fun i j => raw28854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28854step0 raw28854; decide +kernel
      have hl : raw28854step0Labels = raw28854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28854 raw28854Labels permutation346 hz
    mixedMoment B raw28854step0 raw28854step0Labels = mixedMoment B raw28854step1 raw28854step1Labels := by
      have ha : raw28854step1 = (fun i j => raw28854step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28854step1 raw28854step0; decide +kernel
      have hl : raw28854step1Labels = raw28854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28854step0 raw28854step0Labels permutation149 permutation7
    mixedMoment B raw28854step1 raw28854step1Labels = mixedMoment B raw28854step2 raw28854step2Labels := by
      have ha : raw28854step2 = raw28854step1 := by apply Matrix.ext; unfold raw28854step2 raw28854step1; decide +kernel
      have hl : raw28854step1Labels = labelEmbedding1 ∘ raw28854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28854step1 raw28854step1Labels raw28854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical28855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28855 raw28855Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw28855 raw28855Labels = mixedMoment B raw28855step0 raw28855step0Labels := by
      have hz : ∀ j, raw28855 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28855step0 = (fun i j => raw28855 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28855step0 raw28855; decide +kernel
      have hl : raw28855step0Labels = raw28855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28855 raw28855Labels permutation520 hz
    mixedMoment B raw28855step0 raw28855step0Labels = mixedMoment B raw28855step1 raw28855step1Labels := by
      have hz : ∀ j, raw28855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28855step1 = (fun i j => raw28855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28855step1 raw28855step0; decide +kernel
      have hl : raw28855step1Labels = raw28855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28855step0 raw28855step0Labels permutation80 hz
    mixedMoment B raw28855step1 raw28855step1Labels = mixedMoment B raw28855step2 raw28855step2Labels := by
      have ha : raw28855step2 = (fun i j => raw28855step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28855step2 raw28855step1; decide +kernel
      have hl : raw28855step2Labels = raw28855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28855step1 raw28855step1Labels permutation29 permutation7
    mixedMoment B raw28855step2 raw28855step2Labels = mixedMoment B raw28855step3 raw28855step3Labels := by
      have ha : raw28855step3 = raw28855step2 := by apply Matrix.ext; unfold raw28855step3 raw28855step2; decide +kernel
      have hl : raw28855step2Labels = labelEmbedding1 ∘ raw28855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28855step2 raw28855step2Labels raw28855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical28856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28856 raw28856Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw28856 raw28856Labels = mixedMoment B raw28856step0 raw28856step0Labels := by
      have ha : raw28856step0 = (fun i j => raw28856 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28856step0 raw28856; decide +kernel
      have hl : raw28856step0Labels = raw28856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28856 raw28856Labels permutation644 permutation7
    mixedMoment B raw28856step0 raw28856step0Labels = mixedMoment B raw28856step1 raw28856step1Labels := by
      have ha : raw28856step1 = raw28856step0 := by apply Matrix.ext; unfold raw28856step1 raw28856step0; decide +kernel
      have hl : raw28856step0Labels = labelEmbedding1 ∘ raw28856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28856step0 raw28856step0Labels raw28856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

theorem canonical28857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28857 raw28857Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw28857 raw28857Labels = mixedMoment B raw28857step0 raw28857step0Labels := by
      have ha : raw28857step0 = (fun i j => raw28857 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28857step0 raw28857; decide +kernel
      have hl : raw28857step0Labels = raw28857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28857 raw28857Labels permutation644 permutation7
    mixedMoment B raw28857step0 raw28857step0Labels = mixedMoment B raw28857step1 raw28857step1Labels := by
      have ha : raw28857step1 = raw28857step0 := by apply Matrix.ext; unfold raw28857step1 raw28857step0; decide +kernel
      have hl : raw28857step0Labels = labelEmbedding1 ∘ raw28857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28857step0 raw28857step0Labels raw28857step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical28858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28858 raw28858Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw28858 raw28858Labels = mixedMoment B raw28858step0 raw28858step0Labels := by
      have hz : ∀ j, raw28858 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28858step0 = (fun i j => raw28858 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28858step0 raw28858; decide +kernel
      have hl : raw28858step0Labels = raw28858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28858 raw28858Labels permutation520 hz
    mixedMoment B raw28858step0 raw28858step0Labels = mixedMoment B raw28858step1 raw28858step1Labels := by
      have ha : raw28858step1 = (fun i j => raw28858step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28858step1 raw28858step0; decide +kernel
      have hl : raw28858step1Labels = raw28858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28858step0 raw28858step0Labels permutation143 permutation7
    mixedMoment B raw28858step1 raw28858step1Labels = mixedMoment B raw28858step2 raw28858step2Labels := by
      have ha : raw28858step2 = raw28858step1 := by apply Matrix.ext; unfold raw28858step2 raw28858step1; decide +kernel
      have hl : raw28858step1Labels = labelEmbedding1 ∘ raw28858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28858step1 raw28858step1Labels raw28858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical28859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28859 raw28859Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28859 raw28859Labels = mixedMoment B raw28859step0 raw28859step0Labels := by
      have hz : ∀ j, raw28859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28859step0 = (fun i j => raw28859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28859step0 raw28859; decide +kernel
      have hl : raw28859step0Labels = raw28859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28859 raw28859Labels permutation346 hz
    mixedMoment B raw28859step0 raw28859step0Labels = mixedMoment B raw28859step1 raw28859step1Labels := by
      have ha : raw28859step1 = (fun i j => raw28859step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28859step1 raw28859step0; decide +kernel
      have hl : raw28859step1Labels = raw28859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28859step0 raw28859step0Labels permutation149 permutation7
    mixedMoment B raw28859step1 raw28859step1Labels = mixedMoment B raw28859step2 raw28859step2Labels := by
      have ha : raw28859step2 = raw28859step1 := by apply Matrix.ext; unfold raw28859step2 raw28859step1; decide +kernel
      have hl : raw28859step1Labels = labelEmbedding1 ∘ raw28859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28859step1 raw28859step1Labels raw28859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical28860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28860 raw28860Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28860 raw28860Labels = mixedMoment B raw28860step0 raw28860step0Labels := by
      have ha : raw28860step0 = (fun i j => raw28860 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28860step0 raw28860; decide +kernel
      have hl : raw28860step0Labels = raw28860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28860 raw28860Labels permutation674 permutation7
    mixedMoment B raw28860step0 raw28860step0Labels = mixedMoment B raw28860step1 raw28860step1Labels := by
      have ha : raw28860step1 = raw28860step0 := by apply Matrix.ext; unfold raw28860step1 raw28860step0; decide +kernel
      have hl : raw28860step0Labels = labelEmbedding1 ∘ raw28860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28860step0 raw28860step0Labels raw28860step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical28861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28861 raw28861Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw28861 raw28861Labels = mixedMoment B raw28861step0 raw28861step0Labels := by
      have hz : ∀ j, raw28861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28861step0 = (fun i j => raw28861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28861step0 raw28861; decide +kernel
      have hl : raw28861step0Labels = raw28861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28861 raw28861Labels permutation520 hz
    mixedMoment B raw28861step0 raw28861step0Labels = mixedMoment B raw28861step1 raw28861step1Labels := by
      have hz : ∀ j, raw28861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28861step1 = (fun i j => raw28861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28861step1 raw28861step0; decide +kernel
      have hl : raw28861step1Labels = raw28861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28861step0 raw28861step0Labels permutation80 hz
    mixedMoment B raw28861step1 raw28861step1Labels = mixedMoment B raw28861step2 raw28861step2Labels := by
      have ha : raw28861step2 = (fun i j => raw28861step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28861step2 raw28861step1; decide +kernel
      have hl : raw28861step2Labels = raw28861step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28861step1 raw28861step1Labels permutation29 permutation7
    mixedMoment B raw28861step2 raw28861step2Labels = mixedMoment B raw28861step3 raw28861step3Labels := by
      have ha : raw28861step3 = raw28861step2 := by apply Matrix.ext; unfold raw28861step3 raw28861step2; decide +kernel
      have hl : raw28861step2Labels = labelEmbedding1 ∘ raw28861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28861step2 raw28861step2Labels raw28861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical28862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28862 raw28862Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw28862 raw28862Labels = mixedMoment B raw28862step0 raw28862step0Labels := by
      have hz : ∀ j, raw28862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28862step0 = (fun i j => raw28862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28862step0 raw28862; decide +kernel
      have hl : raw28862step0Labels = raw28862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28862 raw28862Labels permutation346 hz
    mixedMoment B raw28862step0 raw28862step0Labels = mixedMoment B raw28862step1 raw28862step1Labels := by
      have ha : raw28862step1 = (fun i j => raw28862step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28862step1 raw28862step0; decide +kernel
      have hl : raw28862step1Labels = raw28862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28862step0 raw28862step0Labels permutation149 permutation7
    mixedMoment B raw28862step1 raw28862step1Labels = mixedMoment B raw28862step2 raw28862step2Labels := by
      have ha : raw28862step2 = raw28862step1 := by apply Matrix.ext; unfold raw28862step2 raw28862step1; decide +kernel
      have hl : raw28862step1Labels = labelEmbedding1 ∘ raw28862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28862step1 raw28862step1Labels raw28862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical28863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28863 raw28863Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw28863 raw28863Labels = mixedMoment B raw28863step0 raw28863step0Labels := by
      have ha : raw28863step0 = (fun i j => raw28863 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28863step0 raw28863; decide +kernel
      have hl : raw28863step0Labels = raw28863Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28863 raw28863Labels permutation674 permutation7
    mixedMoment B raw28863step0 raw28863step0Labels = mixedMoment B raw28863step1 raw28863step1Labels := by
      have ha : raw28863step1 = raw28863step0 := by apply Matrix.ext; unfold raw28863step1 raw28863step0; decide +kernel
      have hl : raw28863step0Labels = labelEmbedding1 ∘ raw28863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28863step0 raw28863step0Labels raw28863step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical28864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28864 raw28864Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw28864 raw28864Labels = mixedMoment B raw28864step0 raw28864step0Labels := by
      have hz : ∀ j, raw28864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28864step0 = (fun i j => raw28864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28864step0 raw28864; decide +kernel
      have hl : raw28864step0Labels = raw28864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28864 raw28864Labels permutation346 hz
    mixedMoment B raw28864step0 raw28864step0Labels = mixedMoment B raw28864step1 raw28864step1Labels := by
      have ha : raw28864step1 = (fun i j => raw28864step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28864step1 raw28864step0; decide +kernel
      have hl : raw28864step1Labels = raw28864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28864step0 raw28864step0Labels permutation149 permutation7
    mixedMoment B raw28864step1 raw28864step1Labels = mixedMoment B raw28864step2 raw28864step2Labels := by
      have ha : raw28864step2 = raw28864step1 := by apply Matrix.ext; unfold raw28864step2 raw28864step1; decide +kernel
      have hl : raw28864step1Labels = labelEmbedding1 ∘ raw28864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28864step1 raw28864step1Labels raw28864step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical28865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28865 raw28865Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw28865 raw28865Labels = mixedMoment B raw28865step0 raw28865step0Labels := by
      have hz : ∀ j, raw28865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28865step0 = (fun i j => raw28865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28865step0 raw28865; decide +kernel
      have hl : raw28865step0Labels = raw28865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28865 raw28865Labels permutation346 hz
    mixedMoment B raw28865step0 raw28865step0Labels = mixedMoment B raw28865step1 raw28865step1Labels := by
      have ha : raw28865step1 = (fun i j => raw28865step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28865step1 raw28865step0; decide +kernel
      have hl : raw28865step1Labels = raw28865step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28865step0 raw28865step0Labels permutation149 permutation7
    mixedMoment B raw28865step1 raw28865step1Labels = mixedMoment B raw28865step2 raw28865step2Labels := by
      have ha : raw28865step2 = raw28865step1 := by apply Matrix.ext; unfold raw28865step2 raw28865step1; decide +kernel
      have hl : raw28865step1Labels = labelEmbedding1 ∘ raw28865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28865step1 raw28865step1Labels raw28865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical28866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28866 raw28866Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw28866 raw28866Labels = mixedMoment B raw28866step0 raw28866step0Labels := by
      have ha : raw28866step0 = (fun i j => raw28866 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28866step0 raw28866; decide +kernel
      have hl : raw28866step0Labels = raw28866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28866 raw28866Labels permutation674 permutation7
    mixedMoment B raw28866step0 raw28866step0Labels = mixedMoment B raw28866step1 raw28866step1Labels := by
      have ha : raw28866step1 = raw28866step0 := by apply Matrix.ext; unfold raw28866step1 raw28866step0; decide +kernel
      have hl : raw28866step0Labels = labelEmbedding1 ∘ raw28866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28866step0 raw28866step0Labels raw28866step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

theorem canonical28867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28867 raw28867Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw28867 raw28867Labels = mixedMoment B raw28867step0 raw28867step0Labels := by
      have hz : ∀ j, raw28867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28867step0 = (fun i j => raw28867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28867step0 raw28867; decide +kernel
      have hl : raw28867step0Labels = raw28867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28867 raw28867Labels permutation346 hz
    mixedMoment B raw28867step0 raw28867step0Labels = mixedMoment B raw28867step1 raw28867step1Labels := by
      have ha : raw28867step1 = (fun i j => raw28867step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28867step1 raw28867step0; decide +kernel
      have hl : raw28867step1Labels = raw28867step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28867step0 raw28867step0Labels permutation149 permutation7
    mixedMoment B raw28867step1 raw28867step1Labels = mixedMoment B raw28867step2 raw28867step2Labels := by
      have ha : raw28867step2 = raw28867step1 := by apply Matrix.ext; unfold raw28867step2 raw28867step1; decide +kernel
      have hl : raw28867step1Labels = labelEmbedding1 ∘ raw28867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28867step1 raw28867step1Labels raw28867step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical28868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28868 raw28868Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw28868 raw28868Labels = mixedMoment B raw28868step0 raw28868step0Labels := by
      have hz : ∀ j, raw28868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28868step0 = (fun i j => raw28868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28868step0 raw28868; decide +kernel
      have hl : raw28868step0Labels = raw28868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28868 raw28868Labels permutation520 hz
    mixedMoment B raw28868step0 raw28868step0Labels = mixedMoment B raw28868step1 raw28868step1Labels := by
      have hz : ∀ j, raw28868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28868step1 = (fun i j => raw28868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28868step1 raw28868step0; decide +kernel
      have hl : raw28868step1Labels = raw28868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28868step0 raw28868step0Labels permutation80 hz
    mixedMoment B raw28868step1 raw28868step1Labels = mixedMoment B raw28868step2 raw28868step2Labels := by
      have ha : raw28868step2 = (fun i j => raw28868step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28868step2 raw28868step1; decide +kernel
      have hl : raw28868step2Labels = raw28868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28868step1 raw28868step1Labels permutation29 permutation7
    mixedMoment B raw28868step2 raw28868step2Labels = mixedMoment B raw28868step3 raw28868step3Labels := by
      have ha : raw28868step3 = raw28868step2 := by apply Matrix.ext; unfold raw28868step3 raw28868step2; decide +kernel
      have hl : raw28868step2Labels = labelEmbedding1 ∘ raw28868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28868step2 raw28868step2Labels raw28868step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical28869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28869 raw28869Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw28869 raw28869Labels = mixedMoment B raw28869step0 raw28869step0Labels := by
      have hz : ∀ j, raw28869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28869step0 = (fun i j => raw28869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28869step0 raw28869; decide +kernel
      have hl : raw28869step0Labels = raw28869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28869 raw28869Labels permutation346 hz
    mixedMoment B raw28869step0 raw28869step0Labels = mixedMoment B raw28869step1 raw28869step1Labels := by
      have ha : raw28869step1 = (fun i j => raw28869step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28869step1 raw28869step0; decide +kernel
      have hl : raw28869step1Labels = raw28869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28869step0 raw28869step0Labels permutation151 permutation2
    mixedMoment B raw28869step1 raw28869step1Labels = mixedMoment B raw28869step2 raw28869step2Labels := by
      have ha : raw28869step2 = -raw28869step1 := by apply Matrix.ext; change ∀ i j, raw28869step2 i j = -(raw28869step1 i j); unfold raw28869step2 raw28869step1; decide +kernel
      have hl : raw28869step2Labels = raw28869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical28870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28870 raw28870Labels = mixedMoment B node1955 node1955Labels := by
  calc
    mixedMoment B raw28870 raw28870Labels = mixedMoment B raw28870step0 raw28870step0Labels := by
      have ha : raw28870step0 = (fun i j => raw28870 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28870step0 raw28870; decide +kernel
      have hl : raw28870step0Labels = raw28870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28870 raw28870Labels permutation646 permutation2
    mixedMoment B raw28870step0 raw28870step0Labels = mixedMoment B raw28870step1 raw28870step1Labels := by
      have ha : raw28870step1 = -raw28870step0 := by apply Matrix.ext; change ∀ i j, raw28870step1 i j = -(raw28870step0 i j); unfold raw28870step1 raw28870step0; decide +kernel
      have hl : raw28870step1Labels = raw28870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1955 node1955Labels := by rfl

theorem canonical28871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28871 raw28871Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28871 raw28871Labels = mixedMoment B raw28871step0 raw28871step0Labels := by
      have hz : ∀ j, raw28871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28871step0 = (fun i j => raw28871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28871step0 raw28871; decide +kernel
      have hl : raw28871step0Labels = raw28871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28871 raw28871Labels permutation346 hz
    mixedMoment B raw28871step0 raw28871step0Labels = mixedMoment B raw28871step1 raw28871step1Labels := by
      have ha : raw28871step1 = (fun i j => raw28871step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28871step1 raw28871step0; decide +kernel
      have hl : raw28871step1Labels = raw28871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28871step0 raw28871step0Labels permutation151 permutation2
    mixedMoment B raw28871step1 raw28871step1Labels = mixedMoment B raw28871step2 raw28871step2Labels := by
      have ha : raw28871step2 = -raw28871step1 := by apply Matrix.ext; change ∀ i j, raw28871step2 i j = -(raw28871step1 i j); unfold raw28871step2 raw28871step1; decide +kernel
      have hl : raw28871step2Labels = raw28871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

theorem canonical28872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28872 raw28872Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw28872 raw28872Labels = mixedMoment B raw28872step0 raw28872step0Labels := by
      have hz : ∀ j, raw28872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28872step0 = (fun i j => raw28872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28872step0 raw28872; decide +kernel
      have hl : raw28872step0Labels = raw28872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28872 raw28872Labels permutation346 hz
    mixedMoment B raw28872step0 raw28872step0Labels = mixedMoment B raw28872step1 raw28872step1Labels := by
      have ha : raw28872step1 = (fun i j => raw28872step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28872step1 raw28872step0; decide +kernel
      have hl : raw28872step1Labels = raw28872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28872step0 raw28872step0Labels permutation151 permutation2
    mixedMoment B raw28872step1 raw28872step1Labels = mixedMoment B raw28872step2 raw28872step2Labels := by
      have ha : raw28872step2 = -raw28872step1 := by apply Matrix.ext; change ∀ i j, raw28872step2 i j = -(raw28872step1 i j); unfold raw28872step2 raw28872step1; decide +kernel
      have hl : raw28872step2Labels = raw28872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1795 node1795Labels := by rfl

theorem canonical28873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28873 raw28873Labels = mixedMoment B node912 node912Labels := by
  calc
    mixedMoment B raw28873 raw28873Labels = mixedMoment B raw28873step0 raw28873step0Labels := by
      have hz : ∀ j, raw28873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28873step0 = (fun i j => raw28873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28873step0 raw28873; decide +kernel
      have hl : raw28873step0Labels = raw28873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28873 raw28873Labels permutation346 hz
    mixedMoment B raw28873step0 raw28873step0Labels = mixedMoment B raw28873step1 raw28873step1Labels := by
      have ha : raw28873step1 = (fun i j => raw28873step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28873step1 raw28873step0; decide +kernel
      have hl : raw28873step1Labels = raw28873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28873step0 raw28873step0Labels permutation151 permutation2
    mixedMoment B raw28873step1 raw28873step1Labels = mixedMoment B raw28873step2 raw28873step2Labels := by
      have ha : raw28873step2 = -raw28873step1 := by apply Matrix.ext; change ∀ i j, raw28873step2 i j = -(raw28873step1 i j); unfold raw28873step2 raw28873step1; decide +kernel
      have hl : raw28873step2Labels = raw28873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node912 node912Labels := by rfl

theorem canonical28874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28874 raw28874Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw28874 raw28874Labels = mixedMoment B raw28874step0 raw28874step0Labels := by
      have ha : raw28874step0 = (fun i j => raw28874 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28874step0 raw28874; decide +kernel
      have hl : raw28874step0Labels = raw28874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28874 raw28874Labels permutation644 permutation2
    mixedMoment B raw28874step0 raw28874step0Labels = mixedMoment B raw28874step1 raw28874step1Labels := by
      have ha : raw28874step1 = -raw28874step0 := by apply Matrix.ext; change ∀ i j, raw28874step1 i j = -(raw28874step0 i j); unfold raw28874step1 raw28874step0; decide +kernel
      have hl : raw28874step1Labels = raw28874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical28875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28875 raw28875Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw28875 raw28875Labels = mixedMoment B raw28875step0 raw28875step0Labels := by
      have hz : ∀ j, raw28875 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28875step0 = (fun i j => raw28875 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28875step0 raw28875; decide +kernel
      have hl : raw28875step0Labels = raw28875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28875 raw28875Labels permutation520 hz
    mixedMoment B raw28875step0 raw28875step0Labels = mixedMoment B raw28875step1 raw28875step1Labels := by
      have ha : raw28875step1 = (fun i j => raw28875step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28875step1 raw28875step0; decide +kernel
      have hl : raw28875step1Labels = raw28875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28875step0 raw28875step0Labels permutation145 permutation2
    mixedMoment B raw28875step1 raw28875step1Labels = mixedMoment B raw28875step2 raw28875step2Labels := by
      have ha : raw28875step2 = -raw28875step1 := by apply Matrix.ext; change ∀ i j, raw28875step2 i j = -(raw28875step1 i j); unfold raw28875step2 raw28875step1; decide +kernel
      have hl : raw28875step2Labels = raw28875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical28876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28876 raw28876Labels = mixedMoment B node2552 node2552Labels := by
  calc
    mixedMoment B raw28876 raw28876Labels = mixedMoment B raw28876step0 raw28876step0Labels := by
      have ha : raw28876step0 = (fun i j => raw28876 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28876step0 raw28876; decide +kernel
      have hl : raw28876step0Labels = raw28876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28876 raw28876Labels permutation158 permutation2
    _ = mixedMoment B node2552 node2552Labels := by rfl

theorem canonical28877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28877 raw28877Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw28877 raw28877Labels = mixedMoment B raw28877step0 raw28877step0Labels := by
      have ha : raw28877step0 = (fun i j => raw28877 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28877step0 raw28877; decide +kernel
      have hl : raw28877step0Labels = raw28877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28877 raw28877Labels permutation686 permutation2
    mixedMoment B raw28877step0 raw28877step0Labels = mixedMoment B raw28877step1 raw28877step1Labels := by
      have ha : raw28877step1 = -raw28877step0 := by apply Matrix.ext; change ∀ i j, raw28877step1 i j = -(raw28877step0 i j); unfold raw28877step1 raw28877step0; decide +kernel
      have hl : raw28877step1Labels = raw28877step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical28878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28878 raw28878Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw28878 raw28878Labels = mixedMoment B raw28878step0 raw28878step0Labels := by
      have hz : ∀ j, raw28878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28878step0 = (fun i j => raw28878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28878step0 raw28878; decide +kernel
      have hl : raw28878step0Labels = raw28878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28878 raw28878Labels permutation265 hz
    mixedMoment B raw28878step0 raw28878step0Labels = mixedMoment B raw28878step1 raw28878step1Labels := by
      have ha : raw28878step1 = (fun i j => raw28878step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28878step1 raw28878step0; decide +kernel
      have hl : raw28878step1Labels = raw28878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28878step0 raw28878step0Labels permutation151 permutation2
    mixedMoment B raw28878step1 raw28878step1Labels = mixedMoment B raw28878step2 raw28878step2Labels := by
      have ha : raw28878step2 = -raw28878step1 := by apply Matrix.ext; change ∀ i j, raw28878step2 i j = -(raw28878step1 i j); unfold raw28878step2 raw28878step1; decide +kernel
      have hl : raw28878step2Labels = raw28878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical28879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28879 raw28879Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28879 raw28879Labels = mixedMoment B raw28879step0 raw28879step0Labels := by
      have ha : raw28879step0 = (fun i j => raw28879 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28879step0 raw28879; decide +kernel
      have hl : raw28879step0Labels = raw28879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28879 raw28879Labels permutation686 permutation2
    mixedMoment B raw28879step0 raw28879step0Labels = mixedMoment B raw28879step1 raw28879step1Labels := by
      have ha : raw28879step1 = -raw28879step0 := by apply Matrix.ext; change ∀ i j, raw28879step1 i j = -(raw28879step0 i j); unfold raw28879step1 raw28879step0; decide +kernel
      have hl : raw28879step1Labels = raw28879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

theorem canonical28880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28880 raw28880Labels = mixedMoment B node1789 node1789Labels := by
  calc
    mixedMoment B raw28880 raw28880Labels = mixedMoment B raw28880step0 raw28880step0Labels := by
      have ha : raw28880step0 = (fun i j => raw28880 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28880step0 raw28880; decide +kernel
      have hl : raw28880step0Labels = raw28880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28880 raw28880Labels permutation686 permutation2
    mixedMoment B raw28880step0 raw28880step0Labels = mixedMoment B raw28880step1 raw28880step1Labels := by
      have ha : raw28880step1 = -raw28880step0 := by apply Matrix.ext; change ∀ i j, raw28880step1 i j = -(raw28880step0 i j); unfold raw28880step1 raw28880step0; decide +kernel
      have hl : raw28880step1Labels = raw28880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1789 node1789Labels := by rfl

theorem canonical28881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28881 raw28881Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw28881 raw28881Labels = mixedMoment B raw28881step0 raw28881step0Labels := by
      have ha : raw28881step0 = (fun i j => raw28881 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28881step0 raw28881; decide +kernel
      have hl : raw28881step0Labels = raw28881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28881 raw28881Labels permutation686 permutation2
    mixedMoment B raw28881step0 raw28881step0Labels = mixedMoment B raw28881step1 raw28881step1Labels := by
      have ha : raw28881step1 = -raw28881step0 := by apply Matrix.ext; change ∀ i j, raw28881step1 i j = -(raw28881step0 i j); unfold raw28881step1 raw28881step0; decide +kernel
      have hl : raw28881step1Labels = raw28881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node904 node904Labels := by rfl

theorem canonical28882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28882 raw28882Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw28882 raw28882Labels = mixedMoment B raw28882step0 raw28882step0Labels := by
      have hz : ∀ j, raw28882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28882step0 = (fun i j => raw28882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28882step0 raw28882; decide +kernel
      have hl : raw28882step0Labels = raw28882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28882 raw28882Labels permutation346 hz
    mixedMoment B raw28882step0 raw28882step0Labels = mixedMoment B raw28882step1 raw28882step1Labels := by
      have ha : raw28882step1 = (fun i j => raw28882step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28882step1 raw28882step0; decide +kernel
      have hl : raw28882step1Labels = raw28882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28882step0 raw28882step0Labels permutation149 permutation2
    mixedMoment B raw28882step1 raw28882step1Labels = mixedMoment B raw28882step2 raw28882step2Labels := by
      have ha : raw28882step2 = -raw28882step1 := by apply Matrix.ext; change ∀ i j, raw28882step2 i j = -(raw28882step1 i j); unfold raw28882step2 raw28882step1; decide +kernel
      have hl : raw28882step2Labels = raw28882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2053 node2053Labels := by rfl

theorem canonical28883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28883 raw28883Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw28883 raw28883Labels = mixedMoment B raw28883step0 raw28883step0Labels := by
      have hz : ∀ j, raw28883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28883step0 = (fun i j => raw28883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28883step0 raw28883; decide +kernel
      have hl : raw28883step0Labels = raw28883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28883 raw28883Labels permutation346 hz
    mixedMoment B raw28883step0 raw28883step0Labels = mixedMoment B raw28883step1 raw28883step1Labels := by
      have ha : raw28883step1 = (fun i j => raw28883step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28883step1 raw28883step0; decide +kernel
      have hl : raw28883step1Labels = raw28883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28883step0 raw28883step0Labels permutation149 permutation2
    mixedMoment B raw28883step1 raw28883step1Labels = mixedMoment B raw28883step2 raw28883step2Labels := by
      have ha : raw28883step2 = -raw28883step1 := by apply Matrix.ext; change ∀ i j, raw28883step2 i j = -(raw28883step1 i j); unfold raw28883step2 raw28883step1; decide +kernel
      have hl : raw28883step2Labels = raw28883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical28884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28884 raw28884Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw28884 raw28884Labels = mixedMoment B raw28884step0 raw28884step0Labels := by
      have hz : ∀ j, raw28884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28884step0 = (fun i j => raw28884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28884step0 raw28884; decide +kernel
      have hl : raw28884step0Labels = raw28884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28884 raw28884Labels permutation346 hz
    mixedMoment B raw28884step0 raw28884step0Labels = mixedMoment B raw28884step1 raw28884step1Labels := by
      have ha : raw28884step1 = (fun i j => raw28884step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28884step1 raw28884step0; decide +kernel
      have hl : raw28884step1Labels = raw28884step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28884step0 raw28884step0Labels permutation149 permutation2
    mixedMoment B raw28884step1 raw28884step1Labels = mixedMoment B raw28884step2 raw28884step2Labels := by
      have ha : raw28884step2 = -raw28884step1 := by apply Matrix.ext; change ∀ i j, raw28884step2 i j = -(raw28884step1 i j); unfold raw28884step2 raw28884step1; decide +kernel
      have hl : raw28884step2Labels = raw28884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node924 node924Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28965 raw28965Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw28965 raw28965Labels = mixedMoment B raw28965step0 raw28965step0Labels := by
      have hz : ∀ j, raw28965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28965step0 = (fun i j => raw28965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28965step0 raw28965; decide +kernel
      have hl : raw28965step0Labels = raw28965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28965 raw28965Labels permutation346 hz
    mixedMoment B raw28965step0 raw28965step0Labels = mixedMoment B raw28965step1 raw28965step1Labels := by
      have ha : raw28965step1 = (fun i j => raw28965step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28965step1 raw28965step0; decide +kernel
      have hl : raw28965step1Labels = raw28965step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28965step0 raw28965step0Labels permutation151 permutation2
    mixedMoment B raw28965step1 raw28965step1Labels = mixedMoment B raw28965step2 raw28965step2Labels := by
      have ha : raw28965step2 = -raw28965step1 := by apply Matrix.ext; change ∀ i j, raw28965step2 i j = -(raw28965step1 i j); unfold raw28965step2 raw28965step1; decide +kernel
      have hl : raw28965step2Labels = raw28965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical28966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28966 raw28966Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw28966 raw28966Labels = mixedMoment B raw28966step0 raw28966step0Labels := by
      have ha : raw28966step0 = (fun i j => raw28966 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28966step0 raw28966; decide +kernel
      have hl : raw28966step0Labels = raw28966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28966 raw28966Labels permutation158 permutation2
    _ = mixedMoment B node2535 node2535Labels := by rfl

theorem canonical28967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28967 raw28967Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw28967 raw28967Labels = mixedMoment B raw28967step0 raw28967step0Labels := by
      have hz : ∀ j, raw28967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28967step0 = (fun i j => raw28967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28967step0 raw28967; decide +kernel
      have hl : raw28967step0Labels = raw28967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28967 raw28967Labels permutation346 hz
    _ = mixedMoment B node2585 node2585Labels := by rfl

theorem canonical28968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28968 raw28968Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw28968 raw28968Labels = mixedMoment B raw28968step0 raw28968step0Labels := by
      have hz : ∀ j, raw28968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28968step0 = (fun i j => raw28968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28968step0 raw28968; decide +kernel
      have hl : raw28968step0Labels = raw28968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28968 raw28968Labels permutation346 hz
    mixedMoment B raw28968step0 raw28968step0Labels = mixedMoment B raw28968step1 raw28968step1Labels := by
      have ha : raw28968step1 = (fun i j => raw28968step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28968step1 raw28968step0; decide +kernel
      have hl : raw28968step1Labels = raw28968step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28968step0 raw28968step0Labels permutation151 permutation2
    mixedMoment B raw28968step1 raw28968step1Labels = mixedMoment B raw28968step2 raw28968step2Labels := by
      have ha : raw28968step2 = -raw28968step1 := by apply Matrix.ext; change ∀ i j, raw28968step2 i j = -(raw28968step1 i j); unfold raw28968step2 raw28968step1; decide +kernel
      have hl : raw28968step2Labels = raw28968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical28969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28969 raw28969Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw28969 raw28969Labels = mixedMoment B raw28969step0 raw28969step0Labels := by
      have ha : raw28969step0 = (fun i j => raw28969 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28969step0 raw28969; decide +kernel
      have hl : raw28969step0Labels = raw28969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28969 raw28969Labels permutation686 permutation2
    mixedMoment B raw28969step0 raw28969step0Labels = mixedMoment B raw28969step1 raw28969step1Labels := by
      have ha : raw28969step1 = -raw28969step0 := by apply Matrix.ext; change ∀ i j, raw28969step1 i j = -(raw28969step0 i j); unfold raw28969step1 raw28969step0; decide +kernel
      have hl : raw28969step1Labels = raw28969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1921 node1921Labels := by rfl

theorem canonical28970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28970 raw28970Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw28970 raw28970Labels = mixedMoment B raw28970step0 raw28970step0Labels := by
      have hz : ∀ j, raw28970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28970step0 = (fun i j => raw28970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28970step0 raw28970; decide +kernel
      have hl : raw28970step0Labels = raw28970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28970 raw28970Labels permutation346 hz
    mixedMoment B raw28970step0 raw28970step0Labels = mixedMoment B raw28970step1 raw28970step1Labels := by
      have ha : raw28970step1 = (fun i j => raw28970step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28970step1 raw28970step0; decide +kernel
      have hl : raw28970step1Labels = raw28970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28970step0 raw28970step0Labels permutation149 permutation2
    mixedMoment B raw28970step1 raw28970step1Labels = mixedMoment B raw28970step2 raw28970step2Labels := by
      have ha : raw28970step2 = -raw28970step1 := by apply Matrix.ext; change ∀ i j, raw28970step2 i j = -(raw28970step1 i j); unfold raw28970step2 raw28970step1; decide +kernel
      have hl : raw28970step2Labels = raw28970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1945 node1945Labels := by rfl

theorem canonical28971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28971 raw28971Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28971 raw28971Labels = mixedMoment B raw28971step0 raw28971step0Labels := by
      have hz : ∀ j, raw28971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28971step0 = (fun i j => raw28971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28971step0 raw28971; decide +kernel
      have hl : raw28971step0Labels = raw28971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28971 raw28971Labels permutation346 hz
    mixedMoment B raw28971step0 raw28971step0Labels = mixedMoment B raw28971step1 raw28971step1Labels := by
      have ha : raw28971step1 = (fun i j => raw28971step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28971step1 raw28971step0; decide +kernel
      have hl : raw28971step1Labels = raw28971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28971step0 raw28971step0Labels permutation151 permutation2
    mixedMoment B raw28971step1 raw28971step1Labels = mixedMoment B raw28971step2 raw28971step2Labels := by
      have ha : raw28971step2 = -raw28971step1 := by apply Matrix.ext; change ∀ i j, raw28971step2 i j = -(raw28971step1 i j); unfold raw28971step2 raw28971step1; decide +kernel
      have hl : raw28971step2Labels = raw28971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical28972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28972 raw28972Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw28972 raw28972Labels = mixedMoment B raw28972step0 raw28972step0Labels := by
      have hz : ∀ j, raw28972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28972step0 = (fun i j => raw28972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28972step0 raw28972; decide +kernel
      have hl : raw28972step0Labels = raw28972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28972 raw28972Labels permutation346 hz
    mixedMoment B raw28972step0 raw28972step0Labels = mixedMoment B raw28972step1 raw28972step1Labels := by
      have ha : raw28972step1 = (fun i j => raw28972step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28972step1 raw28972step0; decide +kernel
      have hl : raw28972step1Labels = raw28972step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28972step0 raw28972step0Labels permutation151 permutation2
    mixedMoment B raw28972step1 raw28972step1Labels = mixedMoment B raw28972step2 raw28972step2Labels := by
      have ha : raw28972step2 = -raw28972step1 := by apply Matrix.ext; change ∀ i j, raw28972step2 i j = -(raw28972step1 i j); unfold raw28972step2 raw28972step1; decide +kernel
      have hl : raw28972step2Labels = raw28972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical28976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28976 raw28976Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw28976 raw28976Labels = mixedMoment B raw28976step0 raw28976step0Labels := by
      have ha : raw28976step0 = (fun i j => raw28976 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28976step0 raw28976; decide +kernel
      have hl : raw28976step0Labels = raw28976Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28976 raw28976Labels permutation158 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

theorem canonical28977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28977 raw28977Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw28977 raw28977Labels = mixedMoment B raw28977step0 raw28977step0Labels := by
      have hz : ∀ j, raw28977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28977step0 = (fun i j => raw28977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28977step0 raw28977; decide +kernel
      have hl : raw28977step0Labels = raw28977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28977 raw28977Labels permutation346 hz
    _ = mixedMoment B node2584 node2584Labels := by rfl

theorem canonical28978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28978 raw28978Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw28978 raw28978Labels = mixedMoment B raw28978step0 raw28978step0Labels := by
      have hz : ∀ j, raw28978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28978step0 = (fun i j => raw28978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28978step0 raw28978; decide +kernel
      have hl : raw28978step0Labels = raw28978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28978 raw28978Labels permutation346 hz
    _ = mixedMoment B node2538 node2538Labels := by rfl

theorem canonical28985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28985 raw28985Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw28985 raw28985Labels = mixedMoment B raw28985step0 raw28985step0Labels := by
      have ha : raw28985step0 = (fun i j => raw28985 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28985step0 raw28985; decide +kernel
      have hl : raw28985step0Labels = raw28985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28985 raw28985Labels permutation682 permutation2
    mixedMoment B raw28985step0 raw28985step0Labels = mixedMoment B raw28985step1 raw28985step1Labels := by
      have ha : raw28985step1 = -raw28985step0 := by apply Matrix.ext; change ∀ i j, raw28985step1 i j = -(raw28985step0 i j); unfold raw28985step1 raw28985step0; decide +kernel
      have hl : raw28985step1Labels = raw28985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2379 node2379Labels := by rfl

theorem canonical28986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28986 raw28986Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw28986 raw28986Labels = mixedMoment B raw28986step0 raw28986step0Labels := by
      have ha : raw28986step0 = (fun i j => raw28986 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28986step0 raw28986; decide +kernel
      have hl : raw28986step0Labels = raw28986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28986 raw28986Labels permutation686 permutation2
    mixedMoment B raw28986step0 raw28986step0Labels = mixedMoment B raw28986step1 raw28986step1Labels := by
      have ha : raw28986step1 = -raw28986step0 := by apply Matrix.ext; change ∀ i j, raw28986step1 i j = -(raw28986step0 i j); unfold raw28986step1 raw28986step0; decide +kernel
      have hl : raw28986step1Labels = raw28986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical28987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28987 raw28987Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw28987 raw28987Labels = mixedMoment B raw28987step0 raw28987step0Labels := by
      have ha : raw28987step0 = (fun i j => raw28987 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28987step0 raw28987; decide +kernel
      have hl : raw28987step0Labels = raw28987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28987 raw28987Labels permutation680 permutation2
    mixedMoment B raw28987step0 raw28987step0Labels = mixedMoment B raw28987step1 raw28987step1Labels := by
      have ha : raw28987step1 = -raw28987step0 := by apply Matrix.ext; change ∀ i j, raw28987step1 i j = -(raw28987step0 i j); unfold raw28987step1 raw28987step0; decide +kernel
      have hl : raw28987step1Labels = raw28987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical28988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28988 raw28988Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw28988 raw28988Labels = mixedMoment B raw28988step0 raw28988step0Labels := by
      have ha : raw28988step0 = (fun i j => raw28988 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28988step0 raw28988; decide +kernel
      have hl : raw28988step0Labels = raw28988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28988 raw28988Labels permutation682 permutation2
    mixedMoment B raw28988step0 raw28988step0Labels = mixedMoment B raw28988step1 raw28988step1Labels := by
      have ha : raw28988step1 = -raw28988step0 := by apply Matrix.ext; change ∀ i j, raw28988step1 i j = -(raw28988step0 i j); unfold raw28988step1 raw28988step0; decide +kernel
      have hl : raw28988step1Labels = raw28988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical28989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28989 raw28989Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw28989 raw28989Labels = mixedMoment B raw28989step0 raw28989step0Labels := by
      have ha : raw28989step0 = (fun i j => raw28989 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28989step0 raw28989; decide +kernel
      have hl : raw28989step0Labels = raw28989Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28989 raw28989Labels permutation682 permutation2
    mixedMoment B raw28989step0 raw28989step0Labels = mixedMoment B raw28989step1 raw28989step1Labels := by
      have ha : raw28989step1 = -raw28989step0 := by apply Matrix.ext; change ∀ i j, raw28989step1 i j = -(raw28989step0 i j); unfold raw28989step1 raw28989step0; decide +kernel
      have hl : raw28989step1Labels = raw28989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3757 node3757Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10642 raw10642Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10642 raw10642Labels = mixedMoment B raw10642step0 raw10642step0Labels := by
      have hz : ∀ j, raw10642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10642step0 = (fun i j => raw10642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10642step0 raw10642; decide +kernel
      have hl : raw10642step0Labels = raw10642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10642 raw10642Labels permutation346 hz
    mixedMoment B raw10642step0 raw10642step0Labels = mixedMoment B raw10642step1 raw10642step1Labels := by
      have ha : raw10642step1 = (fun i j => raw10642step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10642step1 raw10642step0; decide +kernel
      have hl : raw10642step1Labels = raw10642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10642step0 raw10642step0Labels permutation149 permutation7
    mixedMoment B raw10642step1 raw10642step1Labels = mixedMoment B raw10642step2 raw10642step2Labels := by
      have ha : raw10642step2 = raw10642step1 := by apply Matrix.ext; unfold raw10642step2 raw10642step1; decide +kernel
      have hl : raw10642step1Labels = labelEmbedding1 ∘ raw10642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10642step1 raw10642step1Labels raw10642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10653 raw10653Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10653 raw10653Labels = mixedMoment B raw10653step0 raw10653step0Labels := by
      have ha : raw10653step0 = (fun i j => raw10653 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10653step0 raw10653; decide +kernel
      have hl : raw10653step0Labels = raw10653Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10653 raw10653Labels permutation644 permutation7
    mixedMoment B raw10653step0 raw10653step0Labels = mixedMoment B raw10653step1 raw10653step1Labels := by
      have ha : raw10653step1 = raw10653step0 := by apply Matrix.ext; unfold raw10653step1 raw10653step0; decide +kernel
      have hl : raw10653step0Labels = labelEmbedding1 ∘ raw10653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10653step0 raw10653step0Labels raw10653step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical10658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10658 raw10658Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10658 raw10658Labels = mixedMoment B raw10658step0 raw10658step0Labels := by
      have hz : ∀ j, raw10658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10658step0 = (fun i j => raw10658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10658step0 raw10658; decide +kernel
      have hl : raw10658step0Labels = raw10658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10658 raw10658Labels permutation346 hz
    mixedMoment B raw10658step0 raw10658step0Labels = mixedMoment B raw10658step1 raw10658step1Labels := by
      have ha : raw10658step1 = (fun i j => raw10658step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10658step1 raw10658step0; decide +kernel
      have hl : raw10658step1Labels = raw10658step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10658step0 raw10658step0Labels permutation149 permutation7
    mixedMoment B raw10658step1 raw10658step1Labels = mixedMoment B raw10658step2 raw10658step2Labels := by
      have ha : raw10658step2 = raw10658step1 := by apply Matrix.ext; unfold raw10658step2 raw10658step1; decide +kernel
      have hl : raw10658step1Labels = labelEmbedding1 ∘ raw10658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10658step1 raw10658step1Labels raw10658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical10663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10663 raw10663Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10663 raw10663Labels = mixedMoment B raw10663step0 raw10663step0Labels := by
      have hz : ∀ j, raw10663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10663step0 = (fun i j => raw10663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10663step0 raw10663; decide +kernel
      have hl : raw10663step0Labels = raw10663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10663 raw10663Labels permutation346 hz
    mixedMoment B raw10663step0 raw10663step0Labels = mixedMoment B raw10663step1 raw10663step1Labels := by
      have ha : raw10663step1 = (fun i j => raw10663step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10663step1 raw10663step0; decide +kernel
      have hl : raw10663step1Labels = raw10663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10663step0 raw10663step0Labels permutation149 permutation7
    mixedMoment B raw10663step1 raw10663step1Labels = mixedMoment B raw10663step2 raw10663step2Labels := by
      have ha : raw10663step2 = raw10663step1 := by apply Matrix.ext; unfold raw10663step2 raw10663step1; decide +kernel
      have hl : raw10663step1Labels = labelEmbedding1 ∘ raw10663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10663step1 raw10663step1Labels raw10663step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical10667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10667 raw10667Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw10667 raw10667Labels = mixedMoment B raw10667step0 raw10667step0Labels := by
      have hz : ∀ j, raw10667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10667step0 = (fun i j => raw10667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10667step0 raw10667; decide +kernel
      have hl : raw10667step0Labels = raw10667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667 raw10667Labels permutation346 hz
    mixedMoment B raw10667step0 raw10667step0Labels = mixedMoment B raw10667step1 raw10667step1Labels := by
      have hz : ∀ j, raw10667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10667step1 = (fun i j => raw10667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10667step1 raw10667step0; decide +kernel
      have hl : raw10667step1Labels = raw10667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667step0 raw10667step0Labels permutation56 hz
    mixedMoment B raw10667step1 raw10667step1Labels = mixedMoment B raw10667step2 raw10667step2Labels := by
      have ha : raw10667step2 = (fun i j => raw10667step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10667step2 raw10667step1; decide +kernel
      have hl : raw10667step2Labels = raw10667step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10667step1 raw10667step1Labels permutation31 permutation7
    mixedMoment B raw10667step2 raw10667step2Labels = mixedMoment B raw10667step3 raw10667step3Labels := by
      have ha : raw10667step3 = raw10667step2 := by apply Matrix.ext; unfold raw10667step3 raw10667step2; decide +kernel
      have hl : raw10667step2Labels = labelEmbedding1 ∘ raw10667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10667step2 raw10667step2Labels raw10667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical10669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10669 raw10669Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10669 raw10669Labels = mixedMoment B raw10669step0 raw10669step0Labels := by
      have hz : ∀ j, raw10669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10669step0 = (fun i j => raw10669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10669step0 raw10669; decide +kernel
      have hl : raw10669step0Labels = raw10669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10669 raw10669Labels permutation265 hz
    mixedMoment B raw10669step0 raw10669step0Labels = mixedMoment B raw10669step1 raw10669step1Labels := by
      have ha : raw10669step1 = (fun i j => raw10669step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10669step1 raw10669step0; decide +kernel
      have hl : raw10669step1Labels = raw10669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10669step0 raw10669step0Labels permutation149 permutation7
    mixedMoment B raw10669step1 raw10669step1Labels = mixedMoment B raw10669step2 raw10669step2Labels := by
      have ha : raw10669step2 = raw10669step1 := by apply Matrix.ext; unfold raw10669step2 raw10669step1; decide +kernel
      have hl : raw10669step1Labels = labelEmbedding1 ∘ raw10669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10669step1 raw10669step1Labels raw10669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical10670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10670 raw10670Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw10670 raw10670Labels = mixedMoment B raw10670step0 raw10670step0Labels := by
      have hz : ∀ j, raw10670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10670step0 = (fun i j => raw10670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10670step0 raw10670; decide +kernel
      have hl : raw10670step0Labels = raw10670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670 raw10670Labels permutation346 hz
    mixedMoment B raw10670step0 raw10670step0Labels = mixedMoment B raw10670step1 raw10670step1Labels := by
      have hz : ∀ j, raw10670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10670step1 = (fun i j => raw10670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10670step1 raw10670step0; decide +kernel
      have hl : raw10670step1Labels = raw10670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670step0 raw10670step0Labels permutation56 hz
    mixedMoment B raw10670step1 raw10670step1Labels = mixedMoment B raw10670step2 raw10670step2Labels := by
      have ha : raw10670step2 = (fun i j => raw10670step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10670step2 raw10670step1; decide +kernel
      have hl : raw10670step2Labels = raw10670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10670step1 raw10670step1Labels permutation31 permutation7
    mixedMoment B raw10670step2 raw10670step2Labels = mixedMoment B raw10670step3 raw10670step3Labels := by
      have ha : raw10670step3 = raw10670step2 := by apply Matrix.ext; unfold raw10670step3 raw10670step2; decide +kernel
      have hl : raw10670step2Labels = labelEmbedding1 ∘ raw10670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10670step2 raw10670step2Labels raw10670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical10671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10671 raw10671Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10671 raw10671Labels = mixedMoment B raw10671step0 raw10671step0Labels := by
      have hz : ∀ j, raw10671 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10671step0 = (fun i j => raw10671 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10671step0 raw10671; decide +kernel
      have hl : raw10671step0Labels = raw10671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671 raw10671Labels permutation520 hz
    mixedMoment B raw10671step0 raw10671step0Labels = mixedMoment B raw10671step1 raw10671step1Labels := by
      have hz : ∀ j, raw10671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10671step1 = (fun i j => raw10671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10671step1 raw10671step0; decide +kernel
      have hl : raw10671step1Labels = raw10671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step0 raw10671step0Labels permutation80 hz
    mixedMoment B raw10671step1 raw10671step1Labels = mixedMoment B raw10671step2 raw10671step2Labels := by
      have hz : ∀ j, raw10671step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10671step2 = (fun i j => raw10671step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10671step2 raw10671step1; decide +kernel
      have hl : raw10671step2Labels = raw10671step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step1 raw10671step1Labels permutation14 hz
    mixedMoment B raw10671step2 raw10671step2Labels = mixedMoment B raw10671step3 raw10671step3Labels := by
      have ha : raw10671step3 = (fun i j => raw10671step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10671step3 raw10671step2; decide +kernel
      have hl : raw10671step3Labels = raw10671step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10671step2 raw10671step2Labels permutation7 permutation7
    mixedMoment B raw10671step3 raw10671step3Labels = mixedMoment B raw10671step4 raw10671step4Labels := by
      have ha : raw10671step4 = raw10671step3 := by apply Matrix.ext; unfold raw10671step4 raw10671step3; decide +kernel
      have hl : raw10671step3Labels = labelEmbedding1 ∘ raw10671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10671step3 raw10671step3Labels raw10671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node904 node904Labels = 0 := by
  exact mixedMoment_alpha B hF node904 node904Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node904 node904Labels = Sparse.eval nodeValue904 (mixedVector B) := by
  simpa only [nodeValue904, Sparse.eval_nil] using zero904 B _hB _hF

theorem sound912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node912 node912Labels = Sparse.eval nodeValue912 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 912) = mixedMoment B node912 node912Labels := rfl
  simpa [nodeValue912, Sparse.eval] using hc.symm

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

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

theorem sound1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1111 node1111Labels = Sparse.eval nodeValue1111 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1111) = mixedMoment B node1111 node1111Labels := rfl
  simpa [nodeValue1111, Sparse.eval] using hc.symm

theorem sound1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1119 node1119Labels = Sparse.eval nodeValue1119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1119) = mixedMoment B node1119 node1119Labels := rfl
  simpa [nodeValue1119, Sparse.eval] using hc.symm

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1147 node1147Labels = Sparse.eval nodeValue1147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1147) = mixedMoment B node1147 node1147Labels := rfl
  simpa [nodeValue1147, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = 0 := by
  exact mixedMoment_alpha B hF node1663 node1663Labels 1 permutation485
    (by decide +kernel)

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

theorem sound1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = Sparse.eval nodeValue1663 (mixedVector B) := by
  simpa only [nodeValue1663, Sparse.eval_nil] using zero1663 B _hB _hF

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

theorem sound1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1672 node1672Labels = Sparse.eval nodeValue1672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1672) = mixedMoment B node1672 node1672Labels := rfl
  simpa [nodeValue1672, Sparse.eval] using hc.symm

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1789 node1789Labels = Sparse.eval nodeValue1789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1789) = mixedMoment B node1789 node1789Labels := rfl
  simpa [nodeValue1789, Sparse.eval] using hc.symm

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

theorem sound1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1795 node1795Labels = Sparse.eval nodeValue1795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1795) = mixedMoment B node1795 node1795Labels := rfl
  simpa [nodeValue1795, Sparse.eval] using hc.symm

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1945 node1945Labels = 0 := by
  exact mixedMoment_order_one B hB node1945 node1945Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1924 node1924Labels = Sparse.eval nodeValue1924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1924) = mixedMoment B node1924 node1924Labels := rfl
  simpa [nodeValue1924, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1945 node1945Labels = Sparse.eval nodeValue1945 (mixedVector B) := by
  simpa only [nodeValue1945, Sparse.eval_nil] using zero1945 B _hB _hF

theorem sound1955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1955 node1955Labels = Sparse.eval nodeValue1955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1955) = mixedMoment B node1955 node1955Labels := rfl
  simpa [nodeValue1955, Sparse.eval] using hc.symm

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

theorem sound1972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1972 node1972Labels = Sparse.eval nodeValue1972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1972) = mixedMoment B node1972 node1972Labels := rfl
  simpa [nodeValue1972, Sparse.eval] using hc.symm

theorem sound1978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1978 node1978Labels = Sparse.eval nodeValue1978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1978) = mixedMoment B node1978 node1978Labels := rfl
  simpa [nodeValue1978, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = 0 := by
  exact mixedMoment_order_one B hB node2053 node2053Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = Sparse.eval nodeValue2053 (mixedVector B) := by
  simpa only [nodeValue2053, Sparse.eval_nil] using zero2053 B _hB _hF

theorem sound2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = Sparse.eval nodeValue2060 (mixedVector B) := by
  simpa only [nodeValue2060, Sparse.eval_nil] using zero2060 B _hB _hF

end MUB6.Certificate.MixedSemantics

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

theorem sound2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2140 node2140Labels = Sparse.eval nodeValue2140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2140) = mixedMoment B node2140 node2140Labels := rfl
  simpa [nodeValue2140, Sparse.eval] using hc.symm

theorem sound2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2149 node2149Labels = Sparse.eval nodeValue2149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2149) = mixedMoment B node2149 node2149Labels := rfl
  simpa [nodeValue2149, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2155 node2155Labels = Sparse.eval nodeValue2155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2155) = mixedMoment B node2155 node2155Labels := rfl
  simpa [nodeValue2155, Sparse.eval] using hc.symm

theorem sound2172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2172 node2172Labels = Sparse.eval nodeValue2172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2172) = mixedMoment B node2172 node2172Labels := rfl
  simpa [nodeValue2172, Sparse.eval] using hc.symm

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2176 node2176Labels = Sparse.eval nodeValue2176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2176) = mixedMoment B node2176 node2176Labels := rfl
  simpa [nodeValue2176, Sparse.eval] using hc.symm

theorem sound2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2189 node2189Labels = Sparse.eval nodeValue2189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2189) = mixedMoment B node2189 node2189Labels := rfl
  simpa [nodeValue2189, Sparse.eval] using hc.symm

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2200 node2200Labels = Sparse.eval nodeValue2200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2200) = mixedMoment B node2200 node2200Labels := rfl
  simpa [nodeValue2200, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2319 node2319Labels = 0 := by
  exact mixedMoment_alpha B hF node2319 node2319Labels 1 permutation152
    (by decide +kernel)

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

theorem sound2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2319 node2319Labels = Sparse.eval nodeValue2319 (mixedVector B) := by
  simpa only [nodeValue2319, Sparse.eval_nil] using zero2319 B _hB _hF

theorem sound2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2325 node2325Labels = Sparse.eval nodeValue2325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2325) = mixedMoment B node2325 node2325Labels := rfl
  simpa [nodeValue2325, Sparse.eval] using hc.symm

theorem sound2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2334 node2334Labels = Sparse.eval nodeValue2334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2334) = mixedMoment B node2334 node2334Labels := rfl
  simpa [nodeValue2334, Sparse.eval] using hc.symm

theorem sound2347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2347 node2347Labels = Sparse.eval nodeValue2347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2347) = mixedMoment B node2347 node2347Labels := rfl
  simpa [nodeValue2347, Sparse.eval] using hc.symm

theorem sound2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2355 node2355Labels = Sparse.eval nodeValue2355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2355) = mixedMoment B node2355 node2355Labels := rfl
  simpa [nodeValue2355, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = 0 := by
  exact mixedMoment_alpha B hF node2377 node2377Labels 1 permutation200
    (by decide +kernel)

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

theorem sound2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2377 node2377Labels = Sparse.eval nodeValue2377 (mixedVector B) := by
  simpa only [nodeValue2377, Sparse.eval_nil] using zero2377 B _hB _hF

theorem sound2379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2379 node2379Labels = Sparse.eval nodeValue2379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2379) = mixedMoment B node2379 node2379Labels := rfl
  simpa [nodeValue2379, Sparse.eval] using hc.symm

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2391 node2391Labels = Sparse.eval nodeValue2391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2391) = mixedMoment B node2391 node2391Labels := rfl
  simpa [nodeValue2391, Sparse.eval] using hc.symm

theorem sound2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2425 node2425Labels = Sparse.eval nodeValue2425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2425) = mixedMoment B node2425 node2425Labels := rfl
  simpa [nodeValue2425, Sparse.eval] using hc.symm

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

theorem sound2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2436 node2436Labels = Sparse.eval nodeValue2436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2436) = mixedMoment B node2436 node2436Labels := rfl
  simpa [nodeValue2436, Sparse.eval] using hc.symm

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2511 node2511Labels = 0 := by
  exact mixedMoment_order_one B hB node2511 node2511Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = 0 := by
  exact mixedMoment_order_one B hB node2517 node2517Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = 0 := by
  exact mixedMoment_alpha B hF node2552 node2552Labels 1 permutation161
    (by decide +kernel)

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

theorem sound2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2511 node2511Labels = Sparse.eval nodeValue2511 (mixedVector B) := by
  simpa only [nodeValue2511, Sparse.eval_nil] using zero2511 B _hB _hF

theorem sound2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = Sparse.eval nodeValue2517 (mixedVector B) := by
  simpa only [nodeValue2517, Sparse.eval_nil] using zero2517 B _hB _hF

theorem sound2534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2534 node2534Labels = Sparse.eval nodeValue2534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2534) = mixedMoment B node2534 node2534Labels := rfl
  simpa [nodeValue2534, Sparse.eval] using hc.symm

theorem sound2535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2535 node2535Labels = Sparse.eval nodeValue2535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2535) = mixedMoment B node2535 node2535Labels := rfl
  simpa [nodeValue2535, Sparse.eval] using hc.symm

theorem sound2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2538 node2538Labels = Sparse.eval nodeValue2538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2538) = mixedMoment B node2538 node2538Labels := rfl
  simpa [nodeValue2538, Sparse.eval] using hc.symm

theorem sound2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2539 node2539Labels = Sparse.eval nodeValue2539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2539) = mixedMoment B node2539 node2539Labels := rfl
  simpa [nodeValue2539, Sparse.eval] using hc.symm

theorem sound2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = Sparse.eval nodeValue2552 (mixedVector B) := by
  simpa only [nodeValue2552, Sparse.eval_nil] using zero2552 B _hB _hF

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

theorem sound2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2584 node2584Labels = Sparse.eval nodeValue2584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2584) = mixedMoment B node2584 node2584Labels := rfl
  simpa [nodeValue2584, Sparse.eval] using hc.symm

theorem sound2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2585 node2585Labels = Sparse.eval nodeValue2585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2585) = mixedMoment B node2585 node2585Labels := rfl
  simpa [nodeValue2585, Sparse.eval] using hc.symm

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

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = 0 := by
  exact mixedMoment_alpha B hF node2693 node2693Labels 1 permutation213
    (by decide +kernel)

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

theorem sound2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = Sparse.eval nodeValue2693 (mixedVector B) := by
  simpa only [nodeValue2693, Sparse.eval_nil] using zero2693 B _hB _hF

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

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

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2033 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2033 + difference 0 1) (sourceB2033 + difference 1 0) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2033 + difference 0 1) (sourceB2033 + difference 1 0) sourceC2033) = raw28750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28750; decide +kernel
    rw [ha]
    exact (canonical28750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2033 + difference 1 1) (sourceB2033 + difference 1 1) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2033 + difference 1 1) (sourceB2033 + difference 1 1) sourceC2033) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2033 + difference 2 1) (sourceB2033 + difference 1 2) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2033 + difference 2 1) (sourceB2033 + difference 1 2) sourceC2033) = raw28751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28751; decide +kernel
    rw [ha]
    exact (canonical28751 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2033 + difference 3 1) (sourceB2033 + difference 1 3) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2033 + difference 3 1) (sourceB2033 + difference 1 3) sourceC2033) = raw28752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28752; decide +kernel
    rw [ha]
    exact (canonical28752 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2033 + difference 4 1) (sourceB2033 + difference 1 4) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2033 + difference 4 1) (sourceB2033 + difference 1 4) sourceC2033) = raw28753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28753; decide +kernel
    rw [ha]
    exact (canonical28753 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2033 + difference 5 1) (sourceB2033 + difference 1 5) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA2033 + difference 5 1) (sourceB2033 + difference 1 5) sourceC2033) = raw28754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28754; decide +kernel
    rw [ha]
    exact (canonical28754 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2033 + sourceB2033) sourceC2033) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2033 + sourceB2033) sourceC2033) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2033 sourceB2033 sourceC2033 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2033 sourceB2033 sourceC2033
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2033, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2034 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2034 + difference 0 2) (sourceB2034 + difference 2 0) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA2034 + difference 0 2) (sourceB2034 + difference 2 0) sourceC2034) = raw28755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28755; decide +kernel
    rw [ha]
    exact (canonical28755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2034 + difference 1 2) (sourceB2034 + difference 2 1) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2034 + difference 1 2) (sourceB2034 + difference 2 1) sourceC2034) = raw28756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28756; decide +kernel
    rw [ha]
    exact (canonical28756 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2034 + difference 2 2) (sourceB2034 + difference 2 2) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2034 + difference 2 2) (sourceB2034 + difference 2 2) sourceC2034) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2034 + difference 3 2) (sourceB2034 + difference 2 3) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2436) := by
    have ha : (tripleCharges (sourceA2034 + difference 3 2) (sourceB2034 + difference 2 3) sourceC2034) = raw28757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28757; decide +kernel
    rw [ha]
    exact (canonical28757 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2034 + difference 4 2) (sourceB2034 + difference 2 4) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2319) := by
    have ha : (tripleCharges (sourceA2034 + difference 4 2) (sourceB2034 + difference 2 4) sourceC2034) = raw28758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28758; decide +kernel
    rw [ha]
    exact (canonical28758 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2034 + difference 5 2) (sourceB2034 + difference 2 5) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA2034 + difference 5 2) (sourceB2034 + difference 2 5) sourceC2034) = raw28759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28759; decide +kernel
    rw [ha]
    exact (canonical28759 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2034 + sourceB2034) sourceC2034) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2034 + sourceB2034) sourceC2034) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2034 sourceB2034 sourceC2034 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2034 sourceB2034 sourceC2034
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2034, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2035 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2035 + difference 0 3) (sourceB2035 + difference 3 0) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2511) := by
    have ha : (tripleCharges (sourceA2035 + difference 0 3) (sourceB2035 + difference 3 0) sourceC2035) = raw28760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28760; decide +kernel
    rw [ha]
    exact (canonical28760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2035 + difference 1 3) (sourceB2035 + difference 3 1) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA2035 + difference 1 3) (sourceB2035 + difference 3 1) sourceC2035) = raw20744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw20744; decide +kernel
    rw [ha]
    exact (canonical20744 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2035 + difference 2 3) (sourceB2035 + difference 3 2) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA2035 + difference 2 3) (sourceB2035 + difference 3 2) sourceC2035) = raw28761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28761; decide +kernel
    rw [ha]
    exact (canonical28761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2035 + difference 3 3) (sourceB2035 + difference 3 3) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2035 + difference 3 3) (sourceB2035 + difference 3 3) sourceC2035) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2035 + difference 4 3) (sourceB2035 + difference 3 4) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2035 + difference 4 3) (sourceB2035 + difference 3 4) sourceC2035) = raw28762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28762; decide +kernel
    rw [ha]
    exact (canonical28762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2035 + difference 5 3) (sourceB2035 + difference 3 5) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA2035 + difference 5 3) (sourceB2035 + difference 3 5) sourceC2035) = raw28763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28763; decide +kernel
    rw [ha]
    exact (canonical28763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2035 + sourceB2035) sourceC2035) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2035 + sourceB2035) sourceC2035) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2035 sourceB2035 sourceC2035 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2035 sourceB2035 sourceC2035
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2035, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2041 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 1) (sourceB2041 + difference 1 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 1) (sourceB2041 + difference 1 0) sourceC2041) = raw28852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28852; decide +kernel
    rw [ha]
    exact (canonical28852 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 2) (sourceB2041 + difference 2 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 2) (sourceB2041 + difference 2 0) sourceC2041) = raw28853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28853; decide +kernel
    rw [ha]
    exact (canonical28853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 3) (sourceB2041 + difference 3 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 3) (sourceB2041 + difference 3 0) sourceC2041) = raw28854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28854; decide +kernel
    rw [ha]
    exact (canonical28854 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 4) (sourceB2041 + difference 4 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 4) (sourceB2041 + difference 4 0) sourceC2041) = raw28855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28855; decide +kernel
    rw [ha]
    exact (canonical28855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 5) (sourceB2041 + difference 5 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 5) (sourceB2041 + difference 5 0) sourceC2041) = raw10642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10642; decide +kernel
    rw [ha]
    exact (canonical10642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 0) (sourceB2041 + difference 0 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 0) (sourceB2041 + difference 0 1) sourceC2041) = raw10667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10667; decide +kernel
    rw [ha]
    exact (canonical10667 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 2) (sourceB2041 + difference 2 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 2) (sourceB2041 + difference 2 1) sourceC2041) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 3) (sourceB2041 + difference 3 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 3) (sourceB2041 + difference 3 1) sourceC2041) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 4) (sourceB2041 + difference 4 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 4) (sourceB2041 + difference 4 1) sourceC2041) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 5) (sourceB2041 + difference 5 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 5) (sourceB2041 + difference 5 1) sourceC2041) = raw20888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20888; decide +kernel
    rw [ha]
    exact (canonical20888 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 0) (sourceB2041 + difference 0 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 0) (sourceB2041 + difference 0 2) sourceC2041) = raw20894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20894; decide +kernel
    rw [ha]
    exact (canonical20894 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 1) (sourceB2041 + difference 1 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 1) (sourceB2041 + difference 1 2) sourceC2041) = raw28856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28856; decide +kernel
    rw [ha]
    exact (canonical28856 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 3) (sourceB2041 + difference 3 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 3) (sourceB2041 + difference 3 2) sourceC2041) = raw28857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28857; decide +kernel
    rw [ha]
    exact (canonical28857 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 4) (sourceB2041 + difference 4 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 4) (sourceB2041 + difference 4 2) sourceC2041) = raw28858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28858; decide +kernel
    rw [ha]
    exact (canonical28858 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 5) (sourceB2041 + difference 5 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 5) (sourceB2041 + difference 5 2) sourceC2041) = raw10653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10653; decide +kernel
    rw [ha]
    exact (canonical10653 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 0) (sourceB2041 + difference 0 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 0) (sourceB2041 + difference 0 3) sourceC2041) = raw20898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20898; decide +kernel
    rw [ha]
    exact (canonical20898 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 1) (sourceB2041 + difference 1 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 1) (sourceB2041 + difference 1 3) sourceC2041) = raw28859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28859; decide +kernel
    rw [ha]
    exact (canonical28859 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 2) (sourceB2041 + difference 2 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 2) (sourceB2041 + difference 2 3) sourceC2041) = raw28860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28860; decide +kernel
    rw [ha]
    exact (canonical28860 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 4) (sourceB2041 + difference 4 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 4) (sourceB2041 + difference 4 3) sourceC2041) = raw28861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28861; decide +kernel
    rw [ha]
    exact (canonical28861 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 5) (sourceB2041 + difference 5 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 5) (sourceB2041 + difference 5 3) sourceC2041) = raw10658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10658; decide +kernel
    rw [ha]
    exact (canonical10658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 0) (sourceB2041 + difference 0 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 0) (sourceB2041 + difference 0 4) sourceC2041) = raw20902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20902; decide +kernel
    rw [ha]
    exact (canonical20902 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 1) (sourceB2041 + difference 1 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 1) (sourceB2041 + difference 1 4) sourceC2041) = raw28862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28862; decide +kernel
    rw [ha]
    exact (canonical28862 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 2) (sourceB2041 + difference 2 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 2) (sourceB2041 + difference 2 4) sourceC2041) = raw28863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28863; decide +kernel
    rw [ha]
    exact (canonical28863 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 3) (sourceB2041 + difference 3 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 3) (sourceB2041 + difference 3 4) sourceC2041) = raw28864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28864; decide +kernel
    rw [ha]
    exact (canonical28864 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 5) (sourceB2041 + difference 5 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 5) (sourceB2041 + difference 5 4) sourceC2041) = raw10663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10663; decide +kernel
    rw [ha]
    exact (canonical10663 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 0) (sourceB2041 + difference 0 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 0) (sourceB2041 + difference 0 5) sourceC2041) = raw20906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20906; decide +kernel
    rw [ha]
    exact (canonical20906 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 1) (sourceB2041 + difference 1 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 1) (sourceB2041 + difference 1 5) sourceC2041) = raw28865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28865; decide +kernel
    rw [ha]
    exact (canonical28865 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 2) (sourceB2041 + difference 2 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 2) (sourceB2041 + difference 2 5) sourceC2041) = raw28866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28866; decide +kernel
    rw [ha]
    exact (canonical28866 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 3) (sourceB2041 + difference 3 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 3) (sourceB2041 + difference 3 5) sourceC2041) = raw28867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28867; decide +kernel
    rw [ha]
    exact (canonical28867 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 4) (sourceB2041 + difference 4 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 4) (sourceB2041 + difference 4 5) sourceC2041) = raw28868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28868; decide +kernel
    rw [ha]
    exact (canonical28868 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2041 sourceB2041 sourceC2041
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2041, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2042 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2042 + difference 0 1) (sourceB2042 + difference 1 0) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2042 + difference 0 1) (sourceB2042 + difference 1 0) sourceC2042) = raw28869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28869; decide +kernel
    rw [ha]
    exact (canonical28869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2042 + difference 1 1) (sourceB2042 + difference 1 1) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2042 + difference 1 1) (sourceB2042 + difference 1 1) sourceC2042) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2042 + difference 2 1) (sourceB2042 + difference 1 2) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1955) := by
    have ha : (tripleCharges (sourceA2042 + difference 2 1) (sourceB2042 + difference 1 2) sourceC2042) = raw28870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28870; decide +kernel
    rw [ha]
    exact (canonical28870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2042 + difference 3 1) (sourceB2042 + difference 1 3) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2042 + difference 3 1) (sourceB2042 + difference 1 3) sourceC2042) = raw28871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28871; decide +kernel
    rw [ha]
    exact (canonical28871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2042 + difference 4 1) (sourceB2042 + difference 1 4) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1795) := by
    have ha : (tripleCharges (sourceA2042 + difference 4 1) (sourceB2042 + difference 1 4) sourceC2042) = raw28872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28872; decide +kernel
    rw [ha]
    exact (canonical28872 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2042 + difference 5 1) (sourceB2042 + difference 1 5) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 912) := by
    have ha : (tripleCharges (sourceA2042 + difference 5 1) (sourceB2042 + difference 1 5) sourceC2042) = raw28873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28873; decide +kernel
    rw [ha]
    exact (canonical28873 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2042 + sourceB2042) sourceC2042) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2042 + sourceB2042) sourceC2042) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2042 sourceB2042 sourceC2042 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2042 sourceB2042 sourceC2042
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2042, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2043 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 0) (sourceB2043 + difference 0 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 0) (sourceB2043 + difference 0 2) sourceC2043) = raw20922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw20922; decide +kernel
    rw [ha]
    exact (canonical20922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 1) (sourceB2043 + difference 1 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1955) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 1) (sourceB2043 + difference 1 2) sourceC2043) = raw28870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28870; decide +kernel
    rw [ha]
    exact (canonical28870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 2) (sourceB2043 + difference 2 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 2) (sourceB2043 + difference 2 2) sourceC2043) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 3) (sourceB2043 + difference 3 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 3) (sourceB2043 + difference 3 2) sourceC2043) = raw28874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28874; decide +kernel
    rw [ha]
    exact (canonical28874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 4) (sourceB2043 + difference 4 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 4) (sourceB2043 + difference 4 2) sourceC2043) = raw28875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28875; decide +kernel
    rw [ha]
    exact (canonical28875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 5) (sourceB2043 + difference 5 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 5) (sourceB2043 + difference 5 2) sourceC2043) = raw28876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28876; decide +kernel
    rw [ha]
    exact (canonical28876 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2043 + sourceB2043) sourceC2043) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2043 + sourceB2043) sourceC2043) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2043 sourceB2043 sourceC2043 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2043 sourceB2043 sourceC2043
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2043, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2044 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2044 + difference 0 2) (sourceB2044 + difference 2 0) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA2044 + difference 0 2) (sourceB2044 + difference 2 0) sourceC2044) = raw28877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28877; decide +kernel
    rw [ha]
    exact (canonical28877 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2044 + difference 1 2) (sourceB2044 + difference 2 1) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2044 + difference 1 2) (sourceB2044 + difference 2 1) sourceC2044) = raw28878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28878; decide +kernel
    rw [ha]
    exact (canonical28878 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2044 + difference 2 2) (sourceB2044 + difference 2 2) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2044 + difference 2 2) (sourceB2044 + difference 2 2) sourceC2044) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2044 + difference 3 2) (sourceB2044 + difference 2 3) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2044 + difference 3 2) (sourceB2044 + difference 2 3) sourceC2044) = raw28879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28879; decide +kernel
    rw [ha]
    exact (canonical28879 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2044 + difference 4 2) (sourceB2044 + difference 2 4) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1789) := by
    have ha : (tripleCharges (sourceA2044 + difference 4 2) (sourceB2044 + difference 2 4) sourceC2044) = raw28880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28880; decide +kernel
    rw [ha]
    exact (canonical28880 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2044 + difference 5 2) (sourceB2044 + difference 2 5) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA2044 + difference 5 2) (sourceB2044 + difference 2 5) sourceC2044) = raw28881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28881; decide +kernel
    rw [ha]
    exact (canonical28881 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2044 + sourceB2044) sourceC2044) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2044 + sourceB2044) sourceC2044) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2044 sourceB2044 sourceC2044 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2044 sourceB2044 sourceC2044
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2044, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2045 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2045 + difference 0 3) (sourceB2045 + difference 3 0) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA2045 + difference 0 3) (sourceB2045 + difference 3 0) sourceC2045) = raw28882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28882; decide +kernel
    rw [ha]
    exact (canonical28882 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2045 + difference 1 3) (sourceB2045 + difference 3 1) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA2045 + difference 1 3) (sourceB2045 + difference 3 1) sourceC2045) = raw20926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw20926; decide +kernel
    rw [ha]
    exact (canonical20926 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2045 + difference 2 3) (sourceB2045 + difference 3 2) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2045 + difference 2 3) (sourceB2045 + difference 3 2) sourceC2045) = raw28874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28874; decide +kernel
    rw [ha]
    exact (canonical28874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2045 + difference 3 3) (sourceB2045 + difference 3 3) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2045 + difference 3 3) (sourceB2045 + difference 3 3) sourceC2045) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2045 + difference 4 3) (sourceB2045 + difference 3 4) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2045 + difference 4 3) (sourceB2045 + difference 3 4) sourceC2045) = raw28883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28883; decide +kernel
    rw [ha]
    exact (canonical28883 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2045 + difference 5 3) (sourceB2045 + difference 3 5) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA2045 + difference 5 3) (sourceB2045 + difference 3 5) sourceC2045) = raw28884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28884; decide +kernel
    rw [ha]
    exact (canonical28884 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2045 + sourceB2045) sourceC2045) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2045 + sourceB2045) sourceC2045) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2045 sourceB2045 sourceC2045 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2045 sourceB2045 sourceC2045
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2045, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2051 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2051 + difference 0 5) (sourceB2051 + difference 5 0) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2051 + difference 0 5) (sourceB2051 + difference 5 0) sourceC2051) = raw28965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28965; decide +kernel
    rw [ha]
    exact (canonical28965 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2051 + difference 1 5) (sourceB2051 + difference 5 1) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2051 + difference 1 5) (sourceB2051 + difference 5 1) sourceC2051) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2051 + difference 2 5) (sourceB2051 + difference 5 2) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA2051 + difference 2 5) (sourceB2051 + difference 5 2) sourceC2051) = raw28966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28966; decide +kernel
    rw [ha]
    exact (canonical28966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2051 + difference 3 5) (sourceB2051 + difference 5 3) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA2051 + difference 3 5) (sourceB2051 + difference 5 3) sourceC2051) = raw28967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw28967; decide +kernel
    rw [ha]
    exact (canonical28967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2051 + difference 4 5) (sourceB2051 + difference 5 4) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA2051 + difference 4 5) (sourceB2051 + difference 5 4) sourceC2051) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2051 + difference 5 5) (sourceB2051 + difference 5 5) sourceC2051) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA2051 + difference 5 5) (sourceB2051 + difference 5 5) sourceC2051) = raw21003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2051 sourceB2051 sourceC2051 difference raw21003; decide +kernel
    rw [ha]
    exact (canonical21003 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2051 + sourceB2051) sourceC2051) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2051 + sourceB2051) sourceC2051) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA2051 sourceB2051 sourceC2051 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2051 sourceB2051 sourceC2051
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2051, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2052 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2052 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 0) (sourceB2052 + difference 0 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 0) (sourceB2052 + difference 0 0) sourceC2052) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 1) (sourceB2052 + difference 1 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 1) (sourceB2052 + difference 1 0) sourceC2052) = raw28968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28968; decide +kernel
    rw [ha]
    exact (canonical28968 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 2) (sourceB2052 + difference 2 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 2) (sourceB2052 + difference 2 0) sourceC2052) = raw28969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28969; decide +kernel
    rw [ha]
    exact (canonical28969 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 3) (sourceB2052 + difference 3 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 3) (sourceB2052 + difference 3 0) sourceC2052) = raw28970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28970; decide +kernel
    rw [ha]
    exact (canonical28970 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 4) (sourceB2052 + difference 4 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 4) (sourceB2052 + difference 4 0) sourceC2052) = raw28971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28971; decide +kernel
    rw [ha]
    exact (canonical28971 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2052 + difference 0 5) (sourceB2052 + difference 5 0) sourceC2052) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2052 + difference 0 5) (sourceB2052 + difference 5 0) sourceC2052) = raw28972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2052 sourceB2052 sourceC2052 difference raw28972; decide +kernel
    rw [ha]
    exact (canonical28972 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2052 + sourceB2052) sourceC2052) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2052 + sourceB2052) sourceC2052) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA2052 sourceB2052 sourceC2052 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2052 sourceB2052 sourceC2052
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2052, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2054 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2054 + difference 0 5) (sourceB2054 + difference 5 0) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2054 + difference 0 5) (sourceB2054 + difference 5 0) sourceC2054) = raw28972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28972; decide +kernel
    rw [ha]
    exact (canonical28972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2054 + difference 1 5) (sourceB2054 + difference 5 1) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2054 + difference 1 5) (sourceB2054 + difference 5 1) sourceC2054) = raw21018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw21018; decide +kernel
    rw [ha]
    exact (canonical21018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2054 + difference 2 5) (sourceB2054 + difference 5 2) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA2054 + difference 2 5) (sourceB2054 + difference 5 2) sourceC2054) = raw28976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28976; decide +kernel
    rw [ha]
    exact (canonical28976 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2054 + difference 3 5) (sourceB2054 + difference 5 3) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA2054 + difference 3 5) (sourceB2054 + difference 5 3) sourceC2054) = raw28977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28977; decide +kernel
    rw [ha]
    exact (canonical28977 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2054 + difference 4 5) (sourceB2054 + difference 5 4) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA2054 + difference 4 5) (sourceB2054 + difference 5 4) sourceC2054) = raw28978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw28978; decide +kernel
    rw [ha]
    exact (canonical28978 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2054 + difference 5 5) (sourceB2054 + difference 5 5) sourceC2054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2054 + difference 5 5) (sourceB2054 + difference 5 5) sourceC2054) = raw21014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2054 sourceB2054 sourceC2054 difference raw21014; decide +kernel
    rw [ha]
    exact (canonical21014 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2054 + sourceB2054) sourceC2054) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2054 + sourceB2054) sourceC2054) = raw21019 := by
      apply Matrix.ext; unfold doubleCharges sourceA2054 sourceB2054 sourceC2054 raw21019; decide +kernel
    rw [ha]
    exact (canonical21019 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2054 sourceB2054 sourceC2054
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2054, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2056 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 0) (sourceB2056 + difference 0 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2377) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 0) (sourceB2056 + difference 0 0) sourceC2056) = raw21041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw21041; decide +kernel
    rw [ha]
    exact (canonical21041 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 1) (sourceB2056 + difference 1 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 1) (sourceB2056 + difference 1 0) sourceC2056) = raw28985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28985; decide +kernel
    rw [ha]
    exact (canonical28985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 2) (sourceB2056 + difference 2 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 2) (sourceB2056 + difference 2 0) sourceC2056) = raw28986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28986; decide +kernel
    rw [ha]
    exact (canonical28986 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 3) (sourceB2056 + difference 3 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 3) (sourceB2056 + difference 3 0) sourceC2056) = raw28987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28987; decide +kernel
    rw [ha]
    exact (canonical28987 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 4) (sourceB2056 + difference 4 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 4) (sourceB2056 + difference 4 0) sourceC2056) = raw28988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28988; decide +kernel
    rw [ha]
    exact (canonical28988 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2056 + difference 0 5) (sourceB2056 + difference 5 0) sourceC2056) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2056 + difference 0 5) (sourceB2056 + difference 5 0) sourceC2056) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2056 sourceB2056 sourceC2056 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2056 + sourceB2056) sourceC2056) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2056 + sourceB2056) sourceC2056) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2056 sourceB2056 sourceC2056 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2056 sourceB2056 sourceC2056
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2056, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1712 : Integer.Sparse.reindex keyMap MixedData.row1712 = numericRow1712 := by decide +kernel

theorem numericCheck1712 (x : Master → ℝ) : Integer.Sparse.eval numericRow1712 x =
    (1 : ℝ) * reducedSource1712 x := by
  norm_num [numericRow1712, reducedSource1712, Integer.Sparse.eval, Sparse.eval, nodeValue1119, nodeValue2325, nodeValue2347, nodeValue2355, nodeValue2482, nodeValue2488, nodeValue4092]

theorem reindexCheck1713 : Integer.Sparse.reindex keyMap MixedData.row1713 = numericRow1713 := by decide +kernel

theorem numericCheck1713 (x : Master → ℝ) : Integer.Sparse.eval numericRow1713 x =
    (1 : ℝ) * reducedSource1713 x := by
  norm_num [numericRow1713, reducedSource1713, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue2319, nodeValue2436, nodeValue2479, nodeValue2482, nodeValue4092]

theorem reindexCheck1714 : Integer.Sparse.reindex keyMap MixedData.row1714 = numericRow1714 := by decide +kernel

theorem numericCheck1714 (x : Master → ℝ) : Integer.Sparse.eval numericRow1714 x =
    (1 : ℝ) * reducedSource1714 x := by
  norm_num [numericRow1714, reducedSource1714, Integer.Sparse.eval, Sparse.eval, nodeValue1131, nodeValue2334, nodeValue2425, nodeValue2482, nodeValue2511, nodeValue2517, nodeValue4092]

theorem reindexCheck1718 : Integer.Sparse.reindex keyMap MixedData.row1718 = numericRow1718 := by decide +kernel

theorem numericCheck1718 (x : Master → ℝ) : Integer.Sparse.eval numericRow1718 x =
    (1 : ℝ) * reducedSource1718 x := by
  norm_num [numericRow1718, reducedSource1718, Integer.Sparse.eval, Sparse.eval, nodeValue1663, nodeValue1672, nodeValue1674, nodeValue1679, nodeValue1725, nodeValue2140, nodeValue2149, nodeValue2151, nodeValue2155, nodeValue2172, nodeValue2173, nodeValue2176, nodeValue2189, nodeValue2190, nodeValue2200, nodeValue2203, nodeValue2205, nodeValue2212, nodeValue2215, nodeValue2226, nodeValue2228, nodeValue2261, nodeValue2264, nodeValue2292, nodeValue2670, nodeValue2693, nodeValue2719, nodeValue2722, nodeValue2740]

theorem reindexCheck1719 : Integer.Sparse.reindex keyMap MixedData.row1719 = numericRow1719 := by decide +kernel

theorem numericCheck1719 (x : Master → ℝ) : Integer.Sparse.eval numericRow1719 x =
    (1 : ℝ) * reducedSource1719 x := by
  norm_num [numericRow1719, reducedSource1719, Integer.Sparse.eval, Sparse.eval, nodeValue912, nodeValue1795, nodeValue1955, nodeValue1978, nodeValue2022, nodeValue2028, nodeValue4084]

theorem reindexCheck1720 : Integer.Sparse.reindex keyMap MixedData.row1720 = numericRow1720 := by decide +kernel

theorem numericCheck1720 (x : Master → ℝ) : Integer.Sparse.eval numericRow1720 x =
    (1 : ℝ) * reducedSource1720 x := by
  norm_num [numericRow1720, reducedSource1720, Integer.Sparse.eval, Sparse.eval, nodeValue1147, nodeValue1955, nodeValue1960, nodeValue2022, nodeValue2552, nodeValue4084]

theorem reindexCheck1721 : Integer.Sparse.reindex keyMap MixedData.row1721 = numericRow1721 := by decide +kernel

theorem numericCheck1721 (x : Master → ℝ) : Integer.Sparse.eval numericRow1721 x =
    (1 : ℝ) * reducedSource1721 x := by
  norm_num [numericRow1721, reducedSource1721, Integer.Sparse.eval, Sparse.eval, nodeValue904, nodeValue1789, nodeValue1972, nodeValue2019, nodeValue2022, nodeValue4084]

theorem reindexCheck1722 : Integer.Sparse.reindex keyMap MixedData.row1722 = numericRow1722 := by decide +kernel

theorem numericCheck1722 (x : Master → ℝ) : Integer.Sparse.eval numericRow1722 x =
    (1 : ℝ) * reducedSource1722 x := by
  norm_num [numericRow1722, reducedSource1722, Integer.Sparse.eval, Sparse.eval, nodeValue924, nodeValue1807, nodeValue1960, nodeValue2022, nodeValue2053, nodeValue2060, nodeValue4084]

theorem reindexCheck1724 : Integer.Sparse.reindex keyMap MixedData.row1724 = numericRow1724 := by decide +kernel

theorem numericCheck1724 (x : Master → ℝ) : Integer.Sparse.eval numericRow1724 x =
    (1 : ℝ) * reducedSource1724 x := by
  norm_num [numericRow1724, reducedSource1724, Integer.Sparse.eval, Sparse.eval, nodeValue2391, nodeValue2535, nodeValue2539, nodeValue2585, nodeValue2686, nodeValue3770, nodeValue4089]

theorem reindexCheck1725 : Integer.Sparse.reindex keyMap MixedData.row1725 = numericRow1725 := by decide +kernel

theorem numericCheck1725 (x : Master → ℝ) : Integer.Sparse.eval numericRow1725 x =
    (1 : ℝ) * reducedSource1725 x := by
  norm_num [numericRow1725, reducedSource1725, Integer.Sparse.eval, Sparse.eval, nodeValue1921, nodeValue1924, nodeValue1928, nodeValue1945, nodeValue2215, nodeValue3478, nodeValue4082]

theorem reindexCheck1726 : Integer.Sparse.reindex keyMap MixedData.row1726 = numericRow1726 := by decide +kernel

theorem numericCheck1726 (x : Master → ℝ) : Integer.Sparse.eval numericRow1726 x =
    (1 : ℝ) * reducedSource1726 x := by
  norm_num [numericRow1726, reducedSource1726, Integer.Sparse.eval, Sparse.eval, nodeValue1924, nodeValue2534, nodeValue2538, nodeValue2584, nodeValue2685, nodeValue3478, nodeValue4082]

theorem reindexCheck1727 : Integer.Sparse.reindex keyMap MixedData.row1727 = numericRow1727 := by decide +kernel

theorem numericCheck1727 (x : Master → ℝ) : Integer.Sparse.eval numericRow1727 x =
    (1 : ℝ) * reducedSource1727 x := by
  norm_num [numericRow1727, reducedSource1727, Integer.Sparse.eval, Sparse.eval, nodeValue2377, nodeValue2379, nodeValue2382, nodeValue2661, nodeValue3757, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1712 (mixedVector B) = 0 := by
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2033, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1119, h2325, h2347, h2355, h2482, h2488, h4092, reducedSource1712] using sourceEq2033 B hB

theorem rowSound1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1712 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1712, numericCheck1712, reducedZero1712 B hB hF, mul_zero]

theorem reducedZero1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1713 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h2319 : mixedVector B (Sum.inr 2319) = Sparse.eval nodeValue2319 (mixedVector B) := by
    change mixedMoment B node2319 node2319Labels = _
    exact sound2319 B hB hF
  have h2436 : mixedVector B (Sum.inr 2436) = Sparse.eval nodeValue2436 (mixedVector B) := by
    change mixedMoment B node2436 node2436Labels = _
    exact sound2436 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2034, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h2319, h2436, h2479, h2482, h4092, reducedSource1713] using sourceEq2034 B hB

theorem rowSound1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1713 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1713, numericCheck1713, reducedZero1713 B hB hF, mul_zero]

theorem reducedZero1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1714 (mixedVector B) = 0 := by
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h2334 : mixedVector B (Sum.inr 2334) = Sparse.eval nodeValue2334 (mixedVector B) := by
    change mixedMoment B node2334 node2334Labels = _
    exact sound2334 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2511 : mixedVector B (Sum.inr 2511) = Sparse.eval nodeValue2511 (mixedVector B) := by
    change mixedMoment B node2511 node2511Labels = _
    exact sound2511 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2035, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1131, h2334, h2425, h2482, h2511, h2517, h4092, reducedSource1714] using sourceEq2035 B hB

theorem rowSound1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1714 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1714, numericCheck1714, reducedZero1714 B hB hF, mul_zero]

theorem reducedZero1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1718 (mixedVector B) = 0 := by
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2172 : mixedVector B (Sum.inr 2172) = Sparse.eval nodeValue2172 (mixedVector B) := by
    change mixedMoment B node2172 node2172Labels = _
    exact sound2172 B hB hF
  have h2173 : mixedVector B (Sum.inr 2173) = Sparse.eval nodeValue2173 (mixedVector B) := by
    change mixedMoment B node2173 node2173Labels = _
    exact sound2173 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  simpa only [sourceForm2041, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1663, h1672, h1674, h1679, h1725, h2140, h2149, h2151, h2155, h2172, h2173, h2176, h2189, h2190, h2200, h2203, h2205, h2212, h2215, h2226, h2228, h2261, h2264, h2292, h2670, h2693, h2719, h2722, h2740, reducedSource1718] using sourceEq2041 B hB

theorem rowSound1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1718 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1718, numericCheck1718, reducedZero1718 B hB hF, mul_zero]

theorem reducedZero1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1719 (mixedVector B) = 0 := by
  have h912 : mixedVector B (Sum.inr 912) = Sparse.eval nodeValue912 (mixedVector B) := by
    change mixedMoment B node912 node912Labels = _
    exact sound912 B hB hF
  have h1795 : mixedVector B (Sum.inr 1795) = Sparse.eval nodeValue1795 (mixedVector B) := by
    change mixedMoment B node1795 node1795Labels = _
    exact sound1795 B hB hF
  have h1955 : mixedVector B (Sum.inr 1955) = Sparse.eval nodeValue1955 (mixedVector B) := by
    change mixedMoment B node1955 node1955Labels = _
    exact sound1955 B hB hF
  have h1978 : mixedVector B (Sum.inr 1978) = Sparse.eval nodeValue1978 (mixedVector B) := by
    change mixedMoment B node1978 node1978Labels = _
    exact sound1978 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2042, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h912, h1795, h1955, h1978, h2022, h2028, h4084, reducedSource1719] using sourceEq2042 B hB

theorem rowSound1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1719 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1719, numericCheck1719, reducedZero1719 B hB hF, mul_zero]

theorem reducedZero1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1720 (mixedVector B) = 0 := by
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1955 : mixedVector B (Sum.inr 1955) = Sparse.eval nodeValue1955 (mixedVector B) := by
    change mixedMoment B node1955 node1955Labels = _
    exact sound1955 B hB hF
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2043, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1147, h1955, h1960, h2022, h2552, h4084, reducedSource1720] using sourceEq2043 B hB

theorem rowSound1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1720 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1720, numericCheck1720, reducedZero1720 B hB hF, mul_zero]

theorem reducedZero1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1721 (mixedVector B) = 0 := by
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h1789 : mixedVector B (Sum.inr 1789) = Sparse.eval nodeValue1789 (mixedVector B) := by
    change mixedMoment B node1789 node1789Labels = _
    exact sound1789 B hB hF
  have h1972 : mixedVector B (Sum.inr 1972) = Sparse.eval nodeValue1972 (mixedVector B) := by
    change mixedMoment B node1972 node1972Labels = _
    exact sound1972 B hB hF
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2044, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h904, h1789, h1972, h2019, h2022, h4084, reducedSource1721] using sourceEq2044 B hB

theorem rowSound1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1721 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1721, numericCheck1721, reducedZero1721 B hB hF, mul_zero]

theorem reducedZero1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1722 (mixedVector B) = 0 := by
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2045, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h924, h1807, h1960, h2022, h2053, h2060, h4084, reducedSource1722] using sourceEq2045 B hB

theorem rowSound1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1722 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1722, numericCheck1722, reducedZero1722 B hB hF, mul_zero]

theorem reducedZero1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1724 (mixedVector B) = 0 := by
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2539 : mixedVector B (Sum.inr 2539) = Sparse.eval nodeValue2539 (mixedVector B) := by
    change mixedMoment B node2539 node2539Labels = _
    exact sound2539 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm2051, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2391, h2535, h2539, h2585, h2686, h3770, h4089, reducedSource1724] using sourceEq2051 B hB

theorem rowSound1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1724 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1724, numericCheck1724, reducedZero1724 B hB hF, mul_zero]

theorem reducedZero1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1725 (mixedVector B) = 0 := by
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2052, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1921, h1924, h1928, h1945, h2215, h3478, h4082, reducedSource1725] using sourceEq2052 B hB

theorem rowSound1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1725 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1725, numericCheck1725, reducedZero1725 B hB hF, mul_zero]

theorem reducedZero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1726 (mixedVector B) = 0 := by
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2054, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1924, h2534, h2538, h2584, h2685, h3478, h4082, reducedSource1726] using sourceEq2054 B hB

theorem rowSound1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1726 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1726, numericCheck1726, reducedZero1726 B hB hF, mul_zero]

theorem reducedZero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1727 (mixedVector B) = 0 := by
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2379 : mixedVector B (Sum.inr 2379) = Sparse.eval nodeValue2379 (mixedVector B) := by
    change mixedMoment B node2379 node2379Labels = _
    exact sound2379 B hB hF
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2056, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2377, h2379, h2382, h2661, h3757, h4088, reducedSource1727] using sourceEq2056 B hB

theorem rowSound1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1727 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1727, numericCheck1727, reducedZero1727 B hB hF, mul_zero]

theorem sourceRowsAt1712 : MixedData.sourceRows (1712 : Fin 2425) =
    MixedData.row1712 := by decide +kernel

theorem sourceRowsAt1713 : MixedData.sourceRows (1713 : Fin 2425) =
    MixedData.row1713 := by decide +kernel

theorem sourceRowsAt1714 : MixedData.sourceRows (1714 : Fin 2425) =
    MixedData.row1714 := by decide +kernel

theorem sourceRowsAt1715 : MixedData.sourceRows (1715 : Fin 2425) =
    MixedData.row1715 := by decide +kernel

theorem sourceRowsAt1716 : MixedData.sourceRows (1716 : Fin 2425) =
    MixedData.row1716 := by decide +kernel

theorem sourceRowsAt1717 : MixedData.sourceRows (1717 : Fin 2425) =
    MixedData.row1717 := by decide +kernel

theorem sourceRowsAt1718 : MixedData.sourceRows (1718 : Fin 2425) =
    MixedData.row1718 := by decide +kernel

theorem sourceRowsAt1719 : MixedData.sourceRows (1719 : Fin 2425) =
    MixedData.row1719 := by decide +kernel

theorem sourceRowsAt1720 : MixedData.sourceRows (1720 : Fin 2425) =
    MixedData.row1720 := by decide +kernel

theorem sourceRowsAt1721 : MixedData.sourceRows (1721 : Fin 2425) =
    MixedData.row1721 := by decide +kernel

theorem sourceRowsAt1722 : MixedData.sourceRows (1722 : Fin 2425) =
    MixedData.row1722 := by decide +kernel

theorem sourceRowsAt1723 : MixedData.sourceRows (1723 : Fin 2425) =
    MixedData.row1723 := by decide +kernel

theorem sourceRowsAt1724 : MixedData.sourceRows (1724 : Fin 2425) =
    MixedData.row1724 := by decide +kernel

theorem sourceRowsAt1725 : MixedData.sourceRows (1725 : Fin 2425) =
    MixedData.row1725 := by decide +kernel

theorem sourceRowsAt1726 : MixedData.sourceRows (1726 : Fin 2425) =
    MixedData.row1726 := by decide +kernel

theorem sourceRowsAt1727 : MixedData.sourceRows (1727 : Fin 2425) =
    MixedData.row1727 := by decide +kernel

theorem chunkSound107_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 107) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1712 ∨ k.val = 1713 ∨ k.val = 1714 ∨ k.val = 1715 ∨ k.val = 1716 ∨ k.val = 1717 ∨ k.val = 1718 ∨ k.val = 1719 ∨ k.val = 1720 ∨ k.val = 1721 ∨ k.val = 1722 ∨ k.val = 1723 ∨ k.val = 1724 ∨ k.val = 1725 ∨ k.val = 1726 ∨ k.val = 1727 := by omega
  rcases heq with h1712 | h1713 | h1714 | h1715 | h1716 | h1717 | h1718 | h1719 | h1720 | h1721 | h1722 | h1723 | h1724 | h1725 | h1726 | h1727
  · have he : k = (1712 : Fin 2425) := Fin.ext h1712
    subst k
    rw [sourceRowsAt1712]
    exact rowSound1712 B hB hF
  · have he : k = (1713 : Fin 2425) := Fin.ext h1713
    subst k
    rw [sourceRowsAt1713]
    exact rowSound1713 B hB hF
  · have he : k = (1714 : Fin 2425) := Fin.ext h1714
    subst k
    rw [sourceRowsAt1714]
    exact rowSound1714 B hB hF
  · have he : k = (1715 : Fin 2425) := Fin.ext h1715
    subst k
    rw [sourceRowsAt1715]
    exact rowSound1715_e B hB hF
  · have he : k = (1716 : Fin 2425) := Fin.ext h1716
    subst k
    rw [sourceRowsAt1716]
    exact rowSound1716_e B hB hF
  · have he : k = (1717 : Fin 2425) := Fin.ext h1717
    subst k
    rw [sourceRowsAt1717]
    exact rowSound1717_e B hB hF
  · have he : k = (1718 : Fin 2425) := Fin.ext h1718
    subst k
    rw [sourceRowsAt1718]
    exact rowSound1718 B hB hF
  · have he : k = (1719 : Fin 2425) := Fin.ext h1719
    subst k
    rw [sourceRowsAt1719]
    exact rowSound1719 B hB hF
  · have he : k = (1720 : Fin 2425) := Fin.ext h1720
    subst k
    rw [sourceRowsAt1720]
    exact rowSound1720 B hB hF
  · have he : k = (1721 : Fin 2425) := Fin.ext h1721
    subst k
    rw [sourceRowsAt1721]
    exact rowSound1721 B hB hF
  · have he : k = (1722 : Fin 2425) := Fin.ext h1722
    subst k
    rw [sourceRowsAt1722]
    exact rowSound1722 B hB hF
  · have he : k = (1723 : Fin 2425) := Fin.ext h1723
    subst k
    rw [sourceRowsAt1723]
    exact rowSound1723_e B hB hF
  · have he : k = (1724 : Fin 2425) := Fin.ext h1724
    subst k
    rw [sourceRowsAt1724]
    exact rowSound1724 B hB hF
  · have he : k = (1725 : Fin 2425) := Fin.ext h1725
    subst k
    rw [sourceRowsAt1725]
    exact rowSound1725 B hB hF
  · have he : k = (1726 : Fin 2425) := Fin.ext h1726
    subst k
    rw [sourceRowsAt1726]
    exact rowSound1726 B hB hF
  · have he : k = (1727 : Fin 2425) := Fin.ext h1727
    subst k
    rw [sourceRowsAt1727]
    exact rowSound1727 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e_oai
