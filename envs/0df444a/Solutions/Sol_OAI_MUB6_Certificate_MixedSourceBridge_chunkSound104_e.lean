-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:45:56.98421+00:00
-- url     : https://prove2.me/submissions/ea527fc0-d1ff-4855-a25a-60dfd0a57c86

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero1674_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1668_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1669_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1672_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1673_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1679_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27368 raw27368Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw27368 raw27368Labels = mixedMoment B raw27368step0 raw27368step0Labels := by
      have hz : ∀ j, raw27368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27368step0 = (fun i j => raw27368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27368step0 raw27368; decide +kernel
      have hl : raw27368step0Labels = raw27368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27368 raw27368Labels permutation346 hz
    mixedMoment B raw27368step0 raw27368step0Labels = mixedMoment B raw27368step1 raw27368step1Labels := by
      have ha : raw27368step1 = (fun i j => raw27368step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27368step1 raw27368step0; decide +kernel
      have hl : raw27368step1Labels = raw27368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27368step0 raw27368step0Labels permutation34 permutation4
    mixedMoment B raw27368step1 raw27368step1Labels = mixedMoment B raw27368step2 raw27368step2Labels := by
      have ha : raw27368step2 = -raw27368step1 := by apply Matrix.ext; change ∀ i j, raw27368step2 i j = -(raw27368step1 i j); unfold raw27368step2 raw27368step1; decide +kernel
      have hl : raw27368step2Labels = raw27368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2203 node2203Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27524 raw27524Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw27524 raw27524Labels = mixedMoment B raw27524step0 raw27524step0Labels := by
      have hz : ∀ j, raw27524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27524step0 = (fun i j => raw27524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27524step0 raw27524; decide +kernel
      have hl : raw27524step0Labels = raw27524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27524 raw27524Labels permutation346 hz
    mixedMoment B raw27524step0 raw27524step0Labels = mixedMoment B raw27524step1 raw27524step1Labels := by
      have ha : raw27524step1 = (fun i j => raw27524step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27524step1 raw27524step0; decide +kernel
      have hl : raw27524step1Labels = raw27524step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27524step0 raw27524step0Labels permutation143 permutation4
    _ = mixedMoment B node3530 node3530Labels := by rfl

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

theorem canonical27817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27817 raw27817Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw27817 raw27817Labels = mixedMoment B raw27817step0 raw27817step0Labels := by
      have hz : ∀ j, raw27817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27817step0 = (fun i j => raw27817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27817step0 raw27817; decide +kernel
      have hl : raw27817step0Labels = raw27817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27817 raw27817Labels permutation346 hz
    mixedMoment B raw27817step0 raw27817step0Labels = mixedMoment B raw27817step1 raw27817step1Labels := by
      have ha : raw27817step1 = (fun i j => raw27817step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27817step1 raw27817step0; decide +kernel
      have hl : raw27817step1Labels = raw27817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27817step0 raw27817step0Labels permutation149 permutation2
    mixedMoment B raw27817step1 raw27817step1Labels = mixedMoment B raw27817step2 raw27817step2Labels := by
      have ha : raw27817step2 = -raw27817step1 := by apply Matrix.ext; change ∀ i j, raw27817step2 i j = -(raw27817step1 i j); unfold raw27817step2 raw27817step1; decide +kernel
      have hl : raw27817step2Labels = raw27817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical27818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27818 raw27818Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw27818 raw27818Labels = mixedMoment B raw27818step0 raw27818step0Labels := by
      have hz : ∀ j, raw27818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27818step0 = (fun i j => raw27818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27818step0 raw27818; decide +kernel
      have hl : raw27818step0Labels = raw27818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27818 raw27818Labels permutation346 hz
    mixedMoment B raw27818step0 raw27818step0Labels = mixedMoment B raw27818step1 raw27818step1Labels := by
      have ha : raw27818step1 = (fun i j => raw27818step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27818step1 raw27818step0; decide +kernel
      have hl : raw27818step1Labels = raw27818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27818step0 raw27818step0Labels permutation149 permutation2
    mixedMoment B raw27818step1 raw27818step1Labels = mixedMoment B raw27818step2 raw27818step2Labels := by
      have ha : raw27818step2 = -raw27818step1 := by apply Matrix.ext; change ∀ i j, raw27818step2 i j = -(raw27818step1 i j); unfold raw27818step2 raw27818step1; decide +kernel
      have hl : raw27818step2Labels = raw27818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical27819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27819 raw27819Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw27819 raw27819Labels = mixedMoment B raw27819step0 raw27819step0Labels := by
      have ha : raw27819step0 = (fun i j => raw27819 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27819step0 raw27819; decide +kernel
      have hl : raw27819step0Labels = raw27819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27819 raw27819Labels permutation680 permutation2
    mixedMoment B raw27819step0 raw27819step0Labels = mixedMoment B raw27819step1 raw27819step1Labels := by
      have ha : raw27819step1 = -raw27819step0 := by apply Matrix.ext; change ∀ i j, raw27819step1 i j = -(raw27819step0 i j); unfold raw27819step1 raw27819step0; decide +kernel
      have hl : raw27819step1Labels = raw27819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

theorem canonical27820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27820 raw27820Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw27820 raw27820Labels = mixedMoment B raw27820step0 raw27820step0Labels := by
      have hz : ∀ j, raw27820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27820step0 = (fun i j => raw27820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27820step0 raw27820; decide +kernel
      have hl : raw27820step0Labels = raw27820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27820 raw27820Labels permutation346 hz
    mixedMoment B raw27820step0 raw27820step0Labels = mixedMoment B raw27820step1 raw27820step1Labels := by
      have ha : raw27820step1 = (fun i j => raw27820step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27820step1 raw27820step0; decide +kernel
      have hl : raw27820step1Labels = raw27820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27820step0 raw27820step0Labels permutation151 permutation2
    mixedMoment B raw27820step1 raw27820step1Labels = mixedMoment B raw27820step2 raw27820step2Labels := by
      have ha : raw27820step2 = -raw27820step1 := by apply Matrix.ext; change ∀ i j, raw27820step2 i j = -(raw27820step1 i j); unfold raw27820step2 raw27820step1; decide +kernel
      have hl : raw27820step2Labels = raw27820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical27821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27821 raw27821Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27821 raw27821Labels = mixedMoment B raw27821step0 raw27821step0Labels := by
      have hz : ∀ j, raw27821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27821step0 = (fun i j => raw27821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27821step0 raw27821; decide +kernel
      have hl : raw27821step0Labels = raw27821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27821 raw27821Labels permutation346 hz
    mixedMoment B raw27821step0 raw27821step0Labels = mixedMoment B raw27821step1 raw27821step1Labels := by
      have ha : raw27821step1 = (fun i j => raw27821step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27821step1 raw27821step0; decide +kernel
      have hl : raw27821step1Labels = raw27821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27821step0 raw27821step0Labels permutation149 permutation2
    mixedMoment B raw27821step1 raw27821step1Labels = mixedMoment B raw27821step2 raw27821step2Labels := by
      have ha : raw27821step2 = -raw27821step1 := by apply Matrix.ext; change ∀ i j, raw27821step2 i j = -(raw27821step1 i j); unfold raw27821step2 raw27821step1; decide +kernel
      have hl : raw27821step2Labels = raw27821step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical27822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27822 raw27822Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw27822 raw27822Labels = mixedMoment B raw27822step0 raw27822step0Labels := by
      have hz : ∀ j, raw27822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27822step0 = (fun i j => raw27822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27822step0 raw27822; decide +kernel
      have hl : raw27822step0Labels = raw27822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27822 raw27822Labels permutation346 hz
    mixedMoment B raw27822step0 raw27822step0Labels = mixedMoment B raw27822step1 raw27822step1Labels := by
      have ha : raw27822step1 = (fun i j => raw27822step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27822step1 raw27822step0; decide +kernel
      have hl : raw27822step1Labels = raw27822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27822step0 raw27822step0Labels permutation149 permutation2
    mixedMoment B raw27822step1 raw27822step1Labels = mixedMoment B raw27822step2 raw27822step2Labels := by
      have ha : raw27822step2 = -raw27822step1 := by apply Matrix.ext; change ∀ i j, raw27822step2 i j = -(raw27822step1 i j); unfold raw27822step2 raw27822step1; decide +kernel
      have hl : raw27822step2Labels = raw27822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

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

theorem canonical27824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27824 raw27824Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw27824 raw27824Labels = mixedMoment B raw27824step0 raw27824step0Labels := by
      have hz : ∀ j, raw27824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27824step0 = (fun i j => raw27824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27824step0 raw27824; decide +kernel
      have hl : raw27824step0Labels = raw27824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27824 raw27824Labels permutation346 hz
    _ = mixedMoment B node1334 node1334Labels := by rfl

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

theorem canonical27826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27826 raw27826Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw27826 raw27826Labels = mixedMoment B raw27826step0 raw27826step0Labels := by
      have ha : raw27826step0 = (fun i j => raw27826 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27826step0 raw27826; decide +kernel
      have hl : raw27826step0Labels = raw27826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27826 raw27826Labels permutation688 permutation2
    mixedMoment B raw27826step0 raw27826step0Labels = mixedMoment B raw27826step1 raw27826step1Labels := by
      have ha : raw27826step1 = -raw27826step0 := by apply Matrix.ext; change ∀ i j, raw27826step1 i j = -(raw27826step0 i j); unfold raw27826step1 raw27826step0; decide +kernel
      have hl : raw27826step1Labels = raw27826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2797 node2797Labels := by rfl

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

theorem canonical27828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27828 raw27828Labels = mixedMoment B node2099 node2099Labels := by
  calc
    mixedMoment B raw27828 raw27828Labels = mixedMoment B raw27828step0 raw27828step0Labels := by
      have hz : ∀ j, raw27828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27828step0 = (fun i j => raw27828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27828step0 raw27828; decide +kernel
      have hl : raw27828step0Labels = raw27828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27828 raw27828Labels permutation346 hz
    mixedMoment B raw27828step0 raw27828step0Labels = mixedMoment B raw27828step1 raw27828step1Labels := by
      have ha : raw27828step1 = (fun i j => raw27828step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27828step1 raw27828step0; decide +kernel
      have hl : raw27828step1Labels = raw27828step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27828step0 raw27828step0Labels permutation44 permutation4
    mixedMoment B raw27828step1 raw27828step1Labels = mixedMoment B raw27828step2 raw27828step2Labels := by
      have ha : raw27828step2 = -raw27828step1 := by apply Matrix.ext; change ∀ i j, raw27828step2 i j = -(raw27828step1 i j); unfold raw27828step2 raw27828step1; decide +kernel
      have hl : raw27828step2Labels = raw27828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2099 node2099Labels := by rfl

theorem canonical27829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27829 raw27829Labels = mixedMoment B node2074 node2074Labels := by
  calc
    mixedMoment B raw27829 raw27829Labels = mixedMoment B raw27829step0 raw27829step0Labels := by
      have ha : raw27829step0 = (fun i j => raw27829 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27829step0 raw27829; decide +kernel
      have hl : raw27829step0Labels = raw27829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27829 raw27829Labels permutation224 permutation4
    mixedMoment B raw27829step0 raw27829step0Labels = mixedMoment B raw27829step1 raw27829step1Labels := by
      have ha : raw27829step1 = -raw27829step0 := by apply Matrix.ext; change ∀ i j, raw27829step1 i j = -(raw27829step0 i j); unfold raw27829step1 raw27829step0; decide +kernel
      have hl : raw27829step1Labels = raw27829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2074 node2074Labels := by rfl

theorem canonical27830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27830 raw27830Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw27830 raw27830Labels = mixedMoment B raw27830step0 raw27830step0Labels := by
      have hz : ∀ j, raw27830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27830step0 = (fun i j => raw27830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27830step0 raw27830; decide +kernel
      have hl : raw27830step0Labels = raw27830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27830 raw27830Labels permutation346 hz
    mixedMoment B raw27830step0 raw27830step0Labels = mixedMoment B raw27830step1 raw27830step1Labels := by
      have ha : raw27830step1 = (fun i j => raw27830step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27830step1 raw27830step0; decide +kernel
      have hl : raw27830step1Labels = raw27830step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27830step0 raw27830step0Labels permutation44 permutation4
    mixedMoment B raw27830step1 raw27830step1Labels = mixedMoment B raw27830step2 raw27830step2Labels := by
      have ha : raw27830step2 = -raw27830step1 := by apply Matrix.ext; change ∀ i j, raw27830step2 i j = -(raw27830step1 i j); unfold raw27830step2 raw27830step1; decide +kernel
      have hl : raw27830step2Labels = raw27830step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2081 node2081Labels := by rfl

theorem canonical27831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27831 raw27831Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw27831 raw27831Labels = mixedMoment B raw27831step0 raw27831step0Labels := by
      have hz : ∀ j, raw27831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27831step0 = (fun i j => raw27831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27831step0 raw27831; decide +kernel
      have hl : raw27831step0Labels = raw27831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27831 raw27831Labels permutation346 hz
    mixedMoment B raw27831step0 raw27831step0Labels = mixedMoment B raw27831step1 raw27831step1Labels := by
      have ha : raw27831step1 = (fun i j => raw27831step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27831step1 raw27831step0; decide +kernel
      have hl : raw27831step1Labels = raw27831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27831step0 raw27831step0Labels permutation143 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical27832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27832 raw27832Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw27832 raw27832Labels = mixedMoment B raw27832step0 raw27832step0Labels := by
      have hz : ∀ j, raw27832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27832step0 = (fun i j => raw27832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27832step0 raw27832; decide +kernel
      have hl : raw27832step0Labels = raw27832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27832 raw27832Labels permutation346 hz
    mixedMoment B raw27832step0 raw27832step0Labels = mixedMoment B raw27832step1 raw27832step1Labels := by
      have ha : raw27832step1 = (fun i j => raw27832step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27832step1 raw27832step0; decide +kernel
      have hl : raw27832step1Labels = raw27832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27832step0 raw27832step0Labels permutation145 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical27833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27833 raw27833Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw27833 raw27833Labels = mixedMoment B raw27833step0 raw27833step0Labels := by
      have ha : raw27833step0 = (fun i j => raw27833 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27833step0 raw27833; decide +kernel
      have hl : raw27833step0Labels = raw27833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27833 raw27833Labels permutation654 permutation4
    _ = mixedMoment B node2015 node2015Labels := by rfl

theorem canonical27834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27834 raw27834Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw27834 raw27834Labels = mixedMoment B raw27834step0 raw27834step0Labels := by
      have hz : ∀ j, raw27834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27834step0 = (fun i j => raw27834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27834step0 raw27834; decide +kernel
      have hl : raw27834step0Labels = raw27834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27834 raw27834Labels permutation434 hz
    mixedMoment B raw27834step0 raw27834step0Labels = mixedMoment B raw27834step1 raw27834step1Labels := by
      have hz : ∀ j, raw27834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27834step1 = (fun i j => raw27834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27834step1 raw27834step0; decide +kernel
      have hl : raw27834step1Labels = raw27834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27834step0 raw27834step0Labels permutation80 hz
    mixedMoment B raw27834step1 raw27834step1Labels = mixedMoment B raw27834step2 raw27834step2Labels := by
      have ha : raw27834step2 = (fun i j => raw27834step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27834step2 raw27834step1; decide +kernel
      have hl : raw27834step2Labels = raw27834step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27834step1 raw27834step1Labels permutation29 permutation4
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical27835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27835 raw27835Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw27835 raw27835Labels = mixedMoment B raw27835step0 raw27835step0Labels := by
      have hz : ∀ j, raw27835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27835step0 = (fun i j => raw27835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27835step0 raw27835; decide +kernel
      have hl : raw27835step0Labels = raw27835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27835 raw27835Labels permutation346 hz
    mixedMoment B raw27835step0 raw27835step0Labels = mixedMoment B raw27835step1 raw27835step1Labels := by
      have ha : raw27835step1 = (fun i j => raw27835step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27835step1 raw27835step0; decide +kernel
      have hl : raw27835step1Labels = raw27835step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27835step0 raw27835step0Labels permutation143 permutation4
    _ = mixedMoment B node2027 node2027Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27914 raw27914Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw27914 raw27914Labels = mixedMoment B raw27914step0 raw27914step0Labels := by
      have hz : ∀ j, raw27914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27914step0 = (fun i j => raw27914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27914step0 raw27914; decide +kernel
      have hl : raw27914step0Labels = raw27914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27914 raw27914Labels permutation346 hz
    mixedMoment B raw27914step0 raw27914step0Labels = mixedMoment B raw27914step1 raw27914step1Labels := by
      have ha : raw27914step1 = (fun i j => raw27914step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27914step1 raw27914step0; decide +kernel
      have hl : raw27914step1Labels = raw27914step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27914step0 raw27914step0Labels permutation150 permutation7
    mixedMoment B raw27914step1 raw27914step1Labels = mixedMoment B raw27914step2 raw27914step2Labels := by
      have ha : raw27914step2 = raw27914step1 := by apply Matrix.ext; unfold raw27914step2 raw27914step1; decide +kernel
      have hl : raw27914step1Labels = labelEmbedding1 ∘ raw27914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27914step1 raw27914step1Labels raw27914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical27915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27915 raw27915Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw27915 raw27915Labels = mixedMoment B raw27915step0 raw27915step0Labels := by
      have ha : raw27915step0 = (fun i j => raw27915 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27915step0 raw27915; decide +kernel
      have hl : raw27915step0Labels = raw27915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27915 raw27915Labels permutation682 permutation7
    mixedMoment B raw27915step0 raw27915step0Labels = mixedMoment B raw27915step1 raw27915step1Labels := by
      have ha : raw27915step1 = raw27915step0 := by apply Matrix.ext; unfold raw27915step1 raw27915step0; decide +kernel
      have hl : raw27915step0Labels = labelEmbedding1 ∘ raw27915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27915step0 raw27915step0Labels raw27915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical27916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27916 raw27916Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw27916 raw27916Labels = mixedMoment B raw27916step0 raw27916step0Labels := by
      have hz : ∀ j, raw27916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27916step0 = (fun i j => raw27916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27916step0 raw27916; decide +kernel
      have hl : raw27916step0Labels = raw27916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27916 raw27916Labels permutation346 hz
    mixedMoment B raw27916step0 raw27916step0Labels = mixedMoment B raw27916step1 raw27916step1Labels := by
      have ha : raw27916step1 = (fun i j => raw27916step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27916step1 raw27916step0; decide +kernel
      have hl : raw27916step1Labels = raw27916step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27916step0 raw27916step0Labels permutation149 permutation7
    mixedMoment B raw27916step1 raw27916step1Labels = mixedMoment B raw27916step2 raw27916step2Labels := by
      have ha : raw27916step2 = raw27916step1 := by apply Matrix.ext; unfold raw27916step2 raw27916step1; decide +kernel
      have hl : raw27916step1Labels = labelEmbedding1 ∘ raw27916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27916step1 raw27916step1Labels raw27916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical27917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27917 raw27917Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw27917 raw27917Labels = mixedMoment B raw27917step0 raw27917step0Labels := by
      have hz : ∀ j, raw27917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27917step0 = (fun i j => raw27917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27917step0 raw27917; decide +kernel
      have hl : raw27917step0Labels = raw27917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27917 raw27917Labels permutation346 hz
    mixedMoment B raw27917step0 raw27917step0Labels = mixedMoment B raw27917step1 raw27917step1Labels := by
      have ha : raw27917step1 = (fun i j => raw27917step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27917step1 raw27917step0; decide +kernel
      have hl : raw27917step1Labels = raw27917step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27917step0 raw27917step0Labels permutation151 permutation7
    mixedMoment B raw27917step1 raw27917step1Labels = mixedMoment B raw27917step2 raw27917step2Labels := by
      have ha : raw27917step2 = raw27917step1 := by apply Matrix.ext; unfold raw27917step2 raw27917step1; decide +kernel
      have hl : raw27917step1Labels = labelEmbedding1 ∘ raw27917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27917step1 raw27917step1Labels raw27917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical27918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27918 raw27918Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw27918 raw27918Labels = mixedMoment B raw27918step0 raw27918step0Labels := by
      have hz : ∀ j, raw27918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27918step0 = (fun i j => raw27918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27918step0 raw27918; decide +kernel
      have hl : raw27918step0Labels = raw27918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27918 raw27918Labels permutation346 hz
    mixedMoment B raw27918step0 raw27918step0Labels = mixedMoment B raw27918step1 raw27918step1Labels := by
      have ha : raw27918step1 = (fun i j => raw27918step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27918step1 raw27918step0; decide +kernel
      have hl : raw27918step1Labels = raw27918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27918step0 raw27918step0Labels permutation151 permutation7
    mixedMoment B raw27918step1 raw27918step1Labels = mixedMoment B raw27918step2 raw27918step2Labels := by
      have ha : raw27918step2 = raw27918step1 := by apply Matrix.ext; unfold raw27918step2 raw27918step1; decide +kernel
      have hl : raw27918step1Labels = labelEmbedding1 ∘ raw27918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27918step1 raw27918step1Labels raw27918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical27919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27919 raw27919Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw27919 raw27919Labels = mixedMoment B raw27919step0 raw27919step0Labels := by
      have hz : ∀ j, raw27919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27919step0 = (fun i j => raw27919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27919step0 raw27919; decide +kernel
      have hl : raw27919step0Labels = raw27919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27919 raw27919Labels permutation346 hz
    mixedMoment B raw27919step0 raw27919step0Labels = mixedMoment B raw27919step1 raw27919step1Labels := by
      have ha : raw27919step1 = (fun i j => raw27919step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27919step1 raw27919step0; decide +kernel
      have hl : raw27919step1Labels = raw27919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27919step0 raw27919step0Labels permutation44 permutation5
    mixedMoment B raw27919step1 raw27919step1Labels = mixedMoment B raw27919step2 raw27919step2Labels := by
      have ha : raw27919step2 = -raw27919step1 := by apply Matrix.ext; change ∀ i j, raw27919step2 i j = -(raw27919step1 i j); unfold raw27919step2 raw27919step1; decide +kernel
      have hl : raw27919step2Labels = raw27919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27919step2 raw27919step2Labels = mixedMoment B raw27919step3 raw27919step3Labels := by
      have ha : raw27919step3 = raw27919step2 := by apply Matrix.ext; unfold raw27919step3 raw27919step2; decide +kernel
      have hl : raw27919step2Labels = labelEmbedding1 ∘ raw27919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27919step2 raw27919step2Labels raw27919step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical27920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27920 raw27920Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw27920 raw27920Labels = mixedMoment B raw27920step0 raw27920step0Labels := by
      have ha : raw27920step0 = (fun i j => raw27920 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27920step0 raw27920; decide +kernel
      have hl : raw27920step0Labels = raw27920Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27920 raw27920Labels permutation188 permutation5
    mixedMoment B raw27920step0 raw27920step0Labels = mixedMoment B raw27920step1 raw27920step1Labels := by
      have ha : raw27920step1 = -raw27920step0 := by apply Matrix.ext; change ∀ i j, raw27920step1 i j = -(raw27920step0 i j); unfold raw27920step1 raw27920step0; decide +kernel
      have hl : raw27920step1Labels = raw27920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27920step1 raw27920step1Labels = mixedMoment B raw27920step2 raw27920step2Labels := by
      have ha : raw27920step2 = raw27920step1 := by apply Matrix.ext; unfold raw27920step2 raw27920step1; decide +kernel
      have hl : raw27920step1Labels = labelEmbedding1 ∘ raw27920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27920step1 raw27920step1Labels raw27920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

theorem canonical27921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27921 raw27921Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27921 raw27921Labels = mixedMoment B raw27921step0 raw27921step0Labels := by
      have hz : ∀ j, raw27921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27921step0 = (fun i j => raw27921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27921step0 raw27921; decide +kernel
      have hl : raw27921step0Labels = raw27921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27921 raw27921Labels permutation346 hz
    mixedMoment B raw27921step0 raw27921step0Labels = mixedMoment B raw27921step1 raw27921step1Labels := by
      have ha : raw27921step1 = (fun i j => raw27921step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27921step1 raw27921step0; decide +kernel
      have hl : raw27921step1Labels = raw27921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27921step0 raw27921step0Labels permutation149 permutation7
    mixedMoment B raw27921step1 raw27921step1Labels = mixedMoment B raw27921step2 raw27921step2Labels := by
      have ha : raw27921step2 = raw27921step1 := by apply Matrix.ext; unfold raw27921step2 raw27921step1; decide +kernel
      have hl : raw27921step1Labels = labelEmbedding1 ∘ raw27921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27921step1 raw27921step1Labels raw27921step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27922 raw27922Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw27922 raw27922Labels = mixedMoment B raw27922step0 raw27922step0Labels := by
      have hz : ∀ j, raw27922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27922step0 = (fun i j => raw27922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27922step0 raw27922; decide +kernel
      have hl : raw27922step0Labels = raw27922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27922 raw27922Labels permutation346 hz
    mixedMoment B raw27922step0 raw27922step0Labels = mixedMoment B raw27922step1 raw27922step1Labels := by
      have ha : raw27922step1 = (fun i j => raw27922step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27922step1 raw27922step0; decide +kernel
      have hl : raw27922step1Labels = raw27922step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27922step0 raw27922step0Labels permutation44 permutation5
    mixedMoment B raw27922step1 raw27922step1Labels = mixedMoment B raw27922step2 raw27922step2Labels := by
      have ha : raw27922step2 = -raw27922step1 := by apply Matrix.ext; change ∀ i j, raw27922step2 i j = -(raw27922step1 i j); unfold raw27922step2 raw27922step1; decide +kernel
      have hl : raw27922step2Labels = raw27922step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27922step2 raw27922step2Labels = mixedMoment B raw27922step3 raw27922step3Labels := by
      have ha : raw27922step3 = raw27922step2 := by apply Matrix.ext; unfold raw27922step3 raw27922step2; decide +kernel
      have hl : raw27922step2Labels = labelEmbedding1 ∘ raw27922step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27922step2 raw27922step2Labels raw27922step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical27923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27923 raw27923Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw27923 raw27923Labels = mixedMoment B raw27923step0 raw27923step0Labels := by
      have hz : ∀ j, raw27923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27923step0 = (fun i j => raw27923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27923step0 raw27923; decide +kernel
      have hl : raw27923step0Labels = raw27923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27923 raw27923Labels permutation346 hz
    mixedMoment B raw27923step0 raw27923step0Labels = mixedMoment B raw27923step1 raw27923step1Labels := by
      have ha : raw27923step1 = (fun i j => raw27923step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27923step1 raw27923step0; decide +kernel
      have hl : raw27923step1Labels = raw27923step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27923step0 raw27923step0Labels permutation48 permutation5
    mixedMoment B raw27923step1 raw27923step1Labels = mixedMoment B raw27923step2 raw27923step2Labels := by
      have ha : raw27923step2 = -raw27923step1 := by apply Matrix.ext; change ∀ i j, raw27923step2 i j = -(raw27923step1 i j); unfold raw27923step2 raw27923step1; decide +kernel
      have hl : raw27923step2Labels = raw27923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27923step2 raw27923step2Labels = mixedMoment B raw27923step3 raw27923step3Labels := by
      have ha : raw27923step3 = raw27923step2 := by apply Matrix.ext; unfold raw27923step3 raw27923step2; decide +kernel
      have hl : raw27923step2Labels = labelEmbedding1 ∘ raw27923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27923step2 raw27923step2Labels raw27923step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical27924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27924 raw27924Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw27924 raw27924Labels = mixedMoment B raw27924step0 raw27924step0Labels := by
      have ha : raw27924step0 = (fun i j => raw27924 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27924step0 raw27924; decide +kernel
      have hl : raw27924step0Labels = raw27924Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27924 raw27924Labels permutation166 permutation5
    mixedMoment B raw27924step0 raw27924step0Labels = mixedMoment B raw27924step1 raw27924step1Labels := by
      have ha : raw27924step1 = -raw27924step0 := by apply Matrix.ext; change ∀ i j, raw27924step1 i j = -(raw27924step0 i j); unfold raw27924step1 raw27924step0; decide +kernel
      have hl : raw27924step1Labels = raw27924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27924step1 raw27924step1Labels = mixedMoment B raw27924step2 raw27924step2Labels := by
      have ha : raw27924step2 = raw27924step1 := by apply Matrix.ext; unfold raw27924step2 raw27924step1; decide +kernel
      have hl : raw27924step1Labels = labelEmbedding1 ∘ raw27924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27924step1 raw27924step1Labels raw27924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical27925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27925 raw27925Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw27925 raw27925Labels = mixedMoment B raw27925step0 raw27925step0Labels := by
      have ha : raw27925step0 = (fun i j => raw27925 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27925step0 raw27925; decide +kernel
      have hl : raw27925step0Labels = raw27925Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27925 raw27925Labels permutation166 permutation5
    mixedMoment B raw27925step0 raw27925step0Labels = mixedMoment B raw27925step1 raw27925step1Labels := by
      have ha : raw27925step1 = -raw27925step0 := by apply Matrix.ext; change ∀ i j, raw27925step1 i j = -(raw27925step0 i j); unfold raw27925step1 raw27925step0; decide +kernel
      have hl : raw27925step1Labels = raw27925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27925step1 raw27925step1Labels = mixedMoment B raw27925step2 raw27925step2Labels := by
      have ha : raw27925step2 = raw27925step1 := by apply Matrix.ext; unfold raw27925step2 raw27925step1; decide +kernel
      have hl : raw27925step1Labels = labelEmbedding1 ∘ raw27925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27925step1 raw27925step1Labels raw27925step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical27926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27926 raw27926Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw27926 raw27926Labels = mixedMoment B raw27926step0 raw27926step0Labels := by
      have ha : raw27926step0 = (fun i j => raw27926 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27926step0 raw27926; decide +kernel
      have hl : raw27926step0Labels = raw27926Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27926 raw27926Labels permutation680 permutation7
    mixedMoment B raw27926step0 raw27926step0Labels = mixedMoment B raw27926step1 raw27926step1Labels := by
      have ha : raw27926step1 = raw27926step0 := by apply Matrix.ext; unfold raw27926step1 raw27926step0; decide +kernel
      have hl : raw27926step0Labels = labelEmbedding1 ∘ raw27926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27926step0 raw27926step0Labels raw27926step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical27927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27927 raw27927Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27927 raw27927Labels = mixedMoment B raw27927step0 raw27927step0Labels := by
      have ha : raw27927step0 = (fun i j => raw27927 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27927step0 raw27927; decide +kernel
      have hl : raw27927step0Labels = raw27927Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27927 raw27927Labels permutation226 permutation5
    mixedMoment B raw27927step0 raw27927step0Labels = mixedMoment B raw27927step1 raw27927step1Labels := by
      have ha : raw27927step1 = -raw27927step0 := by apply Matrix.ext; change ∀ i j, raw27927step1 i j = -(raw27927step0 i j); unfold raw27927step1 raw27927step0; decide +kernel
      have hl : raw27927step1Labels = raw27927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27927step1 raw27927step1Labels = mixedMoment B raw27927step2 raw27927step2Labels := by
      have ha : raw27927step2 = raw27927step1 := by apply Matrix.ext; unfold raw27927step2 raw27927step1; decide +kernel
      have hl : raw27927step1Labels = labelEmbedding1 ∘ raw27927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27927step1 raw27927step1Labels raw27927step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical27928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27928 raw27928Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw27928 raw27928Labels = mixedMoment B raw27928step0 raw27928step0Labels := by
      have ha : raw27928step0 = (fun i j => raw27928 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27928step0 raw27928; decide +kernel
      have hl : raw27928step0Labels = raw27928Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27928 raw27928Labels permutation169 permutation5
    mixedMoment B raw27928step0 raw27928step0Labels = mixedMoment B raw27928step1 raw27928step1Labels := by
      have ha : raw27928step1 = -raw27928step0 := by apply Matrix.ext; change ∀ i j, raw27928step1 i j = -(raw27928step0 i j); unfold raw27928step1 raw27928step0; decide +kernel
      have hl : raw27928step1Labels = raw27928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27928step1 raw27928step1Labels = mixedMoment B raw27928step2 raw27928step2Labels := by
      have ha : raw27928step2 = raw27928step1 := by apply Matrix.ext; unfold raw27928step2 raw27928step1; decide +kernel
      have hl : raw27928step1Labels = labelEmbedding1 ∘ raw27928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27928step1 raw27928step1Labels raw27928step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical27929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27929 raw27929Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw27929 raw27929Labels = mixedMoment B raw27929step0 raw27929step0Labels := by
      have hz : ∀ j, raw27929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27929step0 = (fun i j => raw27929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27929step0 raw27929; decide +kernel
      have hl : raw27929step0Labels = raw27929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27929 raw27929Labels permutation346 hz
    mixedMoment B raw27929step0 raw27929step0Labels = mixedMoment B raw27929step1 raw27929step1Labels := by
      have ha : raw27929step1 = (fun i j => raw27929step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27929step1 raw27929step0; decide +kernel
      have hl : raw27929step1Labels = raw27929step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27929step0 raw27929step0Labels permutation35 permutation5
    mixedMoment B raw27929step1 raw27929step1Labels = mixedMoment B raw27929step2 raw27929step2Labels := by
      have ha : raw27929step2 = -raw27929step1 := by apply Matrix.ext; change ∀ i j, raw27929step2 i j = -(raw27929step1 i j); unfold raw27929step2 raw27929step1; decide +kernel
      have hl : raw27929step2Labels = raw27929step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27929step2 raw27929step2Labels = mixedMoment B raw27929step3 raw27929step3Labels := by
      have ha : raw27929step3 = raw27929step2 := by apply Matrix.ext; unfold raw27929step3 raw27929step2; decide +kernel
      have hl : raw27929step2Labels = labelEmbedding1 ∘ raw27929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27929step2 raw27929step2Labels raw27929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical27930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27930 raw27930Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw27930 raw27930Labels = mixedMoment B raw27930step0 raw27930step0Labels := by
      have hz : ∀ j, raw27930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27930step0 = (fun i j => raw27930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27930step0 raw27930; decide +kernel
      have hl : raw27930step0Labels = raw27930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27930 raw27930Labels permutation346 hz
    mixedMoment B raw27930step0 raw27930step0Labels = mixedMoment B raw27930step1 raw27930step1Labels := by
      have ha : raw27930step1 = (fun i j => raw27930step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27930step1 raw27930step0; decide +kernel
      have hl : raw27930step1Labels = raw27930step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27930step0 raw27930step0Labels permutation35 permutation5
    mixedMoment B raw27930step1 raw27930step1Labels = mixedMoment B raw27930step2 raw27930step2Labels := by
      have ha : raw27930step2 = -raw27930step1 := by apply Matrix.ext; change ∀ i j, raw27930step2 i j = -(raw27930step1 i j); unfold raw27930step2 raw27930step1; decide +kernel
      have hl : raw27930step2Labels = raw27930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27930step2 raw27930step2Labels = mixedMoment B raw27930step3 raw27930step3Labels := by
      have ha : raw27930step3 = raw27930step2 := by apply Matrix.ext; unfold raw27930step3 raw27930step2; decide +kernel
      have hl : raw27930step2Labels = labelEmbedding1 ∘ raw27930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27930step2 raw27930step2Labels raw27930step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical27931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27931 raw27931Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw27931 raw27931Labels = mixedMoment B raw27931step0 raw27931step0Labels := by
      have ha : raw27931step0 = (fun i j => raw27931 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27931step0 raw27931; decide +kernel
      have hl : raw27931step0Labels = raw27931Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27931 raw27931Labels permutation179 permutation5
    mixedMoment B raw27931step0 raw27931step0Labels = mixedMoment B raw27931step1 raw27931step1Labels := by
      have ha : raw27931step1 = -raw27931step0 := by apply Matrix.ext; change ∀ i j, raw27931step1 i j = -(raw27931step0 i j); unfold raw27931step1 raw27931step0; decide +kernel
      have hl : raw27931step1Labels = raw27931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27931step1 raw27931step1Labels = mixedMoment B raw27931step2 raw27931step2Labels := by
      have ha : raw27931step2 = raw27931step1 := by apply Matrix.ext; unfold raw27931step2 raw27931step1; decide +kernel
      have hl : raw27931step1Labels = labelEmbedding1 ∘ raw27931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27931step1 raw27931step1Labels raw27931step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical27932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27932 raw27932Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27932 raw27932Labels = mixedMoment B raw27932step0 raw27932step0Labels := by
      have hz : ∀ j, raw27932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27932step0 = (fun i j => raw27932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27932step0 raw27932; decide +kernel
      have hl : raw27932step0Labels = raw27932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27932 raw27932Labels permutation346 hz
    mixedMoment B raw27932step0 raw27932step0Labels = mixedMoment B raw27932step1 raw27932step1Labels := by
      have ha : raw27932step1 = (fun i j => raw27932step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27932step1 raw27932step0; decide +kernel
      have hl : raw27932step1Labels = raw27932step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27932step0 raw27932step0Labels permutation45 permutation5
    mixedMoment B raw27932step1 raw27932step1Labels = mixedMoment B raw27932step2 raw27932step2Labels := by
      have ha : raw27932step2 = -raw27932step1 := by apply Matrix.ext; change ∀ i j, raw27932step2 i j = -(raw27932step1 i j); unfold raw27932step2 raw27932step1; decide +kernel
      have hl : raw27932step2Labels = raw27932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27932step2 raw27932step2Labels = mixedMoment B raw27932step3 raw27932step3Labels := by
      have ha : raw27932step3 = raw27932step2 := by apply Matrix.ext; unfold raw27932step3 raw27932step2; decide +kernel
      have hl : raw27932step2Labels = labelEmbedding1 ∘ raw27932step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27932step2 raw27932step2Labels raw27932step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical27933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27933 raw27933Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw27933 raw27933Labels = mixedMoment B raw27933step0 raw27933step0Labels := by
      have hz : ∀ j, raw27933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27933step0 = (fun i j => raw27933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27933step0 raw27933; decide +kernel
      have hl : raw27933step0Labels = raw27933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27933 raw27933Labels permutation346 hz
    mixedMoment B raw27933step0 raw27933step0Labels = mixedMoment B raw27933step1 raw27933step1Labels := by
      have ha : raw27933step1 = (fun i j => raw27933step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27933step1 raw27933step0; decide +kernel
      have hl : raw27933step1Labels = raw27933step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27933step0 raw27933step0Labels permutation35 permutation5
    mixedMoment B raw27933step1 raw27933step1Labels = mixedMoment B raw27933step2 raw27933step2Labels := by
      have ha : raw27933step2 = -raw27933step1 := by apply Matrix.ext; change ∀ i j, raw27933step2 i j = -(raw27933step1 i j); unfold raw27933step2 raw27933step1; decide +kernel
      have hl : raw27933step2Labels = raw27933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27933step2 raw27933step2Labels = mixedMoment B raw27933step3 raw27933step3Labels := by
      have ha : raw27933step3 = raw27933step2 := by apply Matrix.ext; unfold raw27933step3 raw27933step2; decide +kernel
      have hl : raw27933step2Labels = labelEmbedding1 ∘ raw27933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27933step2 raw27933step2Labels raw27933step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical27934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27934 raw27934Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw27934 raw27934Labels = mixedMoment B raw27934step0 raw27934step0Labels := by
      have hz : ∀ j, raw27934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27934step0 = (fun i j => raw27934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27934step0 raw27934; decide +kernel
      have hl : raw27934step0Labels = raw27934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27934 raw27934Labels permutation346 hz
    mixedMoment B raw27934step0 raw27934step0Labels = mixedMoment B raw27934step1 raw27934step1Labels := by
      have ha : raw27934step1 = (fun i j => raw27934step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27934step1 raw27934step0; decide +kernel
      have hl : raw27934step1Labels = raw27934step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27934step0 raw27934step0Labels permutation32 permutation5
    mixedMoment B raw27934step1 raw27934step1Labels = mixedMoment B raw27934step2 raw27934step2Labels := by
      have ha : raw27934step2 = -raw27934step1 := by apply Matrix.ext; change ∀ i j, raw27934step2 i j = -(raw27934step1 i j); unfold raw27934step2 raw27934step1; decide +kernel
      have hl : raw27934step2Labels = raw27934step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27934step2 raw27934step2Labels = mixedMoment B raw27934step3 raw27934step3Labels := by
      have ha : raw27934step3 = raw27934step2 := by apply Matrix.ext; unfold raw27934step3 raw27934step2; decide +kernel
      have hl : raw27934step2Labels = labelEmbedding1 ∘ raw27934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27934step2 raw27934step2Labels raw27934step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical27935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27935 raw27935Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw27935 raw27935Labels = mixedMoment B raw27935step0 raw27935step0Labels := by
      have hz : ∀ j, raw27935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27935step0 = (fun i j => raw27935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27935step0 raw27935; decide +kernel
      have hl : raw27935step0Labels = raw27935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27935 raw27935Labels permutation346 hz
    mixedMoment B raw27935step0 raw27935step0Labels = mixedMoment B raw27935step1 raw27935step1Labels := by
      have ha : raw27935step1 = (fun i j => raw27935step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27935step1 raw27935step0; decide +kernel
      have hl : raw27935step1Labels = raw27935step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27935step0 raw27935step0Labels permutation32 permutation5
    mixedMoment B raw27935step1 raw27935step1Labels = mixedMoment B raw27935step2 raw27935step2Labels := by
      have ha : raw27935step2 = -raw27935step1 := by apply Matrix.ext; change ∀ i j, raw27935step2 i j = -(raw27935step1 i j); unfold raw27935step2 raw27935step1; decide +kernel
      have hl : raw27935step2Labels = raw27935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27935step2 raw27935step2Labels = mixedMoment B raw27935step3 raw27935step3Labels := by
      have ha : raw27935step3 = raw27935step2 := by apply Matrix.ext; unfold raw27935step3 raw27935step2; decide +kernel
      have hl : raw27935step2Labels = labelEmbedding1 ∘ raw27935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27935step2 raw27935step2Labels raw27935step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

theorem canonical27936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27936 raw27936Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw27936 raw27936Labels = mixedMoment B raw27936step0 raw27936step0Labels := by
      have ha : raw27936step0 = (fun i j => raw27936 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27936step0 raw27936; decide +kernel
      have hl : raw27936step0Labels = raw27936Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27936 raw27936Labels permutation682 permutation7
    mixedMoment B raw27936step0 raw27936step0Labels = mixedMoment B raw27936step1 raw27936step1Labels := by
      have ha : raw27936step1 = raw27936step0 := by apply Matrix.ext; unfold raw27936step1 raw27936step0; decide +kernel
      have hl : raw27936step0Labels = labelEmbedding1 ∘ raw27936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27936step0 raw27936step0Labels raw27936step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical27937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27937 raw27937Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw27937 raw27937Labels = mixedMoment B raw27937step0 raw27937step0Labels := by
      have hz : ∀ j, raw27937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27937step0 = (fun i j => raw27937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27937step0 raw27937; decide +kernel
      have hl : raw27937step0Labels = raw27937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27937 raw27937Labels permutation346 hz
    mixedMoment B raw27937step0 raw27937step0Labels = mixedMoment B raw27937step1 raw27937step1Labels := by
      have ha : raw27937step1 = (fun i j => raw27937step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27937step1 raw27937step0; decide +kernel
      have hl : raw27937step1Labels = raw27937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27937step0 raw27937step0Labels permutation149 permutation7
    mixedMoment B raw27937step1 raw27937step1Labels = mixedMoment B raw27937step2 raw27937step2Labels := by
      have ha : raw27937step2 = raw27937step1 := by apply Matrix.ext; unfold raw27937step2 raw27937step1; decide +kernel
      have hl : raw27937step1Labels = labelEmbedding1 ∘ raw27937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27937step1 raw27937step1Labels raw27937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

theorem canonical27938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27938 raw27938Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw27938 raw27938Labels = mixedMoment B raw27938step0 raw27938step0Labels := by
      have hz : ∀ j, raw27938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27938step0 = (fun i j => raw27938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27938step0 raw27938; decide +kernel
      have hl : raw27938step0Labels = raw27938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27938 raw27938Labels permutation346 hz
    mixedMoment B raw27938step0 raw27938step0Labels = mixedMoment B raw27938step1 raw27938step1Labels := by
      have ha : raw27938step1 = (fun i j => raw27938step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27938step1 raw27938step0; decide +kernel
      have hl : raw27938step1Labels = raw27938step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27938step0 raw27938step0Labels permutation36 permutation5
    mixedMoment B raw27938step1 raw27938step1Labels = mixedMoment B raw27938step2 raw27938step2Labels := by
      have ha : raw27938step2 = -raw27938step1 := by apply Matrix.ext; change ∀ i j, raw27938step2 i j = -(raw27938step1 i j); unfold raw27938step2 raw27938step1; decide +kernel
      have hl : raw27938step2Labels = raw27938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27938step2 raw27938step2Labels = mixedMoment B raw27938step3 raw27938step3Labels := by
      have ha : raw27938step3 = raw27938step2 := by apply Matrix.ext; unfold raw27938step3 raw27938step2; decide +kernel
      have hl : raw27938step2Labels = labelEmbedding1 ∘ raw27938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27938step2 raw27938step2Labels raw27938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical27939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27939 raw27939Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw27939 raw27939Labels = mixedMoment B raw27939step0 raw27939step0Labels := by
      have hz : ∀ j, raw27939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27939step0 = (fun i j => raw27939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27939step0 raw27939; decide +kernel
      have hl : raw27939step0Labels = raw27939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27939 raw27939Labels permutation346 hz
    mixedMoment B raw27939step0 raw27939step0Labels = mixedMoment B raw27939step1 raw27939step1Labels := by
      have ha : raw27939step1 = (fun i j => raw27939step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27939step1 raw27939step0; decide +kernel
      have hl : raw27939step1Labels = raw27939step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27939step0 raw27939step0Labels permutation34 permutation5
    mixedMoment B raw27939step1 raw27939step1Labels = mixedMoment B raw27939step2 raw27939step2Labels := by
      have ha : raw27939step2 = -raw27939step1 := by apply Matrix.ext; change ∀ i j, raw27939step2 i j = -(raw27939step1 i j); unfold raw27939step2 raw27939step1; decide +kernel
      have hl : raw27939step2Labels = raw27939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27939step2 raw27939step2Labels = mixedMoment B raw27939step3 raw27939step3Labels := by
      have ha : raw27939step3 = raw27939step2 := by apply Matrix.ext; unfold raw27939step3 raw27939step2; decide +kernel
      have hl : raw27939step2Labels = labelEmbedding1 ∘ raw27939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27939step2 raw27939step2Labels raw27939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical27940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27940 raw27940Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw27940 raw27940Labels = mixedMoment B raw27940step0 raw27940step0Labels := by
      have hz : ∀ j, raw27940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27940step0 = (fun i j => raw27940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27940step0 raw27940; decide +kernel
      have hl : raw27940step0Labels = raw27940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27940 raw27940Labels permutation346 hz
    mixedMoment B raw27940step0 raw27940step0Labels = mixedMoment B raw27940step1 raw27940step1Labels := by
      have ha : raw27940step1 = (fun i j => raw27940step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27940step1 raw27940step0; decide +kernel
      have hl : raw27940step1Labels = raw27940step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27940step0 raw27940step0Labels permutation151 permutation7
    mixedMoment B raw27940step1 raw27940step1Labels = mixedMoment B raw27940step2 raw27940step2Labels := by
      have ha : raw27940step2 = raw27940step1 := by apply Matrix.ext; unfold raw27940step2 raw27940step1; decide +kernel
      have hl : raw27940step1Labels = labelEmbedding1 ∘ raw27940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27940step1 raw27940step1Labels raw27940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical27941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27941 raw27941Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw27941 raw27941Labels = mixedMoment B raw27941step0 raw27941step0Labels := by
      have ha : raw27941step0 = (fun i j => raw27941 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27941step0 raw27941; decide +kernel
      have hl : raw27941step0Labels = raw27941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27941 raw27941Labels permutation682 permutation7
    mixedMoment B raw27941step0 raw27941step0Labels = mixedMoment B raw27941step1 raw27941step1Labels := by
      have ha : raw27941step1 = raw27941step0 := by apply Matrix.ext; unfold raw27941step1 raw27941step0; decide +kernel
      have hl : raw27941step0Labels = labelEmbedding1 ∘ raw27941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27941step0 raw27941step0Labels raw27941step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

theorem canonical27942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27942 raw27942Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw27942 raw27942Labels = mixedMoment B raw27942step0 raw27942step0Labels := by
      have hz : ∀ j, raw27942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27942step0 = (fun i j => raw27942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27942step0 raw27942; decide +kernel
      have hl : raw27942step0Labels = raw27942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27942 raw27942Labels permutation346 hz
    mixedMoment B raw27942step0 raw27942step0Labels = mixedMoment B raw27942step1 raw27942step1Labels := by
      have ha : raw27942step1 = (fun i j => raw27942step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27942step1 raw27942step0; decide +kernel
      have hl : raw27942step1Labels = raw27942step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27942step0 raw27942step0Labels permutation149 permutation7
    mixedMoment B raw27942step1 raw27942step1Labels = mixedMoment B raw27942step2 raw27942step2Labels := by
      have ha : raw27942step2 = raw27942step1 := by apply Matrix.ext; unfold raw27942step2 raw27942step1; decide +kernel
      have hl : raw27942step1Labels = labelEmbedding1 ∘ raw27942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27942step1 raw27942step1Labels raw27942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

theorem canonical27943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27943 raw27943Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw27943 raw27943Labels = mixedMoment B raw27943step0 raw27943step0Labels := by
      have hz : ∀ j, raw27943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27943step0 = (fun i j => raw27943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27943step0 raw27943; decide +kernel
      have hl : raw27943step0Labels = raw27943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27943 raw27943Labels permutation346 hz
    mixedMoment B raw27943step0 raw27943step0Labels = mixedMoment B raw27943step1 raw27943step1Labels := by
      have ha : raw27943step1 = (fun i j => raw27943step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27943step1 raw27943step0; decide +kernel
      have hl : raw27943step1Labels = raw27943step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27943step0 raw27943step0Labels permutation143 permutation5
    mixedMoment B raw27943step1 raw27943step1Labels = mixedMoment B raw27943step2 raw27943step2Labels := by
      have ha : raw27943step2 = raw27943step1 := by apply Matrix.ext; unfold raw27943step2 raw27943step1; decide +kernel
      have hl : raw27943step1Labels = labelEmbedding1 ∘ raw27943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27943step1 raw27943step1Labels raw27943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical27944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27944 raw27944Labels = mixedMoment B node2514 node2514Labels := by
  calc
    mixedMoment B raw27944 raw27944Labels = mixedMoment B raw27944step0 raw27944step0Labels := by
      have hz : ∀ j, raw27944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27944step0 = (fun i j => raw27944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27944step0 raw27944; decide +kernel
      have hl : raw27944step0Labels = raw27944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27944 raw27944Labels permutation346 hz
    mixedMoment B raw27944step0 raw27944step0Labels = mixedMoment B raw27944step1 raw27944step1Labels := by
      have ha : raw27944step1 = (fun i j => raw27944step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27944step1 raw27944step0; decide +kernel
      have hl : raw27944step1Labels = raw27944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27944step0 raw27944step0Labels permutation149 permutation2
    mixedMoment B raw27944step1 raw27944step1Labels = mixedMoment B raw27944step2 raw27944step2Labels := by
      have ha : raw27944step2 = -raw27944step1 := by apply Matrix.ext; change ∀ i j, raw27944step2 i j = -(raw27944step1 i j); unfold raw27944step2 raw27944step1; decide +kernel
      have hl : raw27944step2Labels = raw27944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2514 node2514Labels := by rfl

theorem canonical27945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27945 raw27945Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27945 raw27945Labels = mixedMoment B raw27945step0 raw27945step0Labels := by
      have hz : ∀ j, raw27945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27945step0 = (fun i j => raw27945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27945step0 raw27945; decide +kernel
      have hl : raw27945step0Labels = raw27945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27945 raw27945Labels permutation346 hz
    mixedMoment B raw27945step0 raw27945step0Labels = mixedMoment B raw27945step1 raw27945step1Labels := by
      have ha : raw27945step1 = (fun i j => raw27945step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27945step1 raw27945step0; decide +kernel
      have hl : raw27945step1Labels = raw27945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27945step0 raw27945step0Labels permutation149 permutation2
    mixedMoment B raw27945step1 raw27945step1Labels = mixedMoment B raw27945step2 raw27945step2Labels := by
      have ha : raw27945step2 = -raw27945step1 := by apply Matrix.ext; change ∀ i j, raw27945step2 i j = -(raw27945step1 i j); unfold raw27945step2 raw27945step1; decide +kernel
      have hl : raw27945step2Labels = raw27945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical27946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27946 raw27946Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27946 raw27946Labels = mixedMoment B raw27946step0 raw27946step0Labels := by
      have ha : raw27946step0 = (fun i j => raw27946 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27946step0 raw27946; decide +kernel
      have hl : raw27946step0Labels = raw27946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27946 raw27946Labels permutation680 permutation2
    mixedMoment B raw27946step0 raw27946step0Labels = mixedMoment B raw27946step1 raw27946step1Labels := by
      have ha : raw27946step1 = -raw27946step0 := by apply Matrix.ext; change ∀ i j, raw27946step1 i j = -(raw27946step0 i j); unfold raw27946step1 raw27946step0; decide +kernel
      have hl : raw27946step1Labels = raw27946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical27947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27947 raw27947Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27947 raw27947Labels = mixedMoment B raw27947step0 raw27947step0Labels := by
      have hz : ∀ j, raw27947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27947step0 = (fun i j => raw27947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27947step0 raw27947; decide +kernel
      have hl : raw27947step0Labels = raw27947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27947 raw27947Labels permutation346 hz
    mixedMoment B raw27947step0 raw27947step0Labels = mixedMoment B raw27947step1 raw27947step1Labels := by
      have ha : raw27947step1 = (fun i j => raw27947step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27947step1 raw27947step0; decide +kernel
      have hl : raw27947step1Labels = raw27947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27947step0 raw27947step0Labels permutation151 permutation2
    mixedMoment B raw27947step1 raw27947step1Labels = mixedMoment B raw27947step2 raw27947step2Labels := by
      have ha : raw27947step2 = -raw27947step1 := by apply Matrix.ext; change ∀ i j, raw27947step2 i j = -(raw27947step1 i j); unfold raw27947step2 raw27947step1; decide +kernel
      have hl : raw27947step2Labels = raw27947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical27948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27948 raw27948Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw27948 raw27948Labels = mixedMoment B raw27948step0 raw27948step0Labels := by
      have hz : ∀ j, raw27948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27948step0 = (fun i j => raw27948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27948step0 raw27948; decide +kernel
      have hl : raw27948step0Labels = raw27948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27948 raw27948Labels permutation346 hz
    mixedMoment B raw27948step0 raw27948step0Labels = mixedMoment B raw27948step1 raw27948step1Labels := by
      have ha : raw27948step1 = (fun i j => raw27948step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27948step1 raw27948step0; decide +kernel
      have hl : raw27948step1Labels = raw27948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27948step0 raw27948step0Labels permutation149 permutation2
    mixedMoment B raw27948step1 raw27948step1Labels = mixedMoment B raw27948step2 raw27948step2Labels := by
      have ha : raw27948step2 = -raw27948step1 := by apply Matrix.ext; change ∀ i j, raw27948step2 i j = -(raw27948step1 i j); unfold raw27948step2 raw27948step1; decide +kernel
      have hl : raw27948step2Labels = raw27948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical27949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27949 raw27949Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw27949 raw27949Labels = mixedMoment B raw27949step0 raw27949step0Labels := by
      have hz : ∀ j, raw27949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27949step0 = (fun i j => raw27949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27949step0 raw27949; decide +kernel
      have hl : raw27949step0Labels = raw27949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27949 raw27949Labels permutation346 hz
    mixedMoment B raw27949step0 raw27949step0Labels = mixedMoment B raw27949step1 raw27949step1Labels := by
      have ha : raw27949step1 = (fun i j => raw27949step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27949step1 raw27949step0; decide +kernel
      have hl : raw27949step1Labels = raw27949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27949step0 raw27949step0Labels permutation149 permutation2
    mixedMoment B raw27949step1 raw27949step1Labels = mixedMoment B raw27949step2 raw27949step2Labels := by
      have ha : raw27949step2 = -raw27949step1 := by apply Matrix.ext; change ∀ i j, raw27949step2 i j = -(raw27949step1 i j); unfold raw27949step2 raw27949step1; decide +kernel
      have hl : raw27949step2Labels = raw27949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1136 node1136Labels := by rfl

theorem canonical27950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27950 raw27950Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw27950 raw27950Labels = mixedMoment B raw27950step0 raw27950step0Labels := by
      have hz : ∀ j, raw27950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27950step0 = (fun i j => raw27950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27950step0 raw27950; decide +kernel
      have hl : raw27950step0Labels = raw27950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27950 raw27950Labels permutation346 hz
    mixedMoment B raw27950step0 raw27950step0Labels = mixedMoment B raw27950step1 raw27950step1Labels := by
      have ha : raw27950step1 = (fun i j => raw27950step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27950step1 raw27950step0; decide +kernel
      have hl : raw27950step1Labels = raw27950step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27950step0 raw27950step0Labels permutation146 permutation0
    mixedMoment B raw27950step1 raw27950step1Labels = mixedMoment B raw27950step2 raw27950step2Labels := by
      have ha : raw27950step2 = -raw27950step1 := by apply Matrix.ext; change ∀ i j, raw27950step2 i j = -(raw27950step1 i j); unfold raw27950step2 raw27950step1; decide +kernel
      have hl : raw27950step2Labels = raw27950step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28080 raw28080Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw28080 raw28080Labels = mixedMoment B raw28080step0 raw28080step0Labels := by
      have hz : ∀ j, raw28080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28080step0 = (fun i j => raw28080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28080step0 raw28080; decide +kernel
      have hl : raw28080step0Labels = raw28080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28080 raw28080Labels permutation346 hz
    mixedMoment B raw28080step0 raw28080step0Labels = mixedMoment B raw28080step1 raw28080step1Labels := by
      have ha : raw28080step1 = (fun i j => raw28080step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28080step1 raw28080step0; decide +kernel
      have hl : raw28080step1Labels = raw28080step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28080step0 raw28080step0Labels permutation150 permutation7
    mixedMoment B raw28080step1 raw28080step1Labels = mixedMoment B raw28080step2 raw28080step2Labels := by
      have ha : raw28080step2 = raw28080step1 := by apply Matrix.ext; unfold raw28080step2 raw28080step1; decide +kernel
      have hl : raw28080step1Labels = labelEmbedding1 ∘ raw28080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28080step1 raw28080step1Labels raw28080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical28081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28081 raw28081Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw28081 raw28081Labels = mixedMoment B raw28081step0 raw28081step0Labels := by
      have ha : raw28081step0 = (fun i j => raw28081 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28081step0 raw28081; decide +kernel
      have hl : raw28081step0Labels = raw28081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28081 raw28081Labels permutation682 permutation7
    mixedMoment B raw28081step0 raw28081step0Labels = mixedMoment B raw28081step1 raw28081step1Labels := by
      have ha : raw28081step1 = raw28081step0 := by apply Matrix.ext; unfold raw28081step1 raw28081step0; decide +kernel
      have hl : raw28081step0Labels = labelEmbedding1 ∘ raw28081step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28081step0 raw28081step0Labels raw28081step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical28082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28082 raw28082Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw28082 raw28082Labels = mixedMoment B raw28082step0 raw28082step0Labels := by
      have hz : ∀ j, raw28082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28082step0 = (fun i j => raw28082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28082step0 raw28082; decide +kernel
      have hl : raw28082step0Labels = raw28082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28082 raw28082Labels permutation346 hz
    mixedMoment B raw28082step0 raw28082step0Labels = mixedMoment B raw28082step1 raw28082step1Labels := by
      have ha : raw28082step1 = (fun i j => raw28082step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28082step1 raw28082step0; decide +kernel
      have hl : raw28082step1Labels = raw28082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28082step0 raw28082step0Labels permutation149 permutation7
    mixedMoment B raw28082step1 raw28082step1Labels = mixedMoment B raw28082step2 raw28082step2Labels := by
      have ha : raw28082step2 = raw28082step1 := by apply Matrix.ext; unfold raw28082step2 raw28082step1; decide +kernel
      have hl : raw28082step1Labels = labelEmbedding1 ∘ raw28082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28082step1 raw28082step1Labels raw28082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical28083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28083 raw28083Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw28083 raw28083Labels = mixedMoment B raw28083step0 raw28083step0Labels := by
      have hz : ∀ j, raw28083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28083step0 = (fun i j => raw28083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28083step0 raw28083; decide +kernel
      have hl : raw28083step0Labels = raw28083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28083 raw28083Labels permutation520 hz
    mixedMoment B raw28083step0 raw28083step0Labels = mixedMoment B raw28083step1 raw28083step1Labels := by
      have hz : ∀ j, raw28083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28083step1 = (fun i j => raw28083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28083step1 raw28083step0; decide +kernel
      have hl : raw28083step1Labels = raw28083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28083step0 raw28083step0Labels permutation80 hz
    mixedMoment B raw28083step1 raw28083step1Labels = mixedMoment B raw28083step2 raw28083step2Labels := by
      have ha : raw28083step2 = (fun i j => raw28083step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28083step2 raw28083step1; decide +kernel
      have hl : raw28083step2Labels = raw28083step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28083step1 raw28083step1Labels permutation31 permutation7
    mixedMoment B raw28083step2 raw28083step2Labels = mixedMoment B raw28083step3 raw28083step3Labels := by
      have ha : raw28083step3 = raw28083step2 := by apply Matrix.ext; unfold raw28083step3 raw28083step2; decide +kernel
      have hl : raw28083step2Labels = labelEmbedding1 ∘ raw28083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28083step2 raw28083step2Labels raw28083step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical28084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28084 raw28084Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw28084 raw28084Labels = mixedMoment B raw28084step0 raw28084step0Labels := by
      have hz : ∀ j, raw28084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28084step0 = (fun i j => raw28084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28084step0 raw28084; decide +kernel
      have hl : raw28084step0Labels = raw28084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28084 raw28084Labels permutation346 hz
    mixedMoment B raw28084step0 raw28084step0Labels = mixedMoment B raw28084step1 raw28084step1Labels := by
      have ha : raw28084step1 = (fun i j => raw28084step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28084step1 raw28084step0; decide +kernel
      have hl : raw28084step1Labels = raw28084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28084step0 raw28084step0Labels permutation151 permutation7
    mixedMoment B raw28084step1 raw28084step1Labels = mixedMoment B raw28084step2 raw28084step2Labels := by
      have ha : raw28084step2 = raw28084step1 := by apply Matrix.ext; unfold raw28084step2 raw28084step1; decide +kernel
      have hl : raw28084step1Labels = labelEmbedding1 ∘ raw28084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28084step1 raw28084step1Labels raw28084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical28085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28085 raw28085Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw28085 raw28085Labels = mixedMoment B raw28085step0 raw28085step0Labels := by
      have hz : ∀ j, raw28085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28085step0 = (fun i j => raw28085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28085step0 raw28085; decide +kernel
      have hl : raw28085step0Labels = raw28085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28085 raw28085Labels permutation346 hz
    mixedMoment B raw28085step0 raw28085step0Labels = mixedMoment B raw28085step1 raw28085step1Labels := by
      have ha : raw28085step1 = (fun i j => raw28085step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28085step1 raw28085step0; decide +kernel
      have hl : raw28085step1Labels = raw28085step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28085step0 raw28085step0Labels permutation50 permutation5
    mixedMoment B raw28085step1 raw28085step1Labels = mixedMoment B raw28085step2 raw28085step2Labels := by
      have ha : raw28085step2 = -raw28085step1 := by apply Matrix.ext; change ∀ i j, raw28085step2 i j = -(raw28085step1 i j); unfold raw28085step2 raw28085step1; decide +kernel
      have hl : raw28085step2Labels = raw28085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28085step2 raw28085step2Labels = mixedMoment B raw28085step3 raw28085step3Labels := by
      have ha : raw28085step3 = raw28085step2 := by apply Matrix.ext; unfold raw28085step3 raw28085step2; decide +kernel
      have hl : raw28085step2Labels = labelEmbedding1 ∘ raw28085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28085step2 raw28085step2Labels raw28085step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical28086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28086 raw28086Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw28086 raw28086Labels = mixedMoment B raw28086step0 raw28086step0Labels := by
      have ha : raw28086step0 = (fun i j => raw28086 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28086step0 raw28086; decide +kernel
      have hl : raw28086step0Labels = raw28086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28086 raw28086Labels permutation680 permutation7
    mixedMoment B raw28086step0 raw28086step0Labels = mixedMoment B raw28086step1 raw28086step1Labels := by
      have ha : raw28086step1 = raw28086step0 := by apply Matrix.ext; unfold raw28086step1 raw28086step0; decide +kernel
      have hl : raw28086step0Labels = labelEmbedding1 ∘ raw28086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28086step0 raw28086step0Labels raw28086step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical28087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28087 raw28087Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw28087 raw28087Labels = mixedMoment B raw28087step0 raw28087step0Labels := by
      have hz : ∀ j, raw28087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28087step0 = (fun i j => raw28087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28087step0 raw28087; decide +kernel
      have hl : raw28087step0Labels = raw28087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28087 raw28087Labels permutation346 hz
    mixedMoment B raw28087step0 raw28087step0Labels = mixedMoment B raw28087step1 raw28087step1Labels := by
      have ha : raw28087step1 = (fun i j => raw28087step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28087step1 raw28087step0; decide +kernel
      have hl : raw28087step1Labels = raw28087step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28087step0 raw28087step0Labels permutation149 permutation7
    mixedMoment B raw28087step1 raw28087step1Labels = mixedMoment B raw28087step2 raw28087step2Labels := by
      have ha : raw28087step2 = raw28087step1 := by apply Matrix.ext; unfold raw28087step2 raw28087step1; decide +kernel
      have hl : raw28087step1Labels = labelEmbedding1 ∘ raw28087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28087step1 raw28087step1Labels raw28087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical28088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28088 raw28088Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw28088 raw28088Labels = mixedMoment B raw28088step0 raw28088step0Labels := by
      have hz : ∀ j, raw28088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28088step0 = (fun i j => raw28088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28088step0 raw28088; decide +kernel
      have hl : raw28088step0Labels = raw28088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28088 raw28088Labels permutation520 hz
    mixedMoment B raw28088step0 raw28088step0Labels = mixedMoment B raw28088step1 raw28088step1Labels := by
      have hz : ∀ j, raw28088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28088step1 = (fun i j => raw28088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28088step1 raw28088step0; decide +kernel
      have hl : raw28088step1Labels = raw28088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28088step0 raw28088step0Labels permutation80 hz
    mixedMoment B raw28088step1 raw28088step1Labels = mixedMoment B raw28088step2 raw28088step2Labels := by
      have ha : raw28088step2 = (fun i j => raw28088step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28088step2 raw28088step1; decide +kernel
      have hl : raw28088step2Labels = raw28088step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28088step1 raw28088step1Labels permutation29 permutation7
    mixedMoment B raw28088step2 raw28088step2Labels = mixedMoment B raw28088step3 raw28088step3Labels := by
      have ha : raw28088step3 = raw28088step2 := by apply Matrix.ext; unfold raw28088step3 raw28088step2; decide +kernel
      have hl : raw28088step2Labels = labelEmbedding1 ∘ raw28088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28088step2 raw28088step2Labels raw28088step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical28089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28089 raw28089Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw28089 raw28089Labels = mixedMoment B raw28089step0 raw28089step0Labels := by
      have hz : ∀ j, raw28089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28089step0 = (fun i j => raw28089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28089step0 raw28089; decide +kernel
      have hl : raw28089step0Labels = raw28089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28089 raw28089Labels permutation346 hz
    mixedMoment B raw28089step0 raw28089step0Labels = mixedMoment B raw28089step1 raw28089step1Labels := by
      have ha : raw28089step1 = (fun i j => raw28089step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28089step1 raw28089step0; decide +kernel
      have hl : raw28089step1Labels = raw28089step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28089step0 raw28089step0Labels permutation149 permutation7
    mixedMoment B raw28089step1 raw28089step1Labels = mixedMoment B raw28089step2 raw28089step2Labels := by
      have ha : raw28089step2 = raw28089step1 := by apply Matrix.ext; unfold raw28089step2 raw28089step1; decide +kernel
      have hl : raw28089step1Labels = labelEmbedding1 ∘ raw28089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28089step1 raw28089step1Labels raw28089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical28090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28090 raw28090Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw28090 raw28090Labels = mixedMoment B raw28090step0 raw28090step0Labels := by
      have ha : raw28090step0 = (fun i j => raw28090 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28090step0 raw28090; decide +kernel
      have hl : raw28090step0Labels = raw28090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28090 raw28090Labels permutation172 permutation5
    mixedMoment B raw28090step0 raw28090step0Labels = mixedMoment B raw28090step1 raw28090step1Labels := by
      have ha : raw28090step1 = -raw28090step0 := by apply Matrix.ext; change ∀ i j, raw28090step1 i j = -(raw28090step0 i j); unfold raw28090step1 raw28090step0; decide +kernel
      have hl : raw28090step1Labels = raw28090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28090step1 raw28090step1Labels = mixedMoment B raw28090step2 raw28090step2Labels := by
      have ha : raw28090step2 = raw28090step1 := by apply Matrix.ext; unfold raw28090step2 raw28090step1; decide +kernel
      have hl : raw28090step1Labels = labelEmbedding1 ∘ raw28090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28090step1 raw28090step1Labels raw28090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

theorem canonical28091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28091 raw28091Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw28091 raw28091Labels = mixedMoment B raw28091step0 raw28091step0Labels := by
      have ha : raw28091step0 = (fun i j => raw28091 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28091step0 raw28091; decide +kernel
      have hl : raw28091step0Labels = raw28091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28091 raw28091Labels permutation646 permutation7
    mixedMoment B raw28091step0 raw28091step0Labels = mixedMoment B raw28091step1 raw28091step1Labels := by
      have ha : raw28091step1 = raw28091step0 := by apply Matrix.ext; unfold raw28091step1 raw28091step0; decide +kernel
      have hl : raw28091step0Labels = labelEmbedding1 ∘ raw28091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28091step0 raw28091step0Labels raw28091step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical28092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28092 raw28092Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw28092 raw28092Labels = mixedMoment B raw28092step0 raw28092step0Labels := by
      have ha : raw28092step0 = (fun i j => raw28092 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28092step0 raw28092; decide +kernel
      have hl : raw28092step0Labels = raw28092Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28092 raw28092Labels permutation644 permutation7
    mixedMoment B raw28092step0 raw28092step0Labels = mixedMoment B raw28092step1 raw28092step1Labels := by
      have ha : raw28092step1 = raw28092step0 := by apply Matrix.ext; unfold raw28092step1 raw28092step0; decide +kernel
      have hl : raw28092step0Labels = labelEmbedding1 ∘ raw28092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28092step0 raw28092step0Labels raw28092step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

theorem canonical28093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28093 raw28093Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw28093 raw28093Labels = mixedMoment B raw28093step0 raw28093step0Labels := by
      have hz : ∀ j, raw28093 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28093step0 = (fun i j => raw28093 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28093step0 raw28093; decide +kernel
      have hl : raw28093step0Labels = raw28093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28093 raw28093Labels permutation520 hz
    mixedMoment B raw28093step0 raw28093step0Labels = mixedMoment B raw28093step1 raw28093step1Labels := by
      have ha : raw28093step1 = (fun i j => raw28093step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28093step1 raw28093step0; decide +kernel
      have hl : raw28093step1Labels = raw28093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28093step0 raw28093step0Labels permutation145 permutation7
    mixedMoment B raw28093step1 raw28093step1Labels = mixedMoment B raw28093step2 raw28093step2Labels := by
      have ha : raw28093step2 = raw28093step1 := by apply Matrix.ext; unfold raw28093step2 raw28093step1; decide +kernel
      have hl : raw28093step1Labels = labelEmbedding1 ∘ raw28093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28093step1 raw28093step1Labels raw28093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical28094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28094 raw28094Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw28094 raw28094Labels = mixedMoment B raw28094step0 raw28094step0Labels := by
      have ha : raw28094step0 = (fun i j => raw28094 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28094step0 raw28094; decide +kernel
      have hl : raw28094step0Labels = raw28094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28094 raw28094Labels permutation646 permutation7
    mixedMoment B raw28094step0 raw28094step0Labels = mixedMoment B raw28094step1 raw28094step1Labels := by
      have ha : raw28094step1 = raw28094step0 := by apply Matrix.ext; unfold raw28094step1 raw28094step0; decide +kernel
      have hl : raw28094step0Labels = labelEmbedding1 ∘ raw28094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28094step0 raw28094step0Labels raw28094step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

theorem canonical28095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28095 raw28095Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw28095 raw28095Labels = mixedMoment B raw28095step0 raw28095step0Labels := by
      have hz : ∀ j, raw28095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28095step0 = (fun i j => raw28095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28095step0 raw28095; decide +kernel
      have hl : raw28095step0Labels = raw28095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28095 raw28095Labels permutation346 hz
    mixedMoment B raw28095step0 raw28095step0Labels = mixedMoment B raw28095step1 raw28095step1Labels := by
      have ha : raw28095step1 = (fun i j => raw28095step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28095step1 raw28095step0; decide +kernel
      have hl : raw28095step1Labels = raw28095step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28095step0 raw28095step0Labels permutation37 permutation5
    mixedMoment B raw28095step1 raw28095step1Labels = mixedMoment B raw28095step2 raw28095step2Labels := by
      have ha : raw28095step2 = -raw28095step1 := by apply Matrix.ext; change ∀ i j, raw28095step2 i j = -(raw28095step1 i j); unfold raw28095step2 raw28095step1; decide +kernel
      have hl : raw28095step2Labels = raw28095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28095step2 raw28095step2Labels = mixedMoment B raw28095step3 raw28095step3Labels := by
      have ha : raw28095step3 = raw28095step2 := by apply Matrix.ext; unfold raw28095step3 raw28095step2; decide +kernel
      have hl : raw28095step2Labels = labelEmbedding1 ∘ raw28095step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28095step2 raw28095step2Labels raw28095step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical28096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28096 raw28096Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw28096 raw28096Labels = mixedMoment B raw28096step0 raw28096step0Labels := by
      have hz : ∀ j, raw28096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28096step0 = (fun i j => raw28096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28096step0 raw28096; decide +kernel
      have hl : raw28096step0Labels = raw28096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28096 raw28096Labels permutation346 hz
    mixedMoment B raw28096step0 raw28096step0Labels = mixedMoment B raw28096step1 raw28096step1Labels := by
      have ha : raw28096step1 = (fun i j => raw28096step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28096step1 raw28096step0; decide +kernel
      have hl : raw28096step1Labels = raw28096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28096step0 raw28096step0Labels permutation151 permutation7
    mixedMoment B raw28096step1 raw28096step1Labels = mixedMoment B raw28096step2 raw28096step2Labels := by
      have ha : raw28096step2 = raw28096step1 := by apply Matrix.ext; unfold raw28096step2 raw28096step1; decide +kernel
      have hl : raw28096step1Labels = labelEmbedding1 ∘ raw28096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28096step1 raw28096step1Labels raw28096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical28097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28097 raw28097Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw28097 raw28097Labels = mixedMoment B raw28097step0 raw28097step0Labels := by
      have ha : raw28097step0 = (fun i j => raw28097 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28097step0 raw28097; decide +kernel
      have hl : raw28097step0Labels = raw28097Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28097 raw28097Labels permutation682 permutation7
    mixedMoment B raw28097step0 raw28097step0Labels = mixedMoment B raw28097step1 raw28097step1Labels := by
      have ha : raw28097step1 = raw28097step0 := by apply Matrix.ext; unfold raw28097step1 raw28097step0; decide +kernel
      have hl : raw28097step0Labels = labelEmbedding1 ∘ raw28097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28097step0 raw28097step0Labels raw28097step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical28098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28098 raw28098Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw28098 raw28098Labels = mixedMoment B raw28098step0 raw28098step0Labels := by
      have hz : ∀ j, raw28098 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28098step0 = (fun i j => raw28098 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28098step0 raw28098; decide +kernel
      have hl : raw28098step0Labels = raw28098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28098 raw28098Labels permutation520 hz
    mixedMoment B raw28098step0 raw28098step0Labels = mixedMoment B raw28098step1 raw28098step1Labels := by
      have hz : ∀ j, raw28098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28098step1 = (fun i j => raw28098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28098step1 raw28098step0; decide +kernel
      have hl : raw28098step1Labels = raw28098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28098step0 raw28098step0Labels permutation80 hz
    mixedMoment B raw28098step1 raw28098step1Labels = mixedMoment B raw28098step2 raw28098step2Labels := by
      have ha : raw28098step2 = (fun i j => raw28098step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28098step2 raw28098step1; decide +kernel
      have hl : raw28098step2Labels = raw28098step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28098step1 raw28098step1Labels permutation31 permutation7
    mixedMoment B raw28098step2 raw28098step2Labels = mixedMoment B raw28098step3 raw28098step3Labels := by
      have ha : raw28098step3 = raw28098step2 := by apply Matrix.ext; unfold raw28098step3 raw28098step2; decide +kernel
      have hl : raw28098step2Labels = labelEmbedding1 ∘ raw28098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28098step2 raw28098step2Labels raw28098step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical28099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28099 raw28099Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw28099 raw28099Labels = mixedMoment B raw28099step0 raw28099step0Labels := by
      have hz : ∀ j, raw28099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28099step0 = (fun i j => raw28099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28099step0 raw28099; decide +kernel
      have hl : raw28099step0Labels = raw28099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28099 raw28099Labels permutation346 hz
    mixedMoment B raw28099step0 raw28099step0Labels = mixedMoment B raw28099step1 raw28099step1Labels := by
      have ha : raw28099step1 = (fun i j => raw28099step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28099step1 raw28099step0; decide +kernel
      have hl : raw28099step1Labels = raw28099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28099step0 raw28099step0Labels permutation151 permutation7
    mixedMoment B raw28099step1 raw28099step1Labels = mixedMoment B raw28099step2 raw28099step2Labels := by
      have ha : raw28099step2 = raw28099step1 := by apply Matrix.ext; unfold raw28099step2 raw28099step1; decide +kernel
      have hl : raw28099step1Labels = labelEmbedding1 ∘ raw28099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28099step1 raw28099step1Labels raw28099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical28100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28100 raw28100Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw28100 raw28100Labels = mixedMoment B raw28100step0 raw28100step0Labels := by
      have hz : ∀ j, raw28100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28100step0 = (fun i j => raw28100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28100step0 raw28100; decide +kernel
      have hl : raw28100step0Labels = raw28100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28100 raw28100Labels permutation346 hz
    mixedMoment B raw28100step0 raw28100step0Labels = mixedMoment B raw28100step1 raw28100step1Labels := by
      have ha : raw28100step1 = (fun i j => raw28100step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28100step1 raw28100step0; decide +kernel
      have hl : raw28100step1Labels = raw28100step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28100step0 raw28100step0Labels permutation36 permutation5
    mixedMoment B raw28100step1 raw28100step1Labels = mixedMoment B raw28100step2 raw28100step2Labels := by
      have ha : raw28100step2 = -raw28100step1 := by apply Matrix.ext; change ∀ i j, raw28100step2 i j = -(raw28100step1 i j); unfold raw28100step2 raw28100step1; decide +kernel
      have hl : raw28100step2Labels = raw28100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28100step2 raw28100step2Labels = mixedMoment B raw28100step3 raw28100step3Labels := by
      have ha : raw28100step3 = raw28100step2 := by apply Matrix.ext; unfold raw28100step3 raw28100step2; decide +kernel
      have hl : raw28100step2Labels = labelEmbedding1 ∘ raw28100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28100step2 raw28100step2Labels raw28100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical28101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28101 raw28101Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw28101 raw28101Labels = mixedMoment B raw28101step0 raw28101step0Labels := by
      have hz : ∀ j, raw28101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28101step0 = (fun i j => raw28101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28101step0 raw28101; decide +kernel
      have hl : raw28101step0Labels = raw28101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28101 raw28101Labels permutation346 hz
    mixedMoment B raw28101step0 raw28101step0Labels = mixedMoment B raw28101step1 raw28101step1Labels := by
      have ha : raw28101step1 = (fun i j => raw28101step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28101step1 raw28101step0; decide +kernel
      have hl : raw28101step1Labels = raw28101step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28101step0 raw28101step0Labels permutation151 permutation7
    mixedMoment B raw28101step1 raw28101step1Labels = mixedMoment B raw28101step2 raw28101step2Labels := by
      have ha : raw28101step2 = raw28101step1 := by apply Matrix.ext; unfold raw28101step2 raw28101step1; decide +kernel
      have hl : raw28101step1Labels = labelEmbedding1 ∘ raw28101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28101step1 raw28101step1Labels raw28101step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical28102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28102 raw28102Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw28102 raw28102Labels = mixedMoment B raw28102step0 raw28102step0Labels := by
      have ha : raw28102step0 = (fun i j => raw28102 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28102step0 raw28102; decide +kernel
      have hl : raw28102step0Labels = raw28102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28102 raw28102Labels permutation682 permutation7
    mixedMoment B raw28102step0 raw28102step0Labels = mixedMoment B raw28102step1 raw28102step1Labels := by
      have ha : raw28102step1 = raw28102step0 := by apply Matrix.ext; unfold raw28102step1 raw28102step0; decide +kernel
      have hl : raw28102step0Labels = labelEmbedding1 ∘ raw28102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28102step0 raw28102step0Labels raw28102step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical28103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28103 raw28103Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw28103 raw28103Labels = mixedMoment B raw28103step0 raw28103step0Labels := by
      have hz : ∀ j, raw28103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28103step0 = (fun i j => raw28103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28103step0 raw28103; decide +kernel
      have hl : raw28103step0Labels = raw28103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28103 raw28103Labels permutation346 hz
    mixedMoment B raw28103step0 raw28103step0Labels = mixedMoment B raw28103step1 raw28103step1Labels := by
      have ha : raw28103step1 = (fun i j => raw28103step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28103step1 raw28103step0; decide +kernel
      have hl : raw28103step1Labels = raw28103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28103step0 raw28103step0Labels permutation149 permutation7
    mixedMoment B raw28103step1 raw28103step1Labels = mixedMoment B raw28103step2 raw28103step2Labels := by
      have ha : raw28103step2 = raw28103step1 := by apply Matrix.ext; unfold raw28103step2 raw28103step1; decide +kernel
      have hl : raw28103step1Labels = labelEmbedding1 ∘ raw28103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28103step1 raw28103step1Labels raw28103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

theorem canonical28104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28104 raw28104Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw28104 raw28104Labels = mixedMoment B raw28104step0 raw28104step0Labels := by
      have hz : ∀ j, raw28104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28104step0 = (fun i j => raw28104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28104step0 raw28104; decide +kernel
      have hl : raw28104step0Labels = raw28104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28104 raw28104Labels permutation346 hz
    mixedMoment B raw28104step0 raw28104step0Labels = mixedMoment B raw28104step1 raw28104step1Labels := by
      have ha : raw28104step1 = (fun i j => raw28104step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28104step1 raw28104step0; decide +kernel
      have hl : raw28104step1Labels = raw28104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28104step0 raw28104step0Labels permutation151 permutation7
    mixedMoment B raw28104step1 raw28104step1Labels = mixedMoment B raw28104step2 raw28104step2Labels := by
      have ha : raw28104step2 = raw28104step1 := by apply Matrix.ext; unfold raw28104step2 raw28104step1; decide +kernel
      have hl : raw28104step1Labels = labelEmbedding1 ∘ raw28104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28104step1 raw28104step1Labels raw28104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical28105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28105 raw28105Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw28105 raw28105Labels = mixedMoment B raw28105step0 raw28105step0Labels := by
      have hz : ∀ j, raw28105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28105step0 = (fun i j => raw28105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28105step0 raw28105; decide +kernel
      have hl : raw28105step0Labels = raw28105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28105 raw28105Labels permutation346 hz
    mixedMoment B raw28105step0 raw28105step0Labels = mixedMoment B raw28105step1 raw28105step1Labels := by
      have ha : raw28105step1 = (fun i j => raw28105step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28105step1 raw28105step0; decide +kernel
      have hl : raw28105step1Labels = raw28105step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28105step0 raw28105step0Labels permutation32 permutation5
    mixedMoment B raw28105step1 raw28105step1Labels = mixedMoment B raw28105step2 raw28105step2Labels := by
      have ha : raw28105step2 = -raw28105step1 := by apply Matrix.ext; change ∀ i j, raw28105step2 i j = -(raw28105step1 i j); unfold raw28105step2 raw28105step1; decide +kernel
      have hl : raw28105step2Labels = raw28105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28105step2 raw28105step2Labels = mixedMoment B raw28105step3 raw28105step3Labels := by
      have ha : raw28105step3 = raw28105step2 := by apply Matrix.ext; unfold raw28105step3 raw28105step2; decide +kernel
      have hl : raw28105step2Labels = labelEmbedding1 ∘ raw28105step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28105step2 raw28105step2Labels raw28105step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

theorem canonical28106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28106 raw28106Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw28106 raw28106Labels = mixedMoment B raw28106step0 raw28106step0Labels := by
      have hz : ∀ j, raw28106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28106step0 = (fun i j => raw28106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28106step0 raw28106; decide +kernel
      have hl : raw28106step0Labels = raw28106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28106 raw28106Labels permutation346 hz
    mixedMoment B raw28106step0 raw28106step0Labels = mixedMoment B raw28106step1 raw28106step1Labels := by
      have ha : raw28106step1 = (fun i j => raw28106step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28106step1 raw28106step0; decide +kernel
      have hl : raw28106step1Labels = raw28106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28106step0 raw28106step0Labels permutation151 permutation7
    mixedMoment B raw28106step1 raw28106step1Labels = mixedMoment B raw28106step2 raw28106step2Labels := by
      have ha : raw28106step2 = raw28106step1 := by apply Matrix.ext; unfold raw28106step2 raw28106step1; decide +kernel
      have hl : raw28106step1Labels = labelEmbedding1 ∘ raw28106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28106step1 raw28106step1Labels raw28106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical28107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28107 raw28107Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw28107 raw28107Labels = mixedMoment B raw28107step0 raw28107step0Labels := by
      have ha : raw28107step0 = (fun i j => raw28107 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28107step0 raw28107; decide +kernel
      have hl : raw28107step0Labels = raw28107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28107 raw28107Labels permutation682 permutation7
    mixedMoment B raw28107step0 raw28107step0Labels = mixedMoment B raw28107step1 raw28107step1Labels := by
      have ha : raw28107step1 = raw28107step0 := by apply Matrix.ext; unfold raw28107step1 raw28107step0; decide +kernel
      have hl : raw28107step0Labels = labelEmbedding1 ∘ raw28107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28107step0 raw28107step0Labels raw28107step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical28108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28108 raw28108Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw28108 raw28108Labels = mixedMoment B raw28108step0 raw28108step0Labels := by
      have hz : ∀ j, raw28108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28108step0 = (fun i j => raw28108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28108step0 raw28108; decide +kernel
      have hl : raw28108step0Labels = raw28108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28108 raw28108Labels permutation346 hz
    mixedMoment B raw28108step0 raw28108step0Labels = mixedMoment B raw28108step1 raw28108step1Labels := by
      have ha : raw28108step1 = (fun i j => raw28108step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28108step1 raw28108step0; decide +kernel
      have hl : raw28108step1Labels = raw28108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28108step0 raw28108step0Labels permutation149 permutation7
    mixedMoment B raw28108step1 raw28108step1Labels = mixedMoment B raw28108step2 raw28108step2Labels := by
      have ha : raw28108step2 = raw28108step1 := by apply Matrix.ext; unfold raw28108step2 raw28108step1; decide +kernel
      have hl : raw28108step1Labels = labelEmbedding1 ∘ raw28108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28108step1 raw28108step1Labels raw28108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical28109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28109 raw28109Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw28109 raw28109Labels = mixedMoment B raw28109step0 raw28109step0Labels := by
      have hz : ∀ j, raw28109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28109step0 = (fun i j => raw28109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28109step0 raw28109; decide +kernel
      have hl : raw28109step0Labels = raw28109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28109 raw28109Labels permutation520 hz
    mixedMoment B raw28109step0 raw28109step0Labels = mixedMoment B raw28109step1 raw28109step1Labels := by
      have hz : ∀ j, raw28109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28109step1 = (fun i j => raw28109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28109step1 raw28109step0; decide +kernel
      have hl : raw28109step1Labels = raw28109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28109step0 raw28109step0Labels permutation80 hz
    mixedMoment B raw28109step1 raw28109step1Labels = mixedMoment B raw28109step2 raw28109step2Labels := by
      have ha : raw28109step2 = (fun i j => raw28109step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28109step2 raw28109step1; decide +kernel
      have hl : raw28109step2Labels = raw28109step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28109step1 raw28109step1Labels permutation31 permutation7
    mixedMoment B raw28109step2 raw28109step2Labels = mixedMoment B raw28109step3 raw28109step3Labels := by
      have ha : raw28109step3 = raw28109step2 := by apply Matrix.ext; unfold raw28109step3 raw28109step2; decide +kernel
      have hl : raw28109step2Labels = labelEmbedding1 ∘ raw28109step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28109step2 raw28109step2Labels raw28109step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical28110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28110 raw28110Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw28110 raw28110Labels = mixedMoment B raw28110step0 raw28110step0Labels := by
      have hz : ∀ j, raw28110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28110step0 = (fun i j => raw28110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28110step0 raw28110; decide +kernel
      have hl : raw28110step0Labels = raw28110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28110 raw28110Labels permutation346 hz
    mixedMoment B raw28110step0 raw28110step0Labels = mixedMoment B raw28110step1 raw28110step1Labels := by
      have ha : raw28110step1 = (fun i j => raw28110step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28110step1 raw28110step0; decide +kernel
      have hl : raw28110step1Labels = raw28110step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28110step0 raw28110step0Labels permutation150 permutation2
    mixedMoment B raw28110step1 raw28110step1Labels = mixedMoment B raw28110step2 raw28110step2Labels := by
      have ha : raw28110step2 = -raw28110step1 := by apply Matrix.ext; change ∀ i j, raw28110step2 i j = -(raw28110step1 i j); unfold raw28110step2 raw28110step1; decide +kernel
      have hl : raw28110step2Labels = raw28110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical28111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28111 raw28111Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28111 raw28111Labels = mixedMoment B raw28111step0 raw28111step0Labels := by
      have hz : ∀ j, raw28111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28111step0 = (fun i j => raw28111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28111step0 raw28111; decide +kernel
      have hl : raw28111step0Labels = raw28111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28111 raw28111Labels permutation346 hz
    mixedMoment B raw28111step0 raw28111step0Labels = mixedMoment B raw28111step1 raw28111step1Labels := by
      have ha : raw28111step1 = (fun i j => raw28111step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28111step1 raw28111step0; decide +kernel
      have hl : raw28111step1Labels = raw28111step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28111step0 raw28111step0Labels permutation151 permutation2
    mixedMoment B raw28111step1 raw28111step1Labels = mixedMoment B raw28111step2 raw28111step2Labels := by
      have ha : raw28111step2 = -raw28111step1 := by apply Matrix.ext; change ∀ i j, raw28111step2 i j = -(raw28111step1 i j); unfold raw28111step2 raw28111step1; decide +kernel
      have hl : raw28111step2Labels = raw28111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical28112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28112 raw28112Labels = mixedMoment B node1956 node1956Labels := by
  calc
    mixedMoment B raw28112 raw28112Labels = mixedMoment B raw28112step0 raw28112step0Labels := by
      have ha : raw28112step0 = (fun i j => raw28112 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28112step0 raw28112; decide +kernel
      have hl : raw28112step0Labels = raw28112Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28112 raw28112Labels permutation646 permutation2
    mixedMoment B raw28112step0 raw28112step0Labels = mixedMoment B raw28112step1 raw28112step1Labels := by
      have ha : raw28112step1 = -raw28112step0 := by apply Matrix.ext; change ∀ i j, raw28112step1 i j = -(raw28112step0 i j); unfold raw28112step1 raw28112step0; decide +kernel
      have hl : raw28112step1Labels = raw28112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1956 node1956Labels := by rfl

theorem canonical28113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28113 raw28113Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw28113 raw28113Labels = mixedMoment B raw28113step0 raw28113step0Labels := by
      have hz : ∀ j, raw28113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28113step0 = (fun i j => raw28113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28113step0 raw28113; decide +kernel
      have hl : raw28113step0Labels = raw28113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28113 raw28113Labels permutation346 hz
    mixedMoment B raw28113step0 raw28113step0Labels = mixedMoment B raw28113step1 raw28113step1Labels := by
      have ha : raw28113step1 = (fun i j => raw28113step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28113step1 raw28113step0; decide +kernel
      have hl : raw28113step1Labels = raw28113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28113step0 raw28113step0Labels permutation151 permutation2
    mixedMoment B raw28113step1 raw28113step1Labels = mixedMoment B raw28113step2 raw28113step2Labels := by
      have ha : raw28113step2 = -raw28113step1 := by apply Matrix.ext; change ∀ i j, raw28113step2 i j = -(raw28113step1 i j); unfold raw28113step2 raw28113step1; decide +kernel
      have hl : raw28113step2Labels = raw28113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

theorem canonical28114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28114 raw28114Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw28114 raw28114Labels = mixedMoment B raw28114step0 raw28114step0Labels := by
      have hz : ∀ j, raw28114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28114step0 = (fun i j => raw28114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28114step0 raw28114; decide +kernel
      have hl : raw28114step0Labels = raw28114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28114 raw28114Labels permutation346 hz
    mixedMoment B raw28114step0 raw28114step0Labels = mixedMoment B raw28114step1 raw28114step1Labels := by
      have ha : raw28114step1 = (fun i j => raw28114step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28114step1 raw28114step0; decide +kernel
      have hl : raw28114step1Labels = raw28114step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28114step0 raw28114step0Labels permutation151 permutation2
    mixedMoment B raw28114step1 raw28114step1Labels = mixedMoment B raw28114step2 raw28114step2Labels := by
      have ha : raw28114step2 = -raw28114step1 := by apply Matrix.ext; change ∀ i j, raw28114step2 i j = -(raw28114step1 i j); unfold raw28114step2 raw28114step1; decide +kernel
      have hl : raw28114step2Labels = raw28114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1796 node1796Labels := by rfl

theorem canonical28115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28115 raw28115Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw28115 raw28115Labels = mixedMoment B raw28115step0 raw28115step0Labels := by
      have hz : ∀ j, raw28115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28115step0 = (fun i j => raw28115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28115step0 raw28115; decide +kernel
      have hl : raw28115step0Labels = raw28115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28115 raw28115Labels permutation346 hz
    mixedMoment B raw28115step0 raw28115step0Labels = mixedMoment B raw28115step1 raw28115step1Labels := by
      have ha : raw28115step1 = (fun i j => raw28115step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28115step1 raw28115step0; decide +kernel
      have hl : raw28115step1Labels = raw28115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28115step0 raw28115step0Labels permutation151 permutation2
    mixedMoment B raw28115step1 raw28115step1Labels = mixedMoment B raw28115step2 raw28115step2Labels := by
      have ha : raw28115step2 = -raw28115step1 := by apply Matrix.ext; change ∀ i j, raw28115step2 i j = -(raw28115step1 i j); unfold raw28115step2 raw28115step1; decide +kernel
      have hl : raw28115step2Labels = raw28115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node913 node913Labels := by rfl

theorem canonical28116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28116 raw28116Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw28116 raw28116Labels = mixedMoment B raw28116step0 raw28116step0Labels := by
      have hz : ∀ j, raw28116 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28116step0 = (fun i j => raw28116 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28116step0 raw28116; decide +kernel
      have hl : raw28116step0Labels = raw28116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28116 raw28116Labels permutation520 hz
    mixedMoment B raw28116step0 raw28116step0Labels = mixedMoment B raw28116step1 raw28116step1Labels := by
      have hz : ∀ j, raw28116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28116step1 = (fun i j => raw28116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28116step1 raw28116step0; decide +kernel
      have hl : raw28116step1Labels = raw28116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28116step0 raw28116step0Labels permutation80 hz
    mixedMoment B raw28116step1 raw28116step1Labels = mixedMoment B raw28116step2 raw28116step2Labels := by
      have ha : raw28116step2 = (fun i j => raw28116step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28116step2 raw28116step1; decide +kernel
      have hl : raw28116step2Labels = raw28116step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28116step1 raw28116step1Labels permutation26 permutation0
    mixedMoment B raw28116step2 raw28116step2Labels = mixedMoment B raw28116step3 raw28116step3Labels := by
      have ha : raw28116step3 = -raw28116step2 := by apply Matrix.ext; change ∀ i j, raw28116step3 i j = -(raw28116step2 i j); unfold raw28116step3 raw28116step2; decide +kernel
      have hl : raw28116step3Labels = raw28116step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical28117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28117 raw28117Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw28117 raw28117Labels = mixedMoment B raw28117step0 raw28117step0Labels := by
      have ha : raw28117step0 = (fun i j => raw28117 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28117step0 raw28117; decide +kernel
      have hl : raw28117step0Labels = raw28117Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28117 raw28117Labels permutation158 permutation2
    _ = mixedMoment B node1326 node1326Labels := by rfl

theorem canonical28118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28118 raw28118Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw28118 raw28118Labels = mixedMoment B raw28118step0 raw28118step0Labels := by
      have ha : raw28118step0 = (fun i j => raw28118 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28118step0 raw28118; decide +kernel
      have hl : raw28118step0Labels = raw28118Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28118 raw28118Labels permutation644 permutation2
    mixedMoment B raw28118step0 raw28118step0Labels = mixedMoment B raw28118step1 raw28118step1Labels := by
      have ha : raw28118step1 = -raw28118step0 := by apply Matrix.ext; change ∀ i j, raw28118step1 i j = -(raw28118step0 i j); unfold raw28118step1 raw28118step0; decide +kernel
      have hl : raw28118step1Labels = raw28118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical28119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28119 raw28119Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28119 raw28119Labels = mixedMoment B raw28119step0 raw28119step0Labels := by
      have hz : ∀ j, raw28119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28119step0 = (fun i j => raw28119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28119step0 raw28119; decide +kernel
      have hl : raw28119step0Labels = raw28119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28119 raw28119Labels permutation520 hz
    mixedMoment B raw28119step0 raw28119step0Labels = mixedMoment B raw28119step1 raw28119step1Labels := by
      have ha : raw28119step1 = (fun i j => raw28119step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28119step1 raw28119step0; decide +kernel
      have hl : raw28119step1Labels = raw28119step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28119step0 raw28119step0Labels permutation145 permutation2
    mixedMoment B raw28119step1 raw28119step1Labels = mixedMoment B raw28119step2 raw28119step2Labels := by
      have ha : raw28119step2 = -raw28119step1 := by apply Matrix.ext; change ∀ i j, raw28119step2 i j = -(raw28119step1 i j); unfold raw28119step2 raw28119step1; decide +kernel
      have hl : raw28119step2Labels = raw28119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical28120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28120 raw28120Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw28120 raw28120Labels = mixedMoment B raw28120step0 raw28120step0Labels := by
      have ha : raw28120step0 = (fun i j => raw28120 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28120step0 raw28120; decide +kernel
      have hl : raw28120step0Labels = raw28120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28120 raw28120Labels permutation158 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical28121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28121 raw28121Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw28121 raw28121Labels = mixedMoment B raw28121step0 raw28121step0Labels := by
      have hz : ∀ j, raw28121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28121step0 = (fun i j => raw28121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28121step0 raw28121; decide +kernel
      have hl : raw28121step0Labels = raw28121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28121 raw28121Labels permutation346 hz
    mixedMoment B raw28121step0 raw28121step0Labels = mixedMoment B raw28121step1 raw28121step1Labels := by
      have ha : raw28121step1 = (fun i j => raw28121step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28121step1 raw28121step0; decide +kernel
      have hl : raw28121step1Labels = raw28121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28121step0 raw28121step0Labels permutation149 permutation2
    mixedMoment B raw28121step1 raw28121step1Labels = mixedMoment B raw28121step2 raw28121step2Labels := by
      have ha : raw28121step2 = -raw28121step1 := by apply Matrix.ext; change ∀ i j, raw28121step2 i j = -(raw28121step1 i j); unfold raw28121step2 raw28121step1; decide +kernel
      have hl : raw28121step2Labels = raw28121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2057 node2057Labels := by rfl

theorem canonical28122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28122 raw28122Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28122 raw28122Labels = mixedMoment B raw28122step0 raw28122step0Labels := by
      have hz : ∀ j, raw28122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28122step0 = (fun i j => raw28122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28122step0 raw28122; decide +kernel
      have hl : raw28122step0Labels = raw28122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28122 raw28122Labels permutation346 hz
    mixedMoment B raw28122step0 raw28122step0Labels = mixedMoment B raw28122step1 raw28122step1Labels := by
      have ha : raw28122step1 = (fun i j => raw28122step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28122step1 raw28122step0; decide +kernel
      have hl : raw28122step1Labels = raw28122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28122step0 raw28122step0Labels permutation149 permutation2
    mixedMoment B raw28122step1 raw28122step1Labels = mixedMoment B raw28122step2 raw28122step2Labels := by
      have ha : raw28122step2 = -raw28122step1 := by apply Matrix.ext; change ∀ i j, raw28122step2 i j = -(raw28122step1 i j); unfold raw28122step2 raw28122step1; decide +kernel
      have hl : raw28122step2Labels = raw28122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical28123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28123 raw28123Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw28123 raw28123Labels = mixedMoment B raw28123step0 raw28123step0Labels := by
      have hz : ∀ j, raw28123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28123step0 = (fun i j => raw28123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28123step0 raw28123; decide +kernel
      have hl : raw28123step0Labels = raw28123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28123 raw28123Labels permutation346 hz
    mixedMoment B raw28123step0 raw28123step0Labels = mixedMoment B raw28123step1 raw28123step1Labels := by
      have ha : raw28123step1 = (fun i j => raw28123step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28123step1 raw28123step0; decide +kernel
      have hl : raw28123step1Labels = raw28123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28123step0 raw28123step0Labels permutation149 permutation2
    mixedMoment B raw28123step1 raw28123step1Labels = mixedMoment B raw28123step2 raw28123step2Labels := by
      have ha : raw28123step2 = -raw28123step1 := by apply Matrix.ext; change ∀ i j, raw28123step2 i j = -(raw28123step1 i j); unfold raw28123step2 raw28123step1; decide +kernel
      have hl : raw28123step2Labels = raw28123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical28124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28124 raw28124Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw28124 raw28124Labels = mixedMoment B raw28124step0 raw28124step0Labels := by
      have hz : ∀ j, raw28124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28124step0 = (fun i j => raw28124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28124step0 raw28124; decide +kernel
      have hl : raw28124step0Labels = raw28124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28124 raw28124Labels permutation346 hz
    mixedMoment B raw28124step0 raw28124step0Labels = mixedMoment B raw28124step1 raw28124step1Labels := by
      have ha : raw28124step1 = (fun i j => raw28124step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28124step1 raw28124step0; decide +kernel
      have hl : raw28124step1Labels = raw28124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28124step0 raw28124step0Labels permutation149 permutation2
    mixedMoment B raw28124step1 raw28124step1Labels = mixedMoment B raw28124step2 raw28124step2Labels := by
      have ha : raw28124step2 = -raw28124step1 := by apply Matrix.ext; change ∀ i j, raw28124step2 i j = -(raw28124step1 i j); unfold raw28124step2 raw28124step1; decide +kernel
      have hl : raw28124step2Labels = raw28124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node913 node913Labels = Sparse.eval nodeValue913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 913) = mixedMoment B node913 node913Labels := rfl
  simpa [nodeValue913, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

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

theorem sound1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1136 node1136Labels = Sparse.eval nodeValue1136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1136) = mixedMoment B node1136 node1136Labels := rfl
  simpa [nodeValue1136, Sparse.eval] using hc.symm

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

theorem sound1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1320 node1320Labels = Sparse.eval nodeValue1320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1320) = mixedMoment B node1320 node1320Labels := rfl
  simpa [nodeValue1320, Sparse.eval] using hc.symm

theorem sound1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1326 node1326Labels = Sparse.eval nodeValue1326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1326) = mixedMoment B node1326 node1326Labels := rfl
  simpa [nodeValue1326, Sparse.eval] using hc.symm

theorem sound1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1334 node1334Labels = Sparse.eval nodeValue1334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1334) = mixedMoment B node1334 node1334Labels := rfl
  simpa [nodeValue1334, Sparse.eval] using hc.symm

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

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1672 node1672Labels = Sparse.eval nodeValue1672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1672) = mixedMoment B node1672 node1672Labels := rfl
  simpa [nodeValue1672, Sparse.eval] using hc.symm

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1684 node1684Labels = Sparse.eval nodeValue1684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1684) = mixedMoment B node1684 node1684Labels := rfl
  simpa [nodeValue1684, Sparse.eval] using hc.symm

theorem sound1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1685 node1685Labels = Sparse.eval nodeValue1685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1685) = mixedMoment B node1685 node1685Labels := rfl
  simpa [nodeValue1685, Sparse.eval] using hc.symm

theorem sound1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1686 node1686Labels = Sparse.eval nodeValue1686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1686) = mixedMoment B node1686 node1686Labels := rfl
  simpa [nodeValue1686, Sparse.eval] using hc.symm

theorem sound1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1688 node1688Labels = Sparse.eval nodeValue1688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1688) = mixedMoment B node1688 node1688Labels := rfl
  simpa [nodeValue1688, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

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

theorem sound1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1744 node1744Labels = Sparse.eval nodeValue1744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1744) = mixedMoment B node1744 node1744Labels := rfl
  simpa [nodeValue1744, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

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

theorem sound1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1796 node1796Labels = Sparse.eval nodeValue1796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1796) = mixedMoment B node1796 node1796Labels := rfl
  simpa [nodeValue1796, Sparse.eval] using hc.symm

theorem sound1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1812 node1812Labels = Sparse.eval nodeValue1812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1812) = mixedMoment B node1812 node1812Labels := rfl
  simpa [nodeValue1812, Sparse.eval] using hc.symm

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

theorem sound1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1956 node1956Labels = Sparse.eval nodeValue1956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1956) = mixedMoment B node1956 node1956Labels := rfl
  simpa [nodeValue1956, Sparse.eval] using hc.symm

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

theorem sound1979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1979 node1979Labels = Sparse.eval nodeValue1979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1979) = mixedMoment B node1979 node1979Labels := rfl
  simpa [nodeValue1979, Sparse.eval] using hc.symm

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

theorem sound2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2015 node2015Labels = Sparse.eval nodeValue2015 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2015) = mixedMoment B node2015 node2015Labels := rfl
  simpa [nodeValue2015, Sparse.eval] using hc.symm

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2027 node2027Labels = Sparse.eval nodeValue2027 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2027) = mixedMoment B node2027 node2027Labels := rfl
  simpa [nodeValue2027, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem zero2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2057 node2057Labels = 0 := by
  exact mixedMoment_order_one B hB node2057 node2057Labels 1
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

theorem sound2057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2057 node2057Labels = Sparse.eval nodeValue2057 (mixedVector B) := by
  simpa only [nodeValue2057, Sparse.eval_nil] using zero2057 B _hB _hF

theorem sound2074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2074 node2074Labels = Sparse.eval nodeValue2074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2074) = mixedMoment B node2074 node2074Labels := rfl
  simpa [nodeValue2074, Sparse.eval] using hc.symm

theorem sound2081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2081 node2081Labels = Sparse.eval nodeValue2081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2081) = mixedMoment B node2081 node2081Labels := rfl
  simpa [nodeValue2081, Sparse.eval] using hc.symm

theorem sound2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2099 node2099Labels = Sparse.eval nodeValue2099 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2099) = mixedMoment B node2099 node2099Labels := rfl
  simpa [nodeValue2099, Sparse.eval] using hc.symm

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

theorem sound2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2147 node2147Labels = Sparse.eval nodeValue2147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2147) = mixedMoment B node2147 node2147Labels := rfl
  simpa [nodeValue2147, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

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

theorem zero2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = 0 := by
  exact mixedMoment_order_one B hB node2227 node2227Labels 1
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

theorem sound2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2181 node2181Labels = Sparse.eval nodeValue2181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2181) = mixedMoment B node2181 node2181Labels := rfl
  simpa [nodeValue2181, Sparse.eval] using hc.symm

theorem sound2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2182 node2182Labels = Sparse.eval nodeValue2182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2182) = mixedMoment B node2182 node2182Labels := rfl
  simpa [nodeValue2182, Sparse.eval] using hc.symm

theorem sound2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2198 node2198Labels = Sparse.eval nodeValue2198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2198) = mixedMoment B node2198 node2198Labels := rfl
  simpa [nodeValue2198, Sparse.eval] using hc.symm

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

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

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2339 node2339Labels = Sparse.eval nodeValue2339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2339) = mixedMoment B node2339 node2339Labels := rfl
  simpa [nodeValue2339, Sparse.eval] using hc.symm

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

theorem sound2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2429 node2429Labels = Sparse.eval nodeValue2429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2429) = mixedMoment B node2429 node2429Labels := rfl
  simpa [nodeValue2429, Sparse.eval] using hc.symm

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

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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

theorem zero2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2514 node2514Labels = 0 := by
  exact mixedMoment_order_one B hB node2514 node2514Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2514 node2514Labels = Sparse.eval nodeValue2514 (mixedVector B) := by
  simpa only [nodeValue2514, Sparse.eval_nil] using zero2514 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2700 node2700Labels = Sparse.eval nodeValue2700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2700) = mixedMoment B node2700 node2700Labels := rfl
  simpa [nodeValue2700, Sparse.eval] using hc.symm

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2797 node2797Labels = Sparse.eval nodeValue2797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2797) = mixedMoment B node2797 node2797Labels := rfl
  simpa [nodeValue2797, Sparse.eval] using hc.symm

theorem sound2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2802 node2802Labels = Sparse.eval nodeValue2802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2802) = mixedMoment B node2802 node2802Labels := rfl
  simpa [nodeValue2802, Sparse.eval] using hc.symm

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

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

theorem sound2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2847 node2847Labels = Sparse.eval nodeValue2847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2847) = mixedMoment B node2847 node2847Labels := rfl
  simpa [nodeValue2847, Sparse.eval] using hc.symm

theorem sound2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2865 node2865Labels = Sparse.eval nodeValue2865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2865) = mixedMoment B node2865 node2865Labels := rfl
  simpa [nodeValue2865, Sparse.eval] using hc.symm

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

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

theorem sound2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2923 node2923Labels = Sparse.eval nodeValue2923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2923) = mixedMoment B node2923 node2923Labels := rfl
  simpa [nodeValue2923, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3260 node3260Labels = Sparse.eval nodeValue3260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3260) = mixedMoment B node3260 node3260Labels := rfl
  simpa [nodeValue3260, Sparse.eval] using hc.symm

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

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

theorem sound3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3273 node3273Labels = Sparse.eval nodeValue3273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3273) = mixedMoment B node3273 node3273Labels := rfl
  simpa [nodeValue3273, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

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

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

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

theorem sound3451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3451 node3451Labels = Sparse.eval nodeValue3451 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3451) = mixedMoment B node3451 node3451Labels := rfl
  simpa [nodeValue3451, Sparse.eval] using hc.symm

theorem sound3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3455 node3455Labels = Sparse.eval nodeValue3455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3455) = mixedMoment B node3455 node3455Labels := rfl
  simpa [nodeValue3455, Sparse.eval] using hc.symm

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

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

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

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1959 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1959 + difference 0 3) (sourceB1959 + difference 3 0) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1959 + difference 0 3) (sourceB1959 + difference 3 0) sourceC1959) = raw27817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27817; decide +kernel
    rw [ha]
    exact (canonical27817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1959 + difference 1 3) (sourceB1959 + difference 3 1) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1959 + difference 1 3) (sourceB1959 + difference 3 1) sourceC1959) = raw27818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27818; decide +kernel
    rw [ha]
    exact (canonical27818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1959 + difference 2 3) (sourceB1959 + difference 3 2) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA1959 + difference 2 3) (sourceB1959 + difference 3 2) sourceC1959) = raw27819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27819; decide +kernel
    rw [ha]
    exact (canonical27819 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1959 + difference 3 3) (sourceB1959 + difference 3 3) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1959 + difference 3 3) (sourceB1959 + difference 3 3) sourceC1959) = raw27820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27820; decide +kernel
    rw [ha]
    exact (canonical27820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1959 + difference 4 3) (sourceB1959 + difference 3 4) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1959 + difference 4 3) (sourceB1959 + difference 3 4) sourceC1959) = raw27821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27821; decide +kernel
    rw [ha]
    exact (canonical27821 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1959 + difference 5 3) (sourceB1959 + difference 3 5) sourceC1959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1959 + difference 5 3) (sourceB1959 + difference 3 5) sourceC1959) = raw27822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1959 sourceB1959 sourceC1959 difference raw27822; decide +kernel
    rw [ha]
    exact (canonical27822 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1959 + sourceB1959) sourceC1959) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1959 + sourceB1959) sourceC1959) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA1959 sourceB1959 sourceC1959 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1959 sourceB1959 sourceC1959
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1959, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1960 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 0) (sourceB1960 + difference 0 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 0) (sourceB1960 + difference 0 4) sourceC1960) = raw27824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27824; decide +kernel
    rw [ha]
    exact (canonical27824 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 1) (sourceB1960 + difference 1 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 1) (sourceB1960 + difference 1 4) sourceC1960) = raw27825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27825; decide +kernel
    rw [ha]
    exact (canonical27825 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 2) (sourceB1960 + difference 2 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 2) (sourceB1960 + difference 2 4) sourceC1960) = raw27826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27826; decide +kernel
    rw [ha]
    exact (canonical27826 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 3) (sourceB1960 + difference 3 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 3) (sourceB1960 + difference 3 4) sourceC1960) = raw27821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27821; decide +kernel
    rw [ha]
    exact (canonical27821 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 4) (sourceB1960 + difference 4 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 4) (sourceB1960 + difference 4 4) sourceC1960) = raw27820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27820; decide +kernel
    rw [ha]
    exact (canonical27820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1960 + difference 4 5) (sourceB1960 + difference 5 4) sourceC1960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1960 + difference 4 5) (sourceB1960 + difference 5 4) sourceC1960) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1960 sourceB1960 sourceC1960 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1960 + sourceB1960) sourceC1960) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1960 + sourceB1960) sourceC1960) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA1960 sourceB1960 sourceC1960 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1960 sourceB1960 sourceC1960
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1960, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1961 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1961 + difference 0 0) (sourceB1961 + difference 0 0) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1961 + difference 0 0) (sourceB1961 + difference 0 0) sourceC1961) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1961 + difference 1 0) (sourceB1961 + difference 0 1) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2099) := by
    have ha : (tripleCharges (sourceA1961 + difference 1 0) (sourceB1961 + difference 0 1) sourceC1961) = raw27828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27828; decide +kernel
    rw [ha]
    exact (canonical27828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1961 + difference 2 0) (sourceB1961 + difference 0 2) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA1961 + difference 2 0) (sourceB1961 + difference 0 2) sourceC1961) = raw27829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27829; decide +kernel
    rw [ha]
    exact (canonical27829 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1961 + difference 3 0) (sourceB1961 + difference 0 3) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA1961 + difference 3 0) (sourceB1961 + difference 0 3) sourceC1961) = raw27830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27830; decide +kernel
    rw [ha]
    exact (canonical27830 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1961 + difference 4 0) (sourceB1961 + difference 0 4) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1961 + difference 4 0) (sourceB1961 + difference 0 4) sourceC1961) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1961 + difference 5 0) (sourceB1961 + difference 0 5) sourceC1961) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1961 + difference 5 0) (sourceB1961 + difference 0 5) sourceC1961) = raw27831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1961 sourceB1961 sourceC1961 difference raw27831; decide +kernel
    rw [ha]
    exact (canonical27831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1961 + sourceB1961) sourceC1961) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1961 + sourceB1961) sourceC1961) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1961 sourceB1961 sourceC1961 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1961 sourceB1961 sourceC1961
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1961, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1962 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 0) (sourceB1962 + difference 0 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 0) (sourceB1962 + difference 0 5) sourceC1962) = raw27831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27831; decide +kernel
    rw [ha]
    exact (canonical27831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 1) (sourceB1962 + difference 1 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 1) (sourceB1962 + difference 1 5) sourceC1962) = raw27832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27832; decide +kernel
    rw [ha]
    exact (canonical27832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 2) (sourceB1962 + difference 2 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 2) (sourceB1962 + difference 2 5) sourceC1962) = raw27833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27833; decide +kernel
    rw [ha]
    exact (canonical27833 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 3) (sourceB1962 + difference 3 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 3) (sourceB1962 + difference 3 5) sourceC1962) = raw27834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27834; decide +kernel
    rw [ha]
    exact (canonical27834 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 4) (sourceB1962 + difference 4 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 4) (sourceB1962 + difference 4 5) sourceC1962) = raw27835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27835; decide +kernel
    rw [ha]
    exact (canonical27835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1962 + difference 5 5) (sourceB1962 + difference 5 5) sourceC1962) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1962 + difference 5 5) (sourceB1962 + difference 5 5) sourceC1962) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1962 sourceB1962 sourceC1962 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1962 + sourceB1962) sourceC1962) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1962 + sourceB1962) sourceC1962) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1962 sourceB1962 sourceC1962 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1962 sourceB1962 sourceC1962
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1962, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1967 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 1) (sourceB1967 + difference 1 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 1) (sourceB1967 + difference 1 0) sourceC1967) = raw27914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27914; decide +kernel
    rw [ha]
    exact (canonical27914 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 2) (sourceB1967 + difference 2 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 2) (sourceB1967 + difference 2 0) sourceC1967) = raw27915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27915; decide +kernel
    rw [ha]
    exact (canonical27915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 3) (sourceB1967 + difference 3 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 3) (sourceB1967 + difference 3 0) sourceC1967) = raw27916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27916; decide +kernel
    rw [ha]
    exact (canonical27916 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 4) (sourceB1967 + difference 4 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 4) (sourceB1967 + difference 4 0) sourceC1967) = raw27917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27917; decide +kernel
    rw [ha]
    exact (canonical27917 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1967 + difference 0 5) (sourceB1967 + difference 5 0) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA1967 + difference 0 5) (sourceB1967 + difference 5 0) sourceC1967) = raw27918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27918; decide +kernel
    rw [ha]
    exact (canonical27918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 0) (sourceB1967 + difference 0 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 0) (sourceB1967 + difference 0 1) sourceC1967) = raw27919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27919; decide +kernel
    rw [ha]
    exact (canonical27919 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 2) (sourceB1967 + difference 2 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 2) (sourceB1967 + difference 2 1) sourceC1967) = raw27920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27920; decide +kernel
    rw [ha]
    exact (canonical27920 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 3) (sourceB1967 + difference 3 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 3) (sourceB1967 + difference 3 1) sourceC1967) = raw27921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27921; decide +kernel
    rw [ha]
    exact (canonical27921 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 4) (sourceB1967 + difference 4 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 4) (sourceB1967 + difference 4 1) sourceC1967) = raw27922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27922; decide +kernel
    rw [ha]
    exact (canonical27922 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1967 + difference 1 5) (sourceB1967 + difference 5 1) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA1967 + difference 1 5) (sourceB1967 + difference 5 1) sourceC1967) = raw27923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27923; decide +kernel
    rw [ha]
    exact (canonical27923 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 0) (sourceB1967 + difference 0 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 0) (sourceB1967 + difference 0 2) sourceC1967) = raw27924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27924; decide +kernel
    rw [ha]
    exact (canonical27924 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 1) (sourceB1967 + difference 1 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 1) (sourceB1967 + difference 1 2) sourceC1967) = raw27925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27925; decide +kernel
    rw [ha]
    exact (canonical27925 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 3) (sourceB1967 + difference 3 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 3) (sourceB1967 + difference 3 2) sourceC1967) = raw27926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27926; decide +kernel
    rw [ha]
    exact (canonical27926 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 4) (sourceB1967 + difference 4 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 4) (sourceB1967 + difference 4 2) sourceC1967) = raw27927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27927; decide +kernel
    rw [ha]
    exact (canonical27927 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1967 + difference 2 5) (sourceB1967 + difference 5 2) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA1967 + difference 2 5) (sourceB1967 + difference 5 2) sourceC1967) = raw27928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27928; decide +kernel
    rw [ha]
    exact (canonical27928 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 0) (sourceB1967 + difference 0 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 0) (sourceB1967 + difference 0 3) sourceC1967) = raw27929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27929; decide +kernel
    rw [ha]
    exact (canonical27929 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 1) (sourceB1967 + difference 1 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 1) (sourceB1967 + difference 1 3) sourceC1967) = raw27930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27930; decide +kernel
    rw [ha]
    exact (canonical27930 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 2) (sourceB1967 + difference 2 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 2) (sourceB1967 + difference 2 3) sourceC1967) = raw27931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27931; decide +kernel
    rw [ha]
    exact (canonical27931 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 4) (sourceB1967 + difference 4 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 4) (sourceB1967 + difference 4 3) sourceC1967) = raw27932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27932; decide +kernel
    rw [ha]
    exact (canonical27932 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1967 + difference 3 5) (sourceB1967 + difference 5 3) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA1967 + difference 3 5) (sourceB1967 + difference 5 3) sourceC1967) = raw27933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27933; decide +kernel
    rw [ha]
    exact (canonical27933 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 0) (sourceB1967 + difference 0 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 0) (sourceB1967 + difference 0 4) sourceC1967) = raw27934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27934; decide +kernel
    rw [ha]
    exact (canonical27934 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 1) (sourceB1967 + difference 1 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 1) (sourceB1967 + difference 1 4) sourceC1967) = raw27935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27935; decide +kernel
    rw [ha]
    exact (canonical27935 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 2) (sourceB1967 + difference 2 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 2) (sourceB1967 + difference 2 4) sourceC1967) = raw27936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27936; decide +kernel
    rw [ha]
    exact (canonical27936 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 3) (sourceB1967 + difference 3 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 3) (sourceB1967 + difference 3 4) sourceC1967) = raw27937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27937; decide +kernel
    rw [ha]
    exact (canonical27937 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1967 + difference 4 5) (sourceB1967 + difference 5 4) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA1967 + difference 4 5) (sourceB1967 + difference 5 4) sourceC1967) = raw27938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27938; decide +kernel
    rw [ha]
    exact (canonical27938 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 0) (sourceB1967 + difference 0 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 0) (sourceB1967 + difference 0 5) sourceC1967) = raw27939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27939; decide +kernel
    rw [ha]
    exact (canonical27939 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 1) (sourceB1967 + difference 1 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 1) (sourceB1967 + difference 1 5) sourceC1967) = raw27940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27940; decide +kernel
    rw [ha]
    exact (canonical27940 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 2) (sourceB1967 + difference 2 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 2) (sourceB1967 + difference 2 5) sourceC1967) = raw27941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27941; decide +kernel
    rw [ha]
    exact (canonical27941 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 3) (sourceB1967 + difference 3 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 3) (sourceB1967 + difference 3 5) sourceC1967) = raw27942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27942; decide +kernel
    rw [ha]
    exact (canonical27942 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1967 + difference 5 4) (sourceB1967 + difference 4 5) sourceC1967) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1967 + difference 5 4) (sourceB1967 + difference 4 5) sourceC1967) = raw27943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1967 sourceB1967 sourceC1967 difference raw27943; decide +kernel
    rw [ha]
    exact (canonical27943 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1967 sourceB1967 sourceC1967
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1967, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1968 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1968 + difference 0 3) (sourceB1968 + difference 3 0) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA1968 + difference 0 3) (sourceB1968 + difference 3 0) sourceC1968) = raw27944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27944; decide +kernel
    rw [ha]
    exact (canonical27944 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1968 + difference 1 3) (sourceB1968 + difference 3 1) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1968 + difference 1 3) (sourceB1968 + difference 3 1) sourceC1968) = raw27945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27945; decide +kernel
    rw [ha]
    exact (canonical27945 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1968 + difference 2 3) (sourceB1968 + difference 3 2) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1968 + difference 2 3) (sourceB1968 + difference 3 2) sourceC1968) = raw27946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27946; decide +kernel
    rw [ha]
    exact (canonical27946 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1968 + difference 3 3) (sourceB1968 + difference 3 3) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1968 + difference 3 3) (sourceB1968 + difference 3 3) sourceC1968) = raw27947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27947; decide +kernel
    rw [ha]
    exact (canonical27947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1968 + difference 4 3) (sourceB1968 + difference 3 4) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA1968 + difference 4 3) (sourceB1968 + difference 3 4) sourceC1968) = raw27948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27948; decide +kernel
    rw [ha]
    exact (canonical27948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1968 + difference 5 3) (sourceB1968 + difference 3 5) sourceC1968) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1968 + difference 5 3) (sourceB1968 + difference 3 5) sourceC1968) = raw27949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1968 sourceB1968 sourceC1968 difference raw27949; decide +kernel
    rw [ha]
    exact (canonical27949 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1968 + sourceB1968) sourceC1968) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1968 + sourceB1968) sourceC1968) = raw27950 := by
      apply Matrix.ext; unfold doubleCharges sourceA1968 sourceB1968 sourceC1968 raw27950; decide +kernel
    rw [ha]
    exact (canonical27950 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1968 sourceB1968 sourceC1968
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1968, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1975 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 1) (sourceB1975 + difference 1 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 1) (sourceB1975 + difference 1 0) sourceC1975) = raw28080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28080; decide +kernel
    rw [ha]
    exact (canonical28080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 2) (sourceB1975 + difference 2 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 2) (sourceB1975 + difference 2 0) sourceC1975) = raw28081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28081; decide +kernel
    rw [ha]
    exact (canonical28081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 3) (sourceB1975 + difference 3 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 3) (sourceB1975 + difference 3 0) sourceC1975) = raw28082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28082; decide +kernel
    rw [ha]
    exact (canonical28082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 4) (sourceB1975 + difference 4 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 4) (sourceB1975 + difference 4 0) sourceC1975) = raw28083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28083; decide +kernel
    rw [ha]
    exact (canonical28083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1975 + difference 0 5) (sourceB1975 + difference 5 0) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA1975 + difference 0 5) (sourceB1975 + difference 5 0) sourceC1975) = raw28084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28084; decide +kernel
    rw [ha]
    exact (canonical28084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 0) (sourceB1975 + difference 0 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 0) (sourceB1975 + difference 0 1) sourceC1975) = raw28085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28085; decide +kernel
    rw [ha]
    exact (canonical28085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 2) (sourceB1975 + difference 2 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 2) (sourceB1975 + difference 2 1) sourceC1975) = raw28086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28086; decide +kernel
    rw [ha]
    exact (canonical28086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 3) (sourceB1975 + difference 3 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 3) (sourceB1975 + difference 3 1) sourceC1975) = raw28087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28087; decide +kernel
    rw [ha]
    exact (canonical28087 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 4) (sourceB1975 + difference 4 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 4) (sourceB1975 + difference 4 1) sourceC1975) = raw28088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28088; decide +kernel
    rw [ha]
    exact (canonical28088 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1975 + difference 1 5) (sourceB1975 + difference 5 1) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA1975 + difference 1 5) (sourceB1975 + difference 5 1) sourceC1975) = raw28089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28089; decide +kernel
    rw [ha]
    exact (canonical28089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 0) (sourceB1975 + difference 0 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 0) (sourceB1975 + difference 0 2) sourceC1975) = raw28090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28090; decide +kernel
    rw [ha]
    exact (canonical28090 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 1) (sourceB1975 + difference 1 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 1) (sourceB1975 + difference 1 2) sourceC1975) = raw28091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28091; decide +kernel
    rw [ha]
    exact (canonical28091 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 3) (sourceB1975 + difference 3 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2182) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 3) (sourceB1975 + difference 3 2) sourceC1975) = raw28092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28092; decide +kernel
    rw [ha]
    exact (canonical28092 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 4) (sourceB1975 + difference 4 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 4) (sourceB1975 + difference 4 2) sourceC1975) = raw28093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28093; decide +kernel
    rw [ha]
    exact (canonical28093 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1975 + difference 2 5) (sourceB1975 + difference 5 2) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA1975 + difference 2 5) (sourceB1975 + difference 5 2) sourceC1975) = raw28094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28094; decide +kernel
    rw [ha]
    exact (canonical28094 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 0) (sourceB1975 + difference 0 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 0) (sourceB1975 + difference 0 3) sourceC1975) = raw28095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28095; decide +kernel
    rw [ha]
    exact (canonical28095 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 1) (sourceB1975 + difference 1 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 1) (sourceB1975 + difference 1 3) sourceC1975) = raw28096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28096; decide +kernel
    rw [ha]
    exact (canonical28096 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 2) (sourceB1975 + difference 2 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 2) (sourceB1975 + difference 2 3) sourceC1975) = raw28097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28097; decide +kernel
    rw [ha]
    exact (canonical28097 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 4) (sourceB1975 + difference 4 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 4) (sourceB1975 + difference 4 3) sourceC1975) = raw28098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28098; decide +kernel
    rw [ha]
    exact (canonical28098 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1975 + difference 3 5) (sourceB1975 + difference 5 3) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1975 + difference 3 5) (sourceB1975 + difference 5 3) sourceC1975) = raw28099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28099; decide +kernel
    rw [ha]
    exact (canonical28099 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 0) (sourceB1975 + difference 0 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 0) (sourceB1975 + difference 0 4) sourceC1975) = raw28100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28100; decide +kernel
    rw [ha]
    exact (canonical28100 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 1) (sourceB1975 + difference 1 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 1) (sourceB1975 + difference 1 4) sourceC1975) = raw28101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28101; decide +kernel
    rw [ha]
    exact (canonical28101 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 2) (sourceB1975 + difference 2 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 2) (sourceB1975 + difference 2 4) sourceC1975) = raw28102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28102; decide +kernel
    rw [ha]
    exact (canonical28102 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 3) (sourceB1975 + difference 3 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 3) (sourceB1975 + difference 3 4) sourceC1975) = raw28103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28103; decide +kernel
    rw [ha]
    exact (canonical28103 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1975 + difference 4 5) (sourceB1975 + difference 5 4) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA1975 + difference 4 5) (sourceB1975 + difference 5 4) sourceC1975) = raw28104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28104; decide +kernel
    rw [ha]
    exact (canonical28104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 0) (sourceB1975 + difference 0 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 0) (sourceB1975 + difference 0 5) sourceC1975) = raw28105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28105; decide +kernel
    rw [ha]
    exact (canonical28105 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 1) (sourceB1975 + difference 1 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 1) (sourceB1975 + difference 1 5) sourceC1975) = raw28106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28106; decide +kernel
    rw [ha]
    exact (canonical28106 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 2) (sourceB1975 + difference 2 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 2) (sourceB1975 + difference 2 5) sourceC1975) = raw28107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28107; decide +kernel
    rw [ha]
    exact (canonical28107 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 3) (sourceB1975 + difference 3 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 3) (sourceB1975 + difference 3 5) sourceC1975) = raw28108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28108; decide +kernel
    rw [ha]
    exact (canonical28108 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1975 + difference 5 4) (sourceB1975 + difference 4 5) sourceC1975) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1975 + difference 5 4) (sourceB1975 + difference 4 5) sourceC1975) = raw28109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1975 sourceB1975 sourceC1975 difference raw28109; decide +kernel
    rw [ha]
    exact (canonical28109 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1975 sourceB1975 sourceC1975
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1975, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1976 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1976 + difference 0 1) (sourceB1976 + difference 1 0) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA1976 + difference 0 1) (sourceB1976 + difference 1 0) sourceC1976) = raw28110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28110; decide +kernel
    rw [ha]
    exact (canonical28110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1976 + difference 1 1) (sourceB1976 + difference 1 1) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1976 + difference 1 1) (sourceB1976 + difference 1 1) sourceC1976) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1976 + difference 2 1) (sourceB1976 + difference 1 2) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1956) := by
    have ha : (tripleCharges (sourceA1976 + difference 2 1) (sourceB1976 + difference 1 2) sourceC1976) = raw28112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28112; decide +kernel
    rw [ha]
    exact (canonical28112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1976 + difference 3 1) (sourceB1976 + difference 1 3) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1979) := by
    have ha : (tripleCharges (sourceA1976 + difference 3 1) (sourceB1976 + difference 1 3) sourceC1976) = raw28113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28113; decide +kernel
    rw [ha]
    exact (canonical28113 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1976 + difference 4 1) (sourceB1976 + difference 1 4) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA1976 + difference 4 1) (sourceB1976 + difference 1 4) sourceC1976) = raw28114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28114; decide +kernel
    rw [ha]
    exact (canonical28114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1976 + difference 5 1) (sourceB1976 + difference 1 5) sourceC1976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA1976 + difference 5 1) (sourceB1976 + difference 1 5) sourceC1976) = raw28115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1976 sourceB1976 sourceC1976 difference raw28115; decide +kernel
    rw [ha]
    exact (canonical28115 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1976 + sourceB1976) sourceC1976) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1976 + sourceB1976) sourceC1976) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1976 sourceB1976 sourceC1976 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1976 sourceB1976 sourceC1976
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1976, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1977 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 0) (sourceB1977 + difference 0 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1326) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 0) (sourceB1977 + difference 0 2) sourceC1977) = raw28117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28117; decide +kernel
    rw [ha]
    exact (canonical28117 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 1) (sourceB1977 + difference 1 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1956) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 1) (sourceB1977 + difference 1 2) sourceC1977) = raw28112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28112; decide +kernel
    rw [ha]
    exact (canonical28112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 2) (sourceB1977 + difference 2 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 2) (sourceB1977 + difference 2 2) sourceC1977) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 3) (sourceB1977 + difference 3 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 3) (sourceB1977 + difference 3 2) sourceC1977) = raw28118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28118; decide +kernel
    rw [ha]
    exact (canonical28118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 4) (sourceB1977 + difference 4 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 4) (sourceB1977 + difference 4 2) sourceC1977) = raw28119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28119; decide +kernel
    rw [ha]
    exact (canonical28119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1977 + difference 2 5) (sourceB1977 + difference 5 2) sourceC1977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA1977 + difference 2 5) (sourceB1977 + difference 5 2) sourceC1977) = raw28120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1977 sourceB1977 sourceC1977 difference raw28120; decide +kernel
    rw [ha]
    exact (canonical28120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1977 + sourceB1977) sourceC1977) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1977 + sourceB1977) sourceC1977) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1977 sourceB1977 sourceC1977 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1977 sourceB1977 sourceC1977
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1977, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1978 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1978 + difference 0 3) (sourceB1978 + difference 3 0) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA1978 + difference 0 3) (sourceB1978 + difference 3 0) sourceC1978) = raw28121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28121; decide +kernel
    rw [ha]
    exact (canonical28121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1978 + difference 1 3) (sourceB1978 + difference 3 1) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1978 + difference 1 3) (sourceB1978 + difference 3 1) sourceC1978) = raw28122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28122; decide +kernel
    rw [ha]
    exact (canonical28122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1978 + difference 2 3) (sourceB1978 + difference 3 2) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA1978 + difference 2 3) (sourceB1978 + difference 3 2) sourceC1978) = raw28118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28118; decide +kernel
    rw [ha]
    exact (canonical28118 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1978 + difference 3 3) (sourceB1978 + difference 3 3) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1978 + difference 3 3) (sourceB1978 + difference 3 3) sourceC1978) = raw28111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28111; decide +kernel
    rw [ha]
    exact (canonical28111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1978 + difference 4 3) (sourceB1978 + difference 3 4) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA1978 + difference 4 3) (sourceB1978 + difference 3 4) sourceC1978) = raw28123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28123; decide +kernel
    rw [ha]
    exact (canonical28123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1978 + difference 5 3) (sourceB1978 + difference 3 5) sourceC1978) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1978 + difference 5 3) (sourceB1978 + difference 3 5) sourceC1978) = raw28124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1978 sourceB1978 sourceC1978 difference raw28124; decide +kernel
    rw [ha]
    exact (canonical28124 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1978 + sourceB1978) sourceC1978) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1978 + sourceB1978) sourceC1978) = raw28116 := by
      apply Matrix.ext; unfold doubleCharges sourceA1978 sourceB1978 sourceC1978 raw28116; decide +kernel
    rw [ha]
    exact (canonical28116 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1978 sourceB1978 sourceC1978
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1978, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1664 : Integer.Sparse.reindex keyMap MixedData.row1664 = numericRow1664 := by decide +kernel

theorem numericCheck1664 (x : Master → ℝ) : Integer.Sparse.eval numericRow1664 x =
    (1 : ℝ) * reducedSource1664 x := by
  norm_num [numericRow1664, reducedSource1664, Integer.Sparse.eval, Sparse.eval, nodeValue1320, nodeValue2815, nodeValue2847, nodeValue2865, nodeValue2884, nodeValue4091]

theorem reindexCheck1665 : Integer.Sparse.reindex keyMap MixedData.row1665 = numericRow1665 := by decide +kernel

theorem numericCheck1665 (x : Master → ℝ) : Integer.Sparse.eval numericRow1665 x =
    (1 : ℝ) * reducedSource1665 x := by
  norm_num [numericRow1665, reducedSource1665, Integer.Sparse.eval, Sparse.eval, nodeValue1334, nodeValue2797, nodeValue2802, nodeValue2815, nodeValue2865, nodeValue2931, nodeValue4091]

theorem reindexCheck1666 : Integer.Sparse.reindex keyMap MixedData.row1666 = numericRow1666 := by decide +kernel

theorem numericCheck1666 (x : Master → ℝ) : Integer.Sparse.eval numericRow1666 x =
    (1 : ℝ) * reducedSource1666 x := by
  norm_num [numericRow1666, reducedSource1666, Integer.Sparse.eval, Sparse.eval, nodeValue2018, nodeValue2074, nodeValue2081, nodeValue2099, nodeValue2203, nodeValue3530, nodeValue4081]

theorem reindexCheck1667 : Integer.Sparse.reindex keyMap MixedData.row1667 = numericRow1667 := by decide +kernel

theorem numericCheck1667 (x : Master → ℝ) : Integer.Sparse.eval numericRow1667 x =
    (1 : ℝ) * reducedSource1667 x := by
  norm_num [numericRow1667, reducedSource1667, Integer.Sparse.eval, Sparse.eval, nodeValue2015, nodeValue2018, nodeValue2027, nodeValue2047, nodeValue2261, nodeValue3530, nodeValue4081]

theorem reindexCheck1670 : Integer.Sparse.reindex keyMap MixedData.row1670 = numericRow1670 := by decide +kernel

theorem numericCheck1670 (x : Master → ℝ) : Integer.Sparse.eval numericRow1670 x =
    (1 : ℝ) * reducedSource1670 x := by
  norm_num [numericRow1670, reducedSource1670, Integer.Sparse.eval, Sparse.eval, nodeValue1670, nodeValue1672, nodeValue1676, nodeValue1689, nodeValue1723, nodeValue3260, nodeValue3272, nodeValue3273, nodeValue3291, nodeValue3408, nodeValue3413, nodeValue3419, nodeValue3420, nodeValue3451, nodeValue3455, nodeValue3466, nodeValue3467, nodeValue3481, nodeValue3482, nodeValue3483, nodeValue3519, nodeValue3523, nodeValue3543, nodeValue3544, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3816]

theorem reindexCheck1671 : Integer.Sparse.reindex keyMap MixedData.row1671 = numericRow1671 := by decide +kernel

theorem numericCheck1671 (x : Master → ℝ) : Integer.Sparse.eval numericRow1671 x =
    (1 : ℝ) * reducedSource1671 x := by
  norm_num [numericRow1671, reducedSource1671, Integer.Sparse.eval, Sparse.eval, nodeValue1136, nodeValue2339, nodeValue2429, nodeValue2485, nodeValue2514, nodeValue4091]

theorem reindexCheck1674 : Integer.Sparse.reindex keyMap MixedData.row1674 = numericRow1674 := by decide +kernel

theorem numericCheck1674 (x : Master → ℝ) : Integer.Sparse.eval numericRow1674 x =
    (5760 : ℝ) * reducedSource1674 x := by
  norm_num [numericRow1674, reducedSource1674, Integer.Sparse.eval, Sparse.eval, nodeValue909, nodeValue911, nodeValue914, nodeValue931, nodeValue1024, nodeValue1327, nodeValue1333, nodeValue1340, nodeValue1413, nodeValue2323, nodeValue2327, nodeValue2340, nodeValue2423, nodeValue2430, nodeValue2471, nodeValue2528, nodeValue2532, nodeValue2573, nodeValue2574, nodeValue2575, nodeValue2600, nodeValue2602, nodeValue2754, nodeValue2755, nodeValue3109, nodeValue3204, nodeValue3207, nodeValue3213, nodeValue3229]
  ring

theorem reindexCheck1675 : Integer.Sparse.reindex keyMap MixedData.row1675 = numericRow1675 := by decide +kernel

theorem numericCheck1675 (x : Master → ℝ) : Integer.Sparse.eval numericRow1675 x =
    (1 : ℝ) * reducedSource1675 x := by
  norm_num [numericRow1675, reducedSource1675, Integer.Sparse.eval, Sparse.eval, nodeValue1670, nodeValue1684, nodeValue1685, nodeValue1686, nodeValue1688, nodeValue1689, nodeValue1690, nodeValue1744, nodeValue1750, nodeValue2147, nodeValue2164, nodeValue2165, nodeValue2181, nodeValue2182, nodeValue2198, nodeValue2201, nodeValue2202, nodeValue2223, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2287, nodeValue2290, nodeValue2291, nodeValue2681, nodeValue2700, nodeValue2735, nodeValue2738, nodeValue2739]

theorem reindexCheck1676 : Integer.Sparse.reindex keyMap MixedData.row1676 = numericRow1676 := by decide +kernel

theorem numericCheck1676 (x : Master → ℝ) : Integer.Sparse.eval numericRow1676 x =
    (1 : ℝ) * reducedSource1676 x := by
  norm_num [numericRow1676, reducedSource1676, Integer.Sparse.eval, Sparse.eval, nodeValue913, nodeValue1796, nodeValue1956, nodeValue1979, nodeValue2025, nodeValue2029, nodeValue4083]

theorem reindexCheck1677 : Integer.Sparse.reindex keyMap MixedData.row1677 = numericRow1677 := by decide +kernel

theorem numericCheck1677 (x : Master → ℝ) : Integer.Sparse.eval numericRow1677 x =
    (1 : ℝ) * reducedSource1677 x := by
  norm_num [numericRow1677, reducedSource1677, Integer.Sparse.eval, Sparse.eval, nodeValue1326, nodeValue1956, nodeValue1964, nodeValue2025, nodeValue2923, nodeValue4083]

theorem reindexCheck1678 : Integer.Sparse.reindex keyMap MixedData.row1678 = numericRow1678 := by decide +kernel

theorem numericCheck1678 (x : Master → ℝ) : Integer.Sparse.eval numericRow1678 x =
    (1 : ℝ) * reducedSource1678 x := by
  norm_num [numericRow1678, reducedSource1678, Integer.Sparse.eval, Sparse.eval, nodeValue930, nodeValue1812, nodeValue1964, nodeValue2025, nodeValue2057, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1664 (mixedVector B) = 0 := by
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1959, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1320, h2815, h2847, h2865, h2884, h4091, reducedSource1664] using sourceEq1959 B hB

theorem rowSound1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1664 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1664, numericCheck1664, reducedZero1664 B hB hF, mul_zero]

theorem reducedZero1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1665 (mixedVector B) = 0 := by
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1960, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1334, h2797, h2802, h2815, h2865, h2931, h4091, reducedSource1665] using sourceEq1960 B hB

theorem rowSound1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1665 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1665, numericCheck1665, reducedZero1665 B hB hF, mul_zero]

theorem reducedZero1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1666 (mixedVector B) = 0 := by
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2099 : mixedVector B (Sum.inr 2099) = Sparse.eval nodeValue2099 (mixedVector B) := by
    change mixedMoment B node2099 node2099Labels = _
    exact sound2099 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1961, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2018, h2074, h2081, h2099, h2203, h3530, h4081, reducedSource1666] using sourceEq1961 B hB

theorem rowSound1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1666 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1666, numericCheck1666, reducedZero1666 B hB hF, mul_zero]

theorem reducedZero1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1667 (mixedVector B) = 0 := by
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2027 : mixedVector B (Sum.inr 2027) = Sparse.eval nodeValue2027 (mixedVector B) := by
    change mixedMoment B node2027 node2027Labels = _
    exact sound2027 B hB hF
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1962, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2015, h2018, h2027, h2047, h2261, h3530, h4081, reducedSource1667] using sourceEq1962 B hB

theorem rowSound1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1667 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1667, numericCheck1667, reducedZero1667 B hB hF, mul_zero]

theorem reducedZero1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1670 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
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
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  simpa only [sourceForm1967, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1672, h1676, h1689, h1723, h3260, h3272, h3273, h3291, h3408, h3413, h3419, h3420, h3451, h3455, h3466, h3467, h3481, h3482, h3483, h3519, h3523, h3543, h3544, h3605, h3606, h3612, h3625, h3816, reducedSource1670] using sourceEq1967 B hB

theorem rowSound1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1670 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1670, numericCheck1670, reducedZero1670 B hB hF, mul_zero]

theorem reducedZero1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1671 (mixedVector B) = 0 := by
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h2339 : mixedVector B (Sum.inr 2339) = Sparse.eval nodeValue2339 (mixedVector B) := by
    change mixedMoment B node2339 node2339Labels = _
    exact sound2339 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2514 : mixedVector B (Sum.inr 2514) = Sparse.eval nodeValue2514 (mixedVector B) := by
    change mixedMoment B node2514 node2514Labels = _
    exact sound2514 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1968, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1136, h2339, h2429, h2485, h2514, h4091, reducedSource1671] using sourceEq1968 B hB

theorem rowSound1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1671 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1671, numericCheck1671, reducedZero1671 B hB hF, mul_zero]

theorem rowSound1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1674 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1674, numericCheck1674, reducedZero1674_e B hB hF, mul_zero]

theorem reducedZero1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1675 (mixedVector B) = 0 := by
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1686 : mixedVector B (Sum.inr 1686) = Sparse.eval nodeValue1686 (mixedVector B) := by
    change mixedMoment B node1686 node1686Labels = _
    exact sound1686 B hB hF
  have h1688 : mixedVector B (Sum.inr 1688) = Sparse.eval nodeValue1688 (mixedVector B) := by
    change mixedMoment B node1688 node1688Labels = _
    exact sound1688 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1690 : mixedVector B (Sum.inr 1690) = Sparse.eval nodeValue1690 (mixedVector B) := by
    change mixedMoment B node1690 node1690Labels = _
    exact sound1690 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2147 : mixedVector B (Sum.inr 2147) = Sparse.eval nodeValue2147 (mixedVector B) := by
    change mixedMoment B node2147 node2147Labels = _
    exact sound2147 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2182 : mixedVector B (Sum.inr 2182) = Sparse.eval nodeValue2182 (mixedVector B) := by
    change mixedMoment B node2182 node2182Labels = _
    exact sound2182 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm1975, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1670, h1684, h1685, h1686, h1688, h1689, h1690, h1744, h1750, h2147, h2164, h2165, h2181, h2182, h2198, h2201, h2202, h2223, h2224, h2225, h2227, h2287, h2290, h2291, h2681, h2700, h2735, h2738, h2739, reducedSource1675] using sourceEq1975 B hB

theorem rowSound1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1675 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1675, numericCheck1675, reducedZero1675 B hB hF, mul_zero]

theorem reducedZero1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1676 (mixedVector B) = 0 := by
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h1796 : mixedVector B (Sum.inr 1796) = Sparse.eval nodeValue1796 (mixedVector B) := by
    change mixedMoment B node1796 node1796Labels = _
    exact sound1796 B hB hF
  have h1956 : mixedVector B (Sum.inr 1956) = Sparse.eval nodeValue1956 (mixedVector B) := by
    change mixedMoment B node1956 node1956Labels = _
    exact sound1956 B hB hF
  have h1979 : mixedVector B (Sum.inr 1979) = Sparse.eval nodeValue1979 (mixedVector B) := by
    change mixedMoment B node1979 node1979Labels = _
    exact sound1979 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1976, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h913, h1796, h1956, h1979, h2025, h2029, h4083, reducedSource1676] using sourceEq1976 B hB

theorem rowSound1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1676 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1676, numericCheck1676, reducedZero1676 B hB hF, mul_zero]

theorem reducedZero1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1677 (mixedVector B) = 0 := by
  have h1326 : mixedVector B (Sum.inr 1326) = Sparse.eval nodeValue1326 (mixedVector B) := by
    change mixedMoment B node1326 node1326Labels = _
    exact sound1326 B hB hF
  have h1956 : mixedVector B (Sum.inr 1956) = Sparse.eval nodeValue1956 (mixedVector B) := by
    change mixedMoment B node1956 node1956Labels = _
    exact sound1956 B hB hF
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1977, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1326, h1956, h1964, h2025, h2923, h4083, reducedSource1677] using sourceEq1977 B hB

theorem rowSound1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1677 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1677, numericCheck1677, reducedZero1677 B hB hF, mul_zero]

theorem reducedZero1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1678 (mixedVector B) = 0 := by
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2057 : mixedVector B (Sum.inr 2057) = Sparse.eval nodeValue2057 (mixedVector B) := by
    change mixedMoment B node2057 node2057Labels = _
    exact sound2057 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1978, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h930, h1812, h1964, h2025, h2057, h4083, reducedSource1678] using sourceEq1978 B hB

theorem rowSound1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1678 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1678, numericCheck1678, reducedZero1678 B hB hF, mul_zero]

theorem sourceRowsAt1664 : MixedData.sourceRows (1664 : Fin 2425) =
    MixedData.row1664 := by decide +kernel

theorem sourceRowsAt1665 : MixedData.sourceRows (1665 : Fin 2425) =
    MixedData.row1665 := by decide +kernel

theorem sourceRowsAt1666 : MixedData.sourceRows (1666 : Fin 2425) =
    MixedData.row1666 := by decide +kernel

theorem sourceRowsAt1667 : MixedData.sourceRows (1667 : Fin 2425) =
    MixedData.row1667 := by decide +kernel

theorem sourceRowsAt1668 : MixedData.sourceRows (1668 : Fin 2425) =
    MixedData.row1668 := by decide +kernel

theorem sourceRowsAt1669 : MixedData.sourceRows (1669 : Fin 2425) =
    MixedData.row1669 := by decide +kernel

theorem sourceRowsAt1670 : MixedData.sourceRows (1670 : Fin 2425) =
    MixedData.row1670 := by decide +kernel

theorem sourceRowsAt1671 : MixedData.sourceRows (1671 : Fin 2425) =
    MixedData.row1671 := by decide +kernel

theorem sourceRowsAt1672 : MixedData.sourceRows (1672 : Fin 2425) =
    MixedData.row1672 := by decide +kernel

theorem sourceRowsAt1673 : MixedData.sourceRows (1673 : Fin 2425) =
    MixedData.row1673 := by decide +kernel

theorem sourceRowsAt1674 : MixedData.sourceRows (1674 : Fin 2425) =
    MixedData.row1674 := by decide +kernel

theorem sourceRowsAt1675 : MixedData.sourceRows (1675 : Fin 2425) =
    MixedData.row1675 := by decide +kernel

theorem sourceRowsAt1676 : MixedData.sourceRows (1676 : Fin 2425) =
    MixedData.row1676 := by decide +kernel

theorem sourceRowsAt1677 : MixedData.sourceRows (1677 : Fin 2425) =
    MixedData.row1677 := by decide +kernel

theorem sourceRowsAt1678 : MixedData.sourceRows (1678 : Fin 2425) =
    MixedData.row1678 := by decide +kernel

theorem sourceRowsAt1679 : MixedData.sourceRows (1679 : Fin 2425) =
    MixedData.row1679 := by decide +kernel

theorem chunkSound104_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 104) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1664 ∨ k.val = 1665 ∨ k.val = 1666 ∨ k.val = 1667 ∨ k.val = 1668 ∨ k.val = 1669 ∨ k.val = 1670 ∨ k.val = 1671 ∨ k.val = 1672 ∨ k.val = 1673 ∨ k.val = 1674 ∨ k.val = 1675 ∨ k.val = 1676 ∨ k.val = 1677 ∨ k.val = 1678 ∨ k.val = 1679 := by omega
  rcases heq with h1664 | h1665 | h1666 | h1667 | h1668 | h1669 | h1670 | h1671 | h1672 | h1673 | h1674 | h1675 | h1676 | h1677 | h1678 | h1679
  · have he : k = (1664 : Fin 2425) := Fin.ext h1664
    subst k
    rw [sourceRowsAt1664]
    exact rowSound1664 B hB hF
  · have he : k = (1665 : Fin 2425) := Fin.ext h1665
    subst k
    rw [sourceRowsAt1665]
    exact rowSound1665 B hB hF
  · have he : k = (1666 : Fin 2425) := Fin.ext h1666
    subst k
    rw [sourceRowsAt1666]
    exact rowSound1666 B hB hF
  · have he : k = (1667 : Fin 2425) := Fin.ext h1667
    subst k
    rw [sourceRowsAt1667]
    exact rowSound1667 B hB hF
  · have he : k = (1668 : Fin 2425) := Fin.ext h1668
    subst k
    rw [sourceRowsAt1668]
    exact rowSound1668_e B hB hF
  · have he : k = (1669 : Fin 2425) := Fin.ext h1669
    subst k
    rw [sourceRowsAt1669]
    exact rowSound1669_e B hB hF
  · have he : k = (1670 : Fin 2425) := Fin.ext h1670
    subst k
    rw [sourceRowsAt1670]
    exact rowSound1670 B hB hF
  · have he : k = (1671 : Fin 2425) := Fin.ext h1671
    subst k
    rw [sourceRowsAt1671]
    exact rowSound1671 B hB hF
  · have he : k = (1672 : Fin 2425) := Fin.ext h1672
    subst k
    rw [sourceRowsAt1672]
    exact rowSound1672_e B hB hF
  · have he : k = (1673 : Fin 2425) := Fin.ext h1673
    subst k
    rw [sourceRowsAt1673]
    exact rowSound1673_e B hB hF
  · have he : k = (1674 : Fin 2425) := Fin.ext h1674
    subst k
    rw [sourceRowsAt1674]
    exact rowSound1674 B hB hF
  · have he : k = (1675 : Fin 2425) := Fin.ext h1675
    subst k
    rw [sourceRowsAt1675]
    exact rowSound1675 B hB hF
  · have he : k = (1676 : Fin 2425) := Fin.ext h1676
    subst k
    rw [sourceRowsAt1676]
    exact rowSound1676 B hB hF
  · have he : k = (1677 : Fin 2425) := Fin.ext h1677
    subst k
    rw [sourceRowsAt1677]
    exact rowSound1677 B hB hF
  · have he : k = (1678 : Fin 2425) := Fin.ext h1678
    subst k
    rw [sourceRowsAt1678]
    exact rowSound1678 B hB hF
  · have he : k = (1679 : Fin 2425) := Fin.ext h1679
    subst k
    rw [sourceRowsAt1679]
    exact rowSound1679_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e_oai
