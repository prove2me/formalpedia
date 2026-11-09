-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:11.89309+00:00
-- url     : https://prove2.me/submissions/324e8771-9913-4774-b5c2-23e70a312f79

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1191_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1194_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1195_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1197_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19408 raw19408Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19408 raw19408Labels = mixedMoment B raw19408step0 raw19408step0Labels := by
      have hz : ∀ j, raw19408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19408step0 = (fun i j => raw19408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19408step0 raw19408; decide +kernel
      have hl : raw19408step0Labels = raw19408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408 raw19408Labels permutation434 hz
    mixedMoment B raw19408step0 raw19408step0Labels = mixedMoment B raw19408step1 raw19408step1Labels := by
      have hz : ∀ j, raw19408step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19408step1 = (fun i j => raw19408step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19408step1 raw19408step0; decide +kernel
      have hl : raw19408step1Labels = raw19408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408step0 raw19408step0Labels permutation80 hz
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical19412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19412 raw19412Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw19412 raw19412Labels = mixedMoment B raw19412step0 raw19412step0Labels := by
      have hz : ∀ j, raw19412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19412step0 = (fun i j => raw19412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19412step0 raw19412; decide +kernel
      have hl : raw19412step0Labels = raw19412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412 raw19412Labels permutation434 hz
    mixedMoment B raw19412step0 raw19412step0Labels = mixedMoment B raw19412step1 raw19412step1Labels := by
      have hz : ∀ j, raw19412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19412step1 = (fun i j => raw19412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19412step1 raw19412step0; decide +kernel
      have hl : raw19412step1Labels = raw19412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step0 raw19412step0Labels permutation80 hz
    mixedMoment B raw19412step1 raw19412step1Labels = mixedMoment B raw19412step2 raw19412step2Labels := by
      have hz : ∀ j, raw19412step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19412step2 = (fun i j => raw19412step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19412step2 raw19412step1; decide +kernel
      have hl : raw19412step2Labels = raw19412step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step1 raw19412step1Labels permutation14 hz
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical19413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19413 raw19413Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw19413 raw19413Labels = mixedMoment B raw19413step0 raw19413step0Labels := by
      have hz : ∀ j, raw19413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19413step0 = (fun i j => raw19413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19413step0 raw19413; decide +kernel
      have hl : raw19413step0Labels = raw19413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413 raw19413Labels permutation434 hz
    mixedMoment B raw19413step0 raw19413step0Labels = mixedMoment B raw19413step1 raw19413step1Labels := by
      have hz : ∀ j, raw19413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19413step1 = (fun i j => raw19413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19413step1 raw19413step0; decide +kernel
      have hl : raw19413step1Labels = raw19413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step0 raw19413step0Labels permutation80 hz
    mixedMoment B raw19413step1 raw19413step1Labels = mixedMoment B raw19413step2 raw19413step2Labels := by
      have hz : ∀ j, raw19413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19413step2 = (fun i j => raw19413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19413step2 raw19413step1; decide +kernel
      have hl : raw19413step2Labels = raw19413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step1 raw19413step1Labels permutation14 hz
    mixedMoment B raw19413step2 raw19413step2Labels = mixedMoment B raw19413step3 raw19413step3Labels := by
      have ha : raw19413step3 = (fun i j => raw19413step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19413step3 raw19413step2; decide +kernel
      have hl : raw19413step3Labels = raw19413step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19413step2 raw19413step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19921 raw19921Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19921 raw19921Labels = mixedMoment B raw19921step0 raw19921step0Labels := by
      have hz : ∀ j, raw19921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19921step0 = (fun i j => raw19921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19921step0 raw19921; decide +kernel
      have hl : raw19921step0Labels = raw19921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921 raw19921Labels permutation520 hz
    mixedMoment B raw19921step0 raw19921step0Labels = mixedMoment B raw19921step1 raw19921step1Labels := by
      have hz : ∀ j, raw19921step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19921step1 = (fun i j => raw19921step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19921step1 raw19921step0; decide +kernel
      have hl : raw19921step1Labels = raw19921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step0 raw19921step0Labels permutation104 hz
    mixedMoment B raw19921step1 raw19921step1Labels = mixedMoment B raw19921step2 raw19921step2Labels := by
      have hz : ∀ j, raw19921step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19921step2 = (fun i j => raw19921step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19921step2 raw19921step1; decide +kernel
      have hl : raw19921step2Labels = raw19921step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step1 raw19921step1Labels permutation20 hz
    mixedMoment B raw19921step2 raw19921step2Labels = mixedMoment B raw19921step3 raw19921step3Labels := by
      have hz : ∀ j, raw19921step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19921step3 = (fun i j => raw19921step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19921step3 raw19921step2; decide +kernel
      have hl : raw19921step3Labels = raw19921step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step2 raw19921step2Labels permutation4 hz
    mixedMoment B raw19921step3 raw19921step3Labels = mixedMoment B raw19921step4 raw19921step4Labels := by
      have hz : ∀ i, raw19921step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19921step4 = (fun i j => raw19921step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19921step4 raw19921step3; decide +kernel
      have hl : raw19921step4Labels = (fun j => raw19921step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19921step3 raw19921step3Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical19926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19926 raw19926Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19926 raw19926Labels = mixedMoment B raw19926step0 raw19926step0Labels := by
      have hz : ∀ j, raw19926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19926step0 = (fun i j => raw19926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19926step0 raw19926; decide +kernel
      have hl : raw19926step0Labels = raw19926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926 raw19926Labels permutation520 hz
    mixedMoment B raw19926step0 raw19926step0Labels = mixedMoment B raw19926step1 raw19926step1Labels := by
      have hz : ∀ j, raw19926step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19926step1 = (fun i j => raw19926step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19926step1 raw19926step0; decide +kernel
      have hl : raw19926step1Labels = raw19926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step0 raw19926step0Labels permutation104 hz
    mixedMoment B raw19926step1 raw19926step1Labels = mixedMoment B raw19926step2 raw19926step2Labels := by
      have hz : ∀ j, raw19926step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19926step2 = (fun i j => raw19926step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19926step2 raw19926step1; decide +kernel
      have hl : raw19926step2Labels = raw19926step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step1 raw19926step1Labels permutation20 hz
    mixedMoment B raw19926step2 raw19926step2Labels = mixedMoment B raw19926step3 raw19926step3Labels := by
      have ha : raw19926step3 = (fun i j => raw19926step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19926step3 raw19926step2; decide +kernel
      have hl : raw19926step3Labels = raw19926step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19926step2 raw19926step2Labels permutation2 permutation7
    mixedMoment B raw19926step3 raw19926step3Labels = mixedMoment B raw19926step4 raw19926step4Labels := by
      have ha : raw19926step4 = -raw19926step3 := by apply Matrix.ext; change ∀ i j, raw19926step4 i j = -(raw19926step3 i j); unfold raw19926step4 raw19926step3; decide +kernel
      have hl : raw19926step4Labels = raw19926step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19926step4 raw19926step4Labels = mixedMoment B raw19926step5 raw19926step5Labels := by
      have ha : raw19926step5 = raw19926step4 := by apply Matrix.ext; unfold raw19926step5 raw19926step4; decide +kernel
      have hl : raw19926step4Labels = labelEmbedding1 ∘ raw19926step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19926step4 raw19926step4Labels raw19926step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19931 raw19931Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19931 raw19931Labels = mixedMoment B raw19931step0 raw19931step0Labels := by
      have hz : ∀ j, raw19931 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19931step0 = (fun i j => raw19931 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19931step0 raw19931; decide +kernel
      have hl : raw19931step0Labels = raw19931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931 raw19931Labels permutation520 hz
    mixedMoment B raw19931step0 raw19931step0Labels = mixedMoment B raw19931step1 raw19931step1Labels := by
      have hz : ∀ j, raw19931step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19931step1 = (fun i j => raw19931step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19931step1 raw19931step0; decide +kernel
      have hl : raw19931step1Labels = raw19931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step0 raw19931step0Labels permutation104 hz
    mixedMoment B raw19931step1 raw19931step1Labels = mixedMoment B raw19931step2 raw19931step2Labels := by
      have hz : ∀ j, raw19931step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19931step2 = (fun i j => raw19931step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19931step2 raw19931step1; decide +kernel
      have hl : raw19931step2Labels = raw19931step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step1 raw19931step1Labels permutation14 hz
    mixedMoment B raw19931step2 raw19931step2Labels = mixedMoment B raw19931step3 raw19931step3Labels := by
      have ha : raw19931step3 = (fun i j => raw19931step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19931step3 raw19931step2; decide +kernel
      have hl : raw19931step3Labels = raw19931step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19931step2 raw19931step2Labels permutation2 permutation7
    mixedMoment B raw19931step3 raw19931step3Labels = mixedMoment B raw19931step4 raw19931step4Labels := by
      have ha : raw19931step4 = -raw19931step3 := by apply Matrix.ext; change ∀ i j, raw19931step4 i j = -(raw19931step3 i j); unfold raw19931step4 raw19931step3; decide +kernel
      have hl : raw19931step4Labels = raw19931step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19931step4 raw19931step4Labels = mixedMoment B raw19931step5 raw19931step5Labels := by
      have ha : raw19931step5 = raw19931step4 := by apply Matrix.ext; unfold raw19931step5 raw19931step4; decide +kernel
      have hl : raw19931step4Labels = labelEmbedding1 ∘ raw19931step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19931step4 raw19931step4Labels raw19931step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19936 raw19936Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19936 raw19936Labels = mixedMoment B raw19936step0 raw19936step0Labels := by
      have hz : ∀ j, raw19936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19936step0 = (fun i j => raw19936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19936step0 raw19936; decide +kernel
      have hl : raw19936step0Labels = raw19936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936 raw19936Labels permutation520 hz
    mixedMoment B raw19936step0 raw19936step0Labels = mixedMoment B raw19936step1 raw19936step1Labels := by
      have hz : ∀ j, raw19936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19936step1 = (fun i j => raw19936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19936step1 raw19936step0; decide +kernel
      have hl : raw19936step1Labels = raw19936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step0 raw19936step0Labels permutation80 hz
    mixedMoment B raw19936step1 raw19936step1Labels = mixedMoment B raw19936step2 raw19936step2Labels := by
      have hz : ∀ j, raw19936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19936step2 = (fun i j => raw19936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19936step2 raw19936step1; decide +kernel
      have hl : raw19936step2Labels = raw19936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step1 raw19936step1Labels permutation14 hz
    mixedMoment B raw19936step2 raw19936step2Labels = mixedMoment B raw19936step3 raw19936step3Labels := by
      have ha : raw19936step3 = (fun i j => raw19936step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19936step3 raw19936step2; decide +kernel
      have hl : raw19936step3Labels = raw19936step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19936step2 raw19936step2Labels permutation2 permutation7
    mixedMoment B raw19936step3 raw19936step3Labels = mixedMoment B raw19936step4 raw19936step4Labels := by
      have ha : raw19936step4 = -raw19936step3 := by apply Matrix.ext; change ∀ i j, raw19936step4 i j = -(raw19936step3 i j); unfold raw19936step4 raw19936step3; decide +kernel
      have hl : raw19936step4Labels = raw19936step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19936step4 raw19936step4Labels = mixedMoment B raw19936step5 raw19936step5Labels := by
      have ha : raw19936step5 = raw19936step4 := by apply Matrix.ext; unfold raw19936step5 raw19936step4; decide +kernel
      have hl : raw19936step4Labels = labelEmbedding1 ∘ raw19936step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19936step4 raw19936step4Labels raw19936step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical19937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19937 raw19937Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19937 raw19937Labels = mixedMoment B raw19937step0 raw19937step0Labels := by
      have hz : ∀ j, raw19937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19937step0 = (fun i j => raw19937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19937step0 raw19937; decide +kernel
      have hl : raw19937step0Labels = raw19937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937 raw19937Labels permutation434 hz
    mixedMoment B raw19937step0 raw19937step0Labels = mixedMoment B raw19937step1 raw19937step1Labels := by
      have hz : ∀ j, raw19937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19937step1 = (fun i j => raw19937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19937step1 raw19937step0; decide +kernel
      have hl : raw19937step1Labels = raw19937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step0 raw19937step0Labels permutation80 hz
    mixedMoment B raw19937step1 raw19937step1Labels = mixedMoment B raw19937step2 raw19937step2Labels := by
      have hz : ∀ j, raw19937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19937step2 = (fun i j => raw19937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19937step2 raw19937step1; decide +kernel
      have hl : raw19937step2Labels = raw19937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step1 raw19937step1Labels permutation14 hz
    mixedMoment B raw19937step2 raw19937step2Labels = mixedMoment B raw19937step3 raw19937step3Labels := by
      have ha : raw19937step3 = (fun i j => raw19937step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19937step3 raw19937step2; decide +kernel
      have hl : raw19937step3Labels = raw19937step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19937step2 raw19937step2Labels permutation2 permutation7
    mixedMoment B raw19937step3 raw19937step3Labels = mixedMoment B raw19937step4 raw19937step4Labels := by
      have ha : raw19937step4 = -raw19937step3 := by apply Matrix.ext; change ∀ i j, raw19937step4 i j = -(raw19937step3 i j); unfold raw19937step4 raw19937step3; decide +kernel
      have hl : raw19937step4Labels = raw19937step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19937step4 raw19937step4Labels = mixedMoment B raw19937step5 raw19937step5Labels := by
      have ha : raw19937step5 = raw19937step4 := by apply Matrix.ext; unfold raw19937step5 raw19937step4; decide +kernel
      have hl : raw19937step4Labels = labelEmbedding1 ∘ raw19937step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19937step4 raw19937step4Labels raw19937step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical19938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19938 raw19938Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19938 raw19938Labels = mixedMoment B raw19938step0 raw19938step0Labels := by
      have hz : ∀ j, raw19938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19938step0 = (fun i j => raw19938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19938step0 raw19938; decide +kernel
      have hl : raw19938step0Labels = raw19938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938 raw19938Labels permutation434 hz
    mixedMoment B raw19938step0 raw19938step0Labels = mixedMoment B raw19938step1 raw19938step1Labels := by
      have hz : ∀ j, raw19938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19938step1 = (fun i j => raw19938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19938step1 raw19938step0; decide +kernel
      have hl : raw19938step1Labels = raw19938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938step0 raw19938step0Labels permutation80 hz
    mixedMoment B raw19938step1 raw19938step1Labels = mixedMoment B raw19938step2 raw19938step2Labels := by
      have ha : raw19938step2 = (fun i j => raw19938step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19938step2 raw19938step1; decide +kernel
      have hl : raw19938step2Labels = raw19938step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19938step1 raw19938step1Labels permutation31 permutation7
    mixedMoment B raw19938step2 raw19938step2Labels = mixedMoment B raw19938step3 raw19938step3Labels := by
      have ha : raw19938step3 = raw19938step2 := by apply Matrix.ext; unfold raw19938step3 raw19938step2; decide +kernel
      have hl : raw19938step2Labels = labelEmbedding1 ∘ raw19938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19938step2 raw19938step2Labels raw19938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19939 raw19939Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19939 raw19939Labels = mixedMoment B raw19939step0 raw19939step0Labels := by
      have hz : ∀ j, raw19939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19939step0 = (fun i j => raw19939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19939step0 raw19939; decide +kernel
      have hl : raw19939step0Labels = raw19939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939 raw19939Labels permutation434 hz
    mixedMoment B raw19939step0 raw19939step0Labels = mixedMoment B raw19939step1 raw19939step1Labels := by
      have hz : ∀ j, raw19939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19939step1 = (fun i j => raw19939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19939step1 raw19939step0; decide +kernel
      have hl : raw19939step1Labels = raw19939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939step0 raw19939step0Labels permutation56 hz
    mixedMoment B raw19939step1 raw19939step1Labels = mixedMoment B raw19939step2 raw19939step2Labels := by
      have ha : raw19939step2 = (fun i j => raw19939step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19939step2 raw19939step1; decide +kernel
      have hl : raw19939step2Labels = raw19939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19939step1 raw19939step1Labels permutation31 permutation7
    mixedMoment B raw19939step2 raw19939step2Labels = mixedMoment B raw19939step3 raw19939step3Labels := by
      have ha : raw19939step3 = raw19939step2 := by apply Matrix.ext; unfold raw19939step3 raw19939step2; decide +kernel
      have hl : raw19939step2Labels = labelEmbedding1 ∘ raw19939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19939step2 raw19939step2Labels raw19939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19940 raw19940Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19940 raw19940Labels = mixedMoment B raw19940step0 raw19940step0Labels := by
      have hz : ∀ j, raw19940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19940step0 = (fun i j => raw19940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19940step0 raw19940; decide +kernel
      have hl : raw19940step0Labels = raw19940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940 raw19940Labels permutation346 hz
    mixedMoment B raw19940step0 raw19940step0Labels = mixedMoment B raw19940step1 raw19940step1Labels := by
      have hz : ∀ j, raw19940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19940step1 = (fun i j => raw19940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19940step1 raw19940step0; decide +kernel
      have hl : raw19940step1Labels = raw19940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940step0 raw19940step0Labels permutation56 hz
    mixedMoment B raw19940step1 raw19940step1Labels = mixedMoment B raw19940step2 raw19940step2Labels := by
      have ha : raw19940step2 = (fun i j => raw19940step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19940step2 raw19940step1; decide +kernel
      have hl : raw19940step2Labels = raw19940step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19940step1 raw19940step1Labels permutation31 permutation7
    mixedMoment B raw19940step2 raw19940step2Labels = mixedMoment B raw19940step3 raw19940step3Labels := by
      have ha : raw19940step3 = raw19940step2 := by apply Matrix.ext; unfold raw19940step3 raw19940step2; decide +kernel
      have hl : raw19940step2Labels = labelEmbedding1 ∘ raw19940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19940step2 raw19940step2Labels raw19940step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

theorem canonical19951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19951 raw19951Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19951 raw19951Labels = mixedMoment B raw19951step0 raw19951step0Labels := by
      have hz : ∀ j, raw19951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19951step0 = (fun i j => raw19951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19951step0 raw19951; decide +kernel
      have hl : raw19951step0Labels = raw19951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951 raw19951Labels permutation434 hz
    mixedMoment B raw19951step0 raw19951step0Labels = mixedMoment B raw19951step1 raw19951step1Labels := by
      have hz : ∀ j, raw19951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19951step1 = (fun i j => raw19951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19951step1 raw19951step0; decide +kernel
      have hl : raw19951step1Labels = raw19951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step0 raw19951step0Labels permutation80 hz
    mixedMoment B raw19951step1 raw19951step1Labels = mixedMoment B raw19951step2 raw19951step2Labels := by
      have hz : ∀ j, raw19951step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19951step2 = (fun i j => raw19951step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19951step2 raw19951step1; decide +kernel
      have hl : raw19951step2Labels = raw19951step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step1 raw19951step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical19953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19953 raw19953Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19953 raw19953Labels = mixedMoment B raw19953step0 raw19953step0Labels := by
      have hz : ∀ j, raw19953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19953step0 = (fun i j => raw19953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19953step0 raw19953; decide +kernel
      have hl : raw19953step0Labels = raw19953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953 raw19953Labels permutation520 hz
    mixedMoment B raw19953step0 raw19953step0Labels = mixedMoment B raw19953step1 raw19953step1Labels := by
      have hz : ∀ j, raw19953step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19953step1 = (fun i j => raw19953step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19953step1 raw19953step0; decide +kernel
      have hl : raw19953step1Labels = raw19953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step0 raw19953step0Labels permutation104 hz
    mixedMoment B raw19953step1 raw19953step1Labels = mixedMoment B raw19953step2 raw19953step2Labels := by
      have hz : ∀ j, raw19953step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19953step2 = (fun i j => raw19953step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19953step2 raw19953step1; decide +kernel
      have hl : raw19953step2Labels = raw19953step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step1 raw19953step1Labels permutation20 hz
    mixedMoment B raw19953step2 raw19953step2Labels = mixedMoment B raw19953step3 raw19953step3Labels := by
      have hz : ∀ j, raw19953step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19953step3 = (fun i j => raw19953step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19953step3 raw19953step2; decide +kernel
      have hl : raw19953step3Labels = raw19953step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step2 raw19953step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

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

theorem canonical20995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20995 raw20995Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20995 raw20995Labels = mixedMoment B raw20995step0 raw20995step0Labels := by
      have hz : ∀ j, raw20995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20995step0 = (fun i j => raw20995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20995step0 raw20995; decide +kernel
      have hl : raw20995step0Labels = raw20995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20995 raw20995Labels permutation346 hz
    mixedMoment B raw20995step0 raw20995step0Labels = mixedMoment B raw20995step1 raw20995step1Labels := by
      have ha : raw20995step1 = (fun i j => raw20995step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20995step1 raw20995step0; decide +kernel
      have hl : raw20995step1Labels = raw20995step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20995step0 raw20995step0Labels permutation40 permutation4
    mixedMoment B raw20995step1 raw20995step1Labels = mixedMoment B raw20995step2 raw20995step2Labels := by
      have ha : raw20995step2 = -raw20995step1 := by apply Matrix.ext; change ∀ i j, raw20995step2 i j = -(raw20995step1 i j); unfold raw20995step2 raw20995step1; decide +kernel
      have hl : raw20995step2Labels = raw20995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21578 raw21578Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw21578 raw21578Labels = mixedMoment B raw21578step0 raw21578step0Labels := by
      have hz : ∀ j, raw21578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21578step0 = (fun i j => raw21578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21578step0 raw21578; decide +kernel
      have hl : raw21578step0Labels = raw21578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578 raw21578Labels permutation434 hz
    mixedMoment B raw21578step0 raw21578step0Labels = mixedMoment B raw21578step1 raw21578step1Labels := by
      have hz : ∀ j, raw21578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21578step1 = (fun i j => raw21578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21578step1 raw21578step0; decide +kernel
      have hl : raw21578step1Labels = raw21578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578step0 raw21578step0Labels permutation80 hz
    mixedMoment B raw21578step1 raw21578step1Labels = mixedMoment B raw21578step2 raw21578step2Labels := by
      have ha : raw21578step2 = (fun i j => raw21578step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21578step2 raw21578step1; decide +kernel
      have hl : raw21578step2Labels = raw21578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21578step1 raw21578step1Labels permutation10 permutation4
    mixedMoment B raw21578step2 raw21578step2Labels = mixedMoment B raw21578step3 raw21578step3Labels := by
      have ha : raw21578step3 = -raw21578step2 := by apply Matrix.ext; change ∀ i j, raw21578step3 i j = -(raw21578step2 i j); unfold raw21578step3 raw21578step2; decide +kernel
      have hl : raw21578step3Labels = raw21578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical21580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21580 raw21580Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21580 raw21580Labels = mixedMoment B raw21580step0 raw21580step0Labels := by
      have hz : ∀ j, raw21580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21580step0 = (fun i j => raw21580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21580step0 raw21580; decide +kernel
      have hl : raw21580step0Labels = raw21580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21580 raw21580Labels permutation346 hz
    mixedMoment B raw21580step0 raw21580step0Labels = mixedMoment B raw21580step1 raw21580step1Labels := by
      have ha : raw21580step1 = (fun i j => raw21580step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21580step1 raw21580step0; decide +kernel
      have hl : raw21580step1Labels = raw21580step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21580step0 raw21580step0Labels permutation38 permutation2
    _ = mixedMoment B node983 node983Labels := by rfl

theorem canonical21585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21585 raw21585Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw21585 raw21585Labels = mixedMoment B raw21585step0 raw21585step0Labels := by
      have hz : ∀ j, raw21585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21585step0 = (fun i j => raw21585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21585step0 raw21585; decide +kernel
      have hl : raw21585step0Labels = raw21585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21585 raw21585Labels permutation346 hz
    mixedMoment B raw21585step0 raw21585step0Labels = mixedMoment B raw21585step1 raw21585step1Labels := by
      have ha : raw21585step1 = (fun i j => raw21585step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21585step1 raw21585step0; decide +kernel
      have hl : raw21585step1Labels = raw21585step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21585step0 raw21585step0Labels permutation38 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical21586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21586 raw21586Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21586 raw21586Labels = mixedMoment B raw21586step0 raw21586step0Labels := by
      have hz : ∀ j, raw21586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21586step0 = (fun i j => raw21586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21586step0 raw21586; decide +kernel
      have hl : raw21586step0Labels = raw21586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21586 raw21586Labels permutation346 hz
    mixedMoment B raw21586step0 raw21586step0Labels = mixedMoment B raw21586step1 raw21586step1Labels := by
      have ha : raw21586step1 = (fun i j => raw21586step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21586step1 raw21586step0; decide +kernel
      have hl : raw21586step1Labels = raw21586step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21586step0 raw21586step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21587 raw21587Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw21587 raw21587Labels = mixedMoment B raw21587step0 raw21587step0Labels := by
      have hz : ∀ j, raw21587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21587step0 = (fun i j => raw21587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21587step0 raw21587; decide +kernel
      have hl : raw21587step0Labels = raw21587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21587 raw21587Labels permutation346 hz
    mixedMoment B raw21587step0 raw21587step0Labels = mixedMoment B raw21587step1 raw21587step1Labels := by
      have ha : raw21587step1 = (fun i j => raw21587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21587step1 raw21587step0; decide +kernel
      have hl : raw21587step1Labels = raw21587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21587step0 raw21587step0Labels permutation38 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical21588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21588 raw21588Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw21588 raw21588Labels = mixedMoment B raw21588step0 raw21588step0Labels := by
      have ha : raw21588step0 = (fun i j => raw21588 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21588step0 raw21588; decide +kernel
      have hl : raw21588step0Labels = raw21588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21588 raw21588Labels permutation200 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

theorem canonical21589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21589 raw21589Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw21589 raw21589Labels = mixedMoment B raw21589step0 raw21589step0Labels := by
      have hz : ∀ j, raw21589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21589step0 = (fun i j => raw21589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21589step0 raw21589; decide +kernel
      have hl : raw21589step0Labels = raw21589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21589 raw21589Labels permutation346 hz
    _ = mixedMoment B node1036 node1036Labels := by rfl

theorem canonical21590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21590 raw21590Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw21590 raw21590Labels = mixedMoment B raw21590step0 raw21590step0Labels := by
      have hz : ∀ j, raw21590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21590step0 = (fun i j => raw21590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21590step0 raw21590; decide +kernel
      have hl : raw21590step0Labels = raw21590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21590 raw21590Labels permutation346 hz
    mixedMoment B raw21590step0 raw21590step0Labels = mixedMoment B raw21590step1 raw21590step1Labels := by
      have ha : raw21590step1 = (fun i j => raw21590step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21590step1 raw21590step0; decide +kernel
      have hl : raw21590step1Labels = raw21590step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21590step0 raw21590step0Labels permutation39 permutation2
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical21591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21591 raw21591Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw21591 raw21591Labels = mixedMoment B raw21591step0 raw21591step0Labels := by
      have hz : ∀ j, raw21591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21591step0 = (fun i j => raw21591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21591step0 raw21591; decide +kernel
      have hl : raw21591step0Labels = raw21591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21591 raw21591Labels permutation346 hz
    mixedMoment B raw21591step0 raw21591step0Labels = mixedMoment B raw21591step1 raw21591step1Labels := by
      have ha : raw21591step1 = (fun i j => raw21591step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21591step1 raw21591step0; decide +kernel
      have hl : raw21591step1Labels = raw21591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21591step0 raw21591step0Labels permutation38 permutation2
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical21592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21592 raw21592Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw21592 raw21592Labels = mixedMoment B raw21592step0 raw21592step0Labels := by
      have hz : ∀ j, raw21592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21592step0 = (fun i j => raw21592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21592step0 raw21592; decide +kernel
      have hl : raw21592step0Labels = raw21592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21592 raw21592Labels permutation346 hz
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical21593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21593 raw21593Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw21593 raw21593Labels = mixedMoment B raw21593step0 raw21593step0Labels := by
      have ha : raw21593step0 = (fun i j => raw21593 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21593step0 raw21593; decide +kernel
      have hl : raw21593step0Labels = raw21593Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21593 raw21593Labels permutation182 permutation2
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical21594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21594 raw21594Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21594 raw21594Labels = mixedMoment B raw21594step0 raw21594step0Labels := by
      have hz : ∀ j, raw21594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21594step0 = (fun i j => raw21594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21594step0 raw21594; decide +kernel
      have hl : raw21594step0Labels = raw21594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21594 raw21594Labels permutation346 hz
    mixedMoment B raw21594step0 raw21594step0Labels = mixedMoment B raw21594step1 raw21594step1Labels := by
      have ha : raw21594step1 = (fun i j => raw21594step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21594step1 raw21594step0; decide +kernel
      have hl : raw21594step1Labels = raw21594step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21594step0 raw21594step0Labels permutation38 permutation2
    _ = mixedMoment B node1914 node1914Labels := by rfl

theorem canonical21595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21595 raw21595Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21595 raw21595Labels = mixedMoment B raw21595step0 raw21595step0Labels := by
      have hz : ∀ j, raw21595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21595step0 = (fun i j => raw21595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21595step0 raw21595; decide +kernel
      have hl : raw21595step0Labels = raw21595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21595 raw21595Labels permutation346 hz
    mixedMoment B raw21595step0 raw21595step0Labels = mixedMoment B raw21595step1 raw21595step1Labels := by
      have ha : raw21595step1 = (fun i j => raw21595step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21595step1 raw21595step0; decide +kernel
      have hl : raw21595step1Labels = raw21595step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21595step0 raw21595step0Labels permutation38 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical21596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21596 raw21596Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw21596 raw21596Labels = mixedMoment B raw21596step0 raw21596step0Labels := by
      have hz : ∀ j, raw21596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21596step0 = (fun i j => raw21596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21596step0 raw21596; decide +kernel
      have hl : raw21596step0Labels = raw21596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21596 raw21596Labels permutation346 hz
    mixedMoment B raw21596step0 raw21596step0Labels = mixedMoment B raw21596step1 raw21596step1Labels := by
      have ha : raw21596step1 = (fun i j => raw21596step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21596step1 raw21596step0; decide +kernel
      have hl : raw21596step1Labels = raw21596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21596step0 raw21596step0Labels permutation38 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical21597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21597 raw21597Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21597 raw21597Labels = mixedMoment B raw21597step0 raw21597step0Labels := by
      have hz : ∀ j, raw21597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21597step0 = (fun i j => raw21597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21597step0 raw21597; decide +kernel
      have hl : raw21597step0Labels = raw21597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21597 raw21597Labels permutation346 hz
    mixedMoment B raw21597step0 raw21597step0Labels = mixedMoment B raw21597step1 raw21597step1Labels := by
      have ha : raw21597step1 = (fun i j => raw21597step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21597step1 raw21597step0; decide +kernel
      have hl : raw21597step1Labels = raw21597step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21597step0 raw21597step0Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21602 raw21602Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw21602 raw21602Labels = mixedMoment B raw21602step0 raw21602step0Labels := by
      have hz : ∀ j, raw21602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21602step0 = (fun i j => raw21602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21602step0 raw21602; decide +kernel
      have hl : raw21602step0Labels = raw21602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21602 raw21602Labels permutation346 hz
    mixedMoment B raw21602step0 raw21602step0Labels = mixedMoment B raw21602step1 raw21602step1Labels := by
      have ha : raw21602step1 = (fun i j => raw21602step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21602step1 raw21602step0; decide +kernel
      have hl : raw21602step1Labels = raw21602step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21602step0 raw21602step0Labels permutation38 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

theorem canonical21606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21606 raw21606Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21606 raw21606Labels = mixedMoment B raw21606step0 raw21606step0Labels := by
      have ha : raw21606step0 = (fun i j => raw21606 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21606step0 raw21606; decide +kernel
      have hl : raw21606step0Labels = raw21606Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21606 raw21606Labels permutation200 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical21607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21607 raw21607Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21607 raw21607Labels = mixedMoment B raw21607step0 raw21607step0Labels := by
      have hz : ∀ j, raw21607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21607step0 = (fun i j => raw21607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21607step0 raw21607; decide +kernel
      have hl : raw21607step0Labels = raw21607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21607 raw21607Labels permutation346 hz
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical21608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21608 raw21608Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw21608 raw21608Labels = mixedMoment B raw21608step0 raw21608step0Labels := by
      have hz : ∀ j, raw21608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21608step0 = (fun i j => raw21608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21608step0 raw21608; decide +kernel
      have hl : raw21608step0Labels = raw21608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21608 raw21608Labels permutation346 hz
    mixedMoment B raw21608step0 raw21608step0Labels = mixedMoment B raw21608step1 raw21608step1Labels := by
      have ha : raw21608step1 = (fun i j => raw21608step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21608step1 raw21608step0; decide +kernel
      have hl : raw21608step1Labels = raw21608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21608step0 raw21608step0Labels permutation38 permutation2
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical21612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21612 raw21612Labels = mixedMoment B node714 node714Labels := by
  calc
    mixedMoment B raw21612 raw21612Labels = mixedMoment B raw21612step0 raw21612step0Labels := by
      have hz : ∀ j, raw21612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21612step0 = (fun i j => raw21612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21612step0 raw21612; decide +kernel
      have hl : raw21612step0Labels = raw21612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21612 raw21612Labels permutation346 hz
    mixedMoment B raw21612step0 raw21612step0Labels = mixedMoment B raw21612step1 raw21612step1Labels := by
      have ha : raw21612step1 = (fun i j => raw21612step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21612step1 raw21612step0; decide +kernel
      have hl : raw21612step1Labels = raw21612step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21612step0 raw21612step0Labels permutation38 permutation4
    mixedMoment B raw21612step1 raw21612step1Labels = mixedMoment B raw21612step2 raw21612step2Labels := by
      have ha : raw21612step2 = -raw21612step1 := by apply Matrix.ext; change ∀ i j, raw21612step2 i j = -(raw21612step1 i j); unfold raw21612step2 raw21612step1; decide +kernel
      have hl : raw21612step2Labels = raw21612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node714 node714Labels := by rfl

theorem canonical21613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21613 raw21613Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw21613 raw21613Labels = mixedMoment B raw21613step0 raw21613step0Labels := by
      have hz : ∀ j, raw21613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21613step0 = (fun i j => raw21613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21613step0 raw21613; decide +kernel
      have hl : raw21613step0Labels = raw21613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21613 raw21613Labels permutation346 hz
    mixedMoment B raw21613step0 raw21613step0Labels = mixedMoment B raw21613step1 raw21613step1Labels := by
      have ha : raw21613step1 = (fun i j => raw21613step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21613step1 raw21613step0; decide +kernel
      have hl : raw21613step1Labels = raw21613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21613step0 raw21613step0Labels permutation38 permutation2
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical21614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21614 raw21614Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21614 raw21614Labels = mixedMoment B raw21614step0 raw21614step0Labels := by
      have hz : ∀ j, raw21614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21614step0 = (fun i j => raw21614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21614step0 raw21614; decide +kernel
      have hl : raw21614step0Labels = raw21614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21614 raw21614Labels permutation346 hz
    mixedMoment B raw21614step0 raw21614step0Labels = mixedMoment B raw21614step1 raw21614step1Labels := by
      have ha : raw21614step1 = (fun i j => raw21614step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21614step1 raw21614step0; decide +kernel
      have hl : raw21614step1Labels = raw21614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21614step0 raw21614step0Labels permutation151 permutation2
    mixedMoment B raw21614step1 raw21614step1Labels = mixedMoment B raw21614step2 raw21614step2Labels := by
      have ha : raw21614step2 = -raw21614step1 := by apply Matrix.ext; change ∀ i j, raw21614step2 i j = -(raw21614step1 i j); unfold raw21614step2 raw21614step1; decide +kernel
      have hl : raw21614step2Labels = raw21614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical21615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21615 raw21615Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw21615 raw21615Labels = mixedMoment B raw21615step0 raw21615step0Labels := by
      have ha : raw21615step0 = (fun i j => raw21615 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21615step0 raw21615; decide +kernel
      have hl : raw21615step0Labels = raw21615Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21615 raw21615Labels permutation182 permutation2
    _ = mixedMoment B node1986 node1986Labels := by rfl

theorem canonical21616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21616 raw21616Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21616 raw21616Labels = mixedMoment B raw21616step0 raw21616step0Labels := by
      have hz : ∀ j, raw21616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21616step0 = (fun i j => raw21616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21616step0 raw21616; decide +kernel
      have hl : raw21616step0Labels = raw21616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21616 raw21616Labels permutation346 hz
    mixedMoment B raw21616step0 raw21616step0Labels = mixedMoment B raw21616step1 raw21616step1Labels := by
      have ha : raw21616step1 = (fun i j => raw21616step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21616step1 raw21616step0; decide +kernel
      have hl : raw21616step1Labels = raw21616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21616step0 raw21616step0Labels permutation38 permutation2
    _ = mixedMoment B node1911 node1911Labels := by rfl

theorem canonical21617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21617 raw21617Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21617 raw21617Labels = mixedMoment B raw21617step0 raw21617step0Labels := by
      have hz : ∀ j, raw21617 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21617step0 = (fun i j => raw21617 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21617step0 raw21617; decide +kernel
      have hl : raw21617step0Labels = raw21617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21617 raw21617Labels permutation520 hz
    mixedMoment B raw21617step0 raw21617step0Labels = mixedMoment B raw21617step1 raw21617step1Labels := by
      have hz : ∀ j, raw21617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21617step1 = (fun i j => raw21617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21617step1 raw21617step0; decide +kernel
      have hl : raw21617step1Labels = raw21617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21617step0 raw21617step0Labels permutation80 hz
    mixedMoment B raw21617step1 raw21617step1Labels = mixedMoment B raw21617step2 raw21617step2Labels := by
      have ha : raw21617step2 = (fun i j => raw21617step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21617step2 raw21617step1; decide +kernel
      have hl : raw21617step2Labels = raw21617step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21617step1 raw21617step1Labels permutation10 permutation2
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21618 raw21618Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21618 raw21618Labels = mixedMoment B raw21618step0 raw21618step0Labels := by
      have hz : ∀ j, raw21618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21618step0 = (fun i j => raw21618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21618step0 raw21618; decide +kernel
      have hl : raw21618step0Labels = raw21618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21618 raw21618Labels permutation346 hz
    mixedMoment B raw21618step0 raw21618step0Labels = mixedMoment B raw21618step1 raw21618step1Labels := by
      have ha : raw21618step1 = (fun i j => raw21618step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21618step1 raw21618step0; decide +kernel
      have hl : raw21618step1Labels = raw21618step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21618step0 raw21618step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical21619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21619 raw21619Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21619 raw21619Labels = mixedMoment B raw21619step0 raw21619step0Labels := by
      have hz : ∀ j, raw21619 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21619step0 = (fun i j => raw21619 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21619step0 raw21619; decide +kernel
      have hl : raw21619step0Labels = raw21619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21619 raw21619Labels permutation520 hz
    mixedMoment B raw21619step0 raw21619step0Labels = mixedMoment B raw21619step1 raw21619step1Labels := by
      have hz : ∀ j, raw21619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21619step1 = (fun i j => raw21619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21619step1 raw21619step0; decide +kernel
      have hl : raw21619step1Labels = raw21619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21619step0 raw21619step0Labels permutation80 hz
    mixedMoment B raw21619step1 raw21619step1Labels = mixedMoment B raw21619step2 raw21619step2Labels := by
      have ha : raw21619step2 = (fun i j => raw21619step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21619step2 raw21619step1; decide +kernel
      have hl : raw21619step2Labels = raw21619step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21619step1 raw21619step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical21622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21622 raw21622Labels = mixedMoment B node880 node880Labels := by
  calc
    mixedMoment B raw21622 raw21622Labels = mixedMoment B raw21622step0 raw21622step0Labels := by
      have hz : ∀ j, raw21622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21622step0 = (fun i j => raw21622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21622step0 raw21622; decide +kernel
      have hl : raw21622step0Labels = raw21622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21622 raw21622Labels permutation346 hz
    mixedMoment B raw21622step0 raw21622step0Labels = mixedMoment B raw21622step1 raw21622step1Labels := by
      have ha : raw21622step1 = (fun i j => raw21622step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21622step1 raw21622step0; decide +kernel
      have hl : raw21622step1Labels = raw21622step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21622step0 raw21622step0Labels permutation40 permutation2
    _ = mixedMoment B node880 node880Labels := by rfl

theorem canonical21624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21624 raw21624Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw21624 raw21624Labels = mixedMoment B raw21624step0 raw21624step0Labels := by
      have hz : ∀ j, raw21624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21624step0 = (fun i j => raw21624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21624step0 raw21624; decide +kernel
      have hl : raw21624step0Labels = raw21624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21624 raw21624Labels permutation346 hz
    mixedMoment B raw21624step0 raw21624step0Labels = mixedMoment B raw21624step1 raw21624step1Labels := by
      have ha : raw21624step1 = (fun i j => raw21624step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21624step1 raw21624step0; decide +kernel
      have hl : raw21624step1Labels = raw21624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21624step0 raw21624step0Labels permutation40 permutation2
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical21625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21625 raw21625Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw21625 raw21625Labels = mixedMoment B raw21625step0 raw21625step0Labels := by
      have ha : raw21625step0 = (fun i j => raw21625 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21625step0 raw21625; decide +kernel
      have hl : raw21625step0Labels = raw21625Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21625 raw21625Labels permutation200 permutation2
    _ = mixedMoment B node864 node864Labels := by rfl

theorem canonical21626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21626 raw21626Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw21626 raw21626Labels = mixedMoment B raw21626step0 raw21626step0Labels := by
      have hz : ∀ j, raw21626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21626step0 = (fun i j => raw21626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21626step0 raw21626; decide +kernel
      have hl : raw21626step0Labels = raw21626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21626 raw21626Labels permutation346 hz
    mixedMoment B raw21626step0 raw21626step0Labels = mixedMoment B raw21626step1 raw21626step1Labels := by
      have ha : raw21626step1 = (fun i j => raw21626step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21626step1 raw21626step0; decide +kernel
      have hl : raw21626step1Labels = raw21626step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21626step0 raw21626step0Labels permutation38 permutation2
    _ = mixedMoment B node872 node872Labels := by rfl

theorem canonical21627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21627 raw21627Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21627 raw21627Labels = mixedMoment B raw21627step0 raw21627step0Labels := by
      have hz : ∀ j, raw21627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21627step0 = (fun i j => raw21627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21627step0 raw21627; decide +kernel
      have hl : raw21627step0Labels = raw21627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21627 raw21627Labels permutation346 hz
    mixedMoment B raw21627step0 raw21627step0Labels = mixedMoment B raw21627step1 raw21627step1Labels := by
      have ha : raw21627step1 = (fun i j => raw21627step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21627step1 raw21627step0; decide +kernel
      have hl : raw21627step1Labels = raw21627step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21627step0 raw21627step0Labels permutation38 permutation2
    _ = mixedMoment B node867 node867Labels := by rfl

theorem canonical21628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21628 raw21628Labels = mixedMoment B node976 node976Labels := by
  calc
    mixedMoment B raw21628 raw21628Labels = mixedMoment B raw21628step0 raw21628step0Labels := by
      have ha : raw21628step0 = (fun i j => raw21628 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21628step0 raw21628; decide +kernel
      have hl : raw21628step0Labels = raw21628Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21628 raw21628Labels permutation200 permutation2
    _ = mixedMoment B node976 node976Labels := by rfl

theorem canonical21629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21629 raw21629Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21629 raw21629Labels = mixedMoment B raw21629step0 raw21629step0Labels := by
      have hz : ∀ j, raw21629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21629step0 = (fun i j => raw21629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21629step0 raw21629; decide +kernel
      have hl : raw21629step0Labels = raw21629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21629 raw21629Labels permutation346 hz
    _ = mixedMoment B node1033 node1033Labels := by rfl

theorem canonical21630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21630 raw21630Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw21630 raw21630Labels = mixedMoment B raw21630step0 raw21630step0Labels := by
      have hz : ∀ j, raw21630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21630step0 = (fun i j => raw21630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21630step0 raw21630; decide +kernel
      have hl : raw21630step0Labels = raw21630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21630 raw21630Labels permutation346 hz
    mixedMoment B raw21630step0 raw21630step0Labels = mixedMoment B raw21630step1 raw21630step1Labels := by
      have ha : raw21630step1 = (fun i j => raw21630step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21630step1 raw21630step0; decide +kernel
      have hl : raw21630step1Labels = raw21630step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21630step0 raw21630step0Labels permutation38 permutation2
    _ = mixedMoment B node984 node984Labels := by rfl

theorem canonical21631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21631 raw21631Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw21631 raw21631Labels = mixedMoment B raw21631step0 raw21631step0Labels := by
      have hz : ∀ j, raw21631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21631step0 = (fun i j => raw21631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21631step0 raw21631; decide +kernel
      have hl : raw21631step0Labels = raw21631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21631 raw21631Labels permutation346 hz
    mixedMoment B raw21631step0 raw21631step0Labels = mixedMoment B raw21631step1 raw21631step1Labels := by
      have ha : raw21631step1 = (fun i j => raw21631step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21631step1 raw21631step0; decide +kernel
      have hl : raw21631step1Labels = raw21631step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21631step0 raw21631step0Labels permutation40 permutation4
    mixedMoment B raw21631step1 raw21631step1Labels = mixedMoment B raw21631step2 raw21631step2Labels := by
      have ha : raw21631step2 = -raw21631step1 := by apply Matrix.ext; change ∀ i j, raw21631step2 i j = -(raw21631step1 i j); unfold raw21631step2 raw21631step1; decide +kernel
      have hl : raw21631step2Labels = raw21631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node706 node706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21632 raw21632Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw21632 raw21632Labels = mixedMoment B raw21632step0 raw21632step0Labels := by
      have ha : raw21632step0 = (fun i j => raw21632 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21632step0 raw21632; decide +kernel
      have hl : raw21632step0Labels = raw21632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21632 raw21632Labels permutation212 permutation4
    mixedMoment B raw21632step0 raw21632step0Labels = mixedMoment B raw21632step1 raw21632step1Labels := by
      have ha : raw21632step1 = -raw21632step0 := by apply Matrix.ext; change ∀ i j, raw21632step1 i j = -(raw21632step0 i j); unfold raw21632step1 raw21632step0; decide +kernel
      have hl : raw21632step1Labels = raw21632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node698 node698Labels := by rfl

theorem canonical21633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21633 raw21633Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw21633 raw21633Labels = mixedMoment B raw21633step0 raw21633step0Labels := by
      have hz : ∀ j, raw21633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21633step0 = (fun i j => raw21633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21633step0 raw21633; decide +kernel
      have hl : raw21633step0Labels = raw21633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21633 raw21633Labels permutation346 hz
    mixedMoment B raw21633step0 raw21633step0Labels = mixedMoment B raw21633step1 raw21633step1Labels := by
      have ha : raw21633step1 = (fun i j => raw21633step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21633step1 raw21633step0; decide +kernel
      have hl : raw21633step1Labels = raw21633step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21633step0 raw21633step0Labels permutation40 permutation4
    mixedMoment B raw21633step1 raw21633step1Labels = mixedMoment B raw21633step2 raw21633step2Labels := by
      have ha : raw21633step2 = -raw21633step1 := by apply Matrix.ext; change ∀ i j, raw21633step2 i j = -(raw21633step1 i j); unfold raw21633step2 raw21633step1; decide +kernel
      have hl : raw21633step2Labels = raw21633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

theorem canonical21656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21656 raw21656Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21656 raw21656Labels = mixedMoment B raw21656step0 raw21656step0Labels := by
      have hz : ∀ j, raw21656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21656step0 = (fun i j => raw21656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21656step0 raw21656; decide +kernel
      have hl : raw21656step0Labels = raw21656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656 raw21656Labels permutation434 hz
    mixedMoment B raw21656step0 raw21656step0Labels = mixedMoment B raw21656step1 raw21656step1Labels := by
      have hz : ∀ j, raw21656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21656step1 = (fun i j => raw21656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21656step1 raw21656step0; decide +kernel
      have hl : raw21656step1Labels = raw21656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656step0 raw21656step0Labels permutation80 hz
    mixedMoment B raw21656step1 raw21656step1Labels = mixedMoment B raw21656step2 raw21656step2Labels := by
      have ha : raw21656step2 = (fun i j => raw21656step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21656step2 raw21656step1; decide +kernel
      have hl : raw21656step2Labels = raw21656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21656step1 raw21656step1Labels permutation9 permutation7
    mixedMoment B raw21656step2 raw21656step2Labels = mixedMoment B raw21656step3 raw21656step3Labels := by
      have ha : raw21656step3 = -raw21656step2 := by apply Matrix.ext; change ∀ i j, raw21656step3 i j = -(raw21656step2 i j); unfold raw21656step3 raw21656step2; decide +kernel
      have hl : raw21656step3Labels = raw21656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21656step3 raw21656step3Labels = mixedMoment B raw21656step4 raw21656step4Labels := by
      have ha : raw21656step4 = raw21656step3 := by apply Matrix.ext; unfold raw21656step4 raw21656step3; decide +kernel
      have hl : raw21656step3Labels = labelEmbedding1 ∘ raw21656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21656step3 raw21656step3Labels raw21656step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21657 raw21657Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21657 raw21657Labels = mixedMoment B raw21657step0 raw21657step0Labels := by
      have hz : ∀ j, raw21657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21657step0 = (fun i j => raw21657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21657step0 raw21657; decide +kernel
      have hl : raw21657step0Labels = raw21657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21657 raw21657Labels permutation434 hz
    mixedMoment B raw21657step0 raw21657step0Labels = mixedMoment B raw21657step1 raw21657step1Labels := by
      have hz : ∀ j, raw21657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21657step1 = (fun i j => raw21657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21657step1 raw21657step0; decide +kernel
      have hl : raw21657step1Labels = raw21657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21657step0 raw21657step0Labels permutation56 hz
    mixedMoment B raw21657step1 raw21657step1Labels = mixedMoment B raw21657step2 raw21657step2Labels := by
      have ha : raw21657step2 = (fun i j => raw21657step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21657step2 raw21657step1; decide +kernel
      have hl : raw21657step2Labels = raw21657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21657step1 raw21657step1Labels permutation9 permutation7
    mixedMoment B raw21657step2 raw21657step2Labels = mixedMoment B raw21657step3 raw21657step3Labels := by
      have ha : raw21657step3 = -raw21657step2 := by apply Matrix.ext; change ∀ i j, raw21657step3 i j = -(raw21657step2 i j); unfold raw21657step3 raw21657step2; decide +kernel
      have hl : raw21657step3Labels = raw21657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21657step3 raw21657step3Labels = mixedMoment B raw21657step4 raw21657step4Labels := by
      have ha : raw21657step4 = raw21657step3 := by apply Matrix.ext; unfold raw21657step4 raw21657step3; decide +kernel
      have hl : raw21657step3Labels = labelEmbedding1 ∘ raw21657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21657step3 raw21657step3Labels raw21657step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21658 raw21658Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21658 raw21658Labels = mixedMoment B raw21658step0 raw21658step0Labels := by
      have hz : ∀ j, raw21658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21658step0 = (fun i j => raw21658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21658step0 raw21658; decide +kernel
      have hl : raw21658step0Labels = raw21658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21658 raw21658Labels permutation346 hz
    mixedMoment B raw21658step0 raw21658step0Labels = mixedMoment B raw21658step1 raw21658step1Labels := by
      have hz : ∀ j, raw21658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21658step1 = (fun i j => raw21658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21658step1 raw21658step0; decide +kernel
      have hl : raw21658step1Labels = raw21658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21658step0 raw21658step0Labels permutation56 hz
    mixedMoment B raw21658step1 raw21658step1Labels = mixedMoment B raw21658step2 raw21658step2Labels := by
      have ha : raw21658step2 = (fun i j => raw21658step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21658step2 raw21658step1; decide +kernel
      have hl : raw21658step2Labels = raw21658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21658step1 raw21658step1Labels permutation9 permutation7
    mixedMoment B raw21658step2 raw21658step2Labels = mixedMoment B raw21658step3 raw21658step3Labels := by
      have ha : raw21658step3 = -raw21658step2 := by apply Matrix.ext; change ∀ i j, raw21658step3 i j = -(raw21658step2 i j); unfold raw21658step3 raw21658step2; decide +kernel
      have hl : raw21658step3Labels = raw21658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21658step3 raw21658step3Labels = mixedMoment B raw21658step4 raw21658step4Labels := by
      have ha : raw21658step4 = raw21658step3 := by apply Matrix.ext; unfold raw21658step4 raw21658step3; decide +kernel
      have hl : raw21658step3Labels = labelEmbedding1 ∘ raw21658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21658step3 raw21658step3Labels raw21658step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21659 raw21659Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw21659 raw21659Labels = mixedMoment B raw21659step0 raw21659step0Labels := by
      have hz : ∀ j, raw21659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21659step0 = (fun i j => raw21659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21659step0 raw21659; decide +kernel
      have hl : raw21659step0Labels = raw21659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659 raw21659Labels permutation434 hz
    mixedMoment B raw21659step0 raw21659step0Labels = mixedMoment B raw21659step1 raw21659step1Labels := by
      have hz : ∀ j, raw21659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21659step1 = (fun i j => raw21659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21659step1 raw21659step0; decide +kernel
      have hl : raw21659step1Labels = raw21659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659step0 raw21659step0Labels permutation80 hz
    mixedMoment B raw21659step1 raw21659step1Labels = mixedMoment B raw21659step2 raw21659step2Labels := by
      have hz : ∀ j, raw21659step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21659step2 = (fun i j => raw21659step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21659step2 raw21659step1; decide +kernel
      have hl : raw21659step2Labels = raw21659step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659step1 raw21659step1Labels permutation14 hz
    mixedMoment B raw21659step2 raw21659step2Labels = mixedMoment B raw21659step3 raw21659step3Labels := by
      have ha : raw21659step3 = (fun i j => raw21659step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21659step3 raw21659step2; decide +kernel
      have hl : raw21659step3Labels = raw21659step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21659step2 raw21659step2Labels permutation3 permutation7
    mixedMoment B raw21659step3 raw21659step3Labels = mixedMoment B raw21659step4 raw21659step4Labels := by
      have ha : raw21659step4 = -raw21659step3 := by apply Matrix.ext; change ∀ i j, raw21659step4 i j = -(raw21659step3 i j); unfold raw21659step4 raw21659step3; decide +kernel
      have hl : raw21659step4Labels = raw21659step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21659step4 raw21659step4Labels = mixedMoment B raw21659step5 raw21659step5Labels := by
      have ha : raw21659step5 = raw21659step4 := by apply Matrix.ext; unfold raw21659step5 raw21659step4; decide +kernel
      have hl : raw21659step4Labels = labelEmbedding1 ∘ raw21659step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21659step4 raw21659step4Labels raw21659step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical21660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21660 raw21660Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw21660 raw21660Labels = mixedMoment B raw21660step0 raw21660step0Labels := by
      have hz : ∀ j, raw21660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21660step0 = (fun i j => raw21660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21660step0 raw21660; decide +kernel
      have hl : raw21660step0Labels = raw21660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660 raw21660Labels permutation434 hz
    mixedMoment B raw21660step0 raw21660step0Labels = mixedMoment B raw21660step1 raw21660step1Labels := by
      have hz : ∀ j, raw21660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21660step1 = (fun i j => raw21660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21660step1 raw21660step0; decide +kernel
      have hl : raw21660step1Labels = raw21660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step0 raw21660step0Labels permutation80 hz
    mixedMoment B raw21660step1 raw21660step1Labels = mixedMoment B raw21660step2 raw21660step2Labels := by
      have hz : ∀ j, raw21660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21660step2 = (fun i j => raw21660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21660step2 raw21660step1; decide +kernel
      have hl : raw21660step2Labels = raw21660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step1 raw21660step1Labels permutation14 hz
    mixedMoment B raw21660step2 raw21660step2Labels = mixedMoment B raw21660step3 raw21660step3Labels := by
      have ha : raw21660step3 = (fun i j => raw21660step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21660step3 raw21660step2; decide +kernel
      have hl : raw21660step3Labels = raw21660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21660step2 raw21660step2Labels permutation3 permutation7
    mixedMoment B raw21660step3 raw21660step3Labels = mixedMoment B raw21660step4 raw21660step4Labels := by
      have ha : raw21660step4 = -raw21660step3 := by apply Matrix.ext; change ∀ i j, raw21660step4 i j = -(raw21660step3 i j); unfold raw21660step4 raw21660step3; decide +kernel
      have hl : raw21660step4Labels = raw21660step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21660step4 raw21660step4Labels = mixedMoment B raw21660step5 raw21660step5Labels := by
      have ha : raw21660step5 = raw21660step4 := by apply Matrix.ext; unfold raw21660step5 raw21660step4; decide +kernel
      have hl : raw21660step4Labels = labelEmbedding1 ∘ raw21660step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21660step4 raw21660step4Labels raw21660step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical21661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21661 raw21661Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21661 raw21661Labels = mixedMoment B raw21661step0 raw21661step0Labels := by
      have hz : ∀ j, raw21661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21661step0 = (fun i j => raw21661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21661step0 raw21661; decide +kernel
      have hl : raw21661step0Labels = raw21661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21661 raw21661Labels permutation434 hz
    mixedMoment B raw21661step0 raw21661step0Labels = mixedMoment B raw21661step1 raw21661step1Labels := by
      have hz : ∀ j, raw21661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21661step1 = (fun i j => raw21661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21661step1 raw21661step0; decide +kernel
      have hl : raw21661step1Labels = raw21661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21661step0 raw21661step0Labels permutation80 hz
    mixedMoment B raw21661step1 raw21661step1Labels = mixedMoment B raw21661step2 raw21661step2Labels := by
      have ha : raw21661step2 = (fun i j => raw21661step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21661step2 raw21661step1; decide +kernel
      have hl : raw21661step2Labels = raw21661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21661step1 raw21661step1Labels permutation9 permutation7
    mixedMoment B raw21661step2 raw21661step2Labels = mixedMoment B raw21661step3 raw21661step3Labels := by
      have ha : raw21661step3 = -raw21661step2 := by apply Matrix.ext; change ∀ i j, raw21661step3 i j = -(raw21661step2 i j); unfold raw21661step3 raw21661step2; decide +kernel
      have hl : raw21661step3Labels = raw21661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21661step3 raw21661step3Labels = mixedMoment B raw21661step4 raw21661step4Labels := by
      have ha : raw21661step4 = raw21661step3 := by apply Matrix.ext; unfold raw21661step4 raw21661step3; decide +kernel
      have hl : raw21661step3Labels = labelEmbedding1 ∘ raw21661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21661step3 raw21661step3Labels raw21661step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical21662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21662 raw21662Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21662 raw21662Labels = mixedMoment B raw21662step0 raw21662step0Labels := by
      have hz : ∀ j, raw21662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21662step0 = (fun i j => raw21662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21662step0 raw21662; decide +kernel
      have hl : raw21662step0Labels = raw21662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21662 raw21662Labels permutation434 hz
    mixedMoment B raw21662step0 raw21662step0Labels = mixedMoment B raw21662step1 raw21662step1Labels := by
      have ha : raw21662step1 = (fun i j => raw21662step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21662step1 raw21662step0; decide +kernel
      have hl : raw21662step1Labels = raw21662step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21662step0 raw21662step0Labels permutation39 permutation7
    mixedMoment B raw21662step1 raw21662step1Labels = mixedMoment B raw21662step2 raw21662step2Labels := by
      have ha : raw21662step2 = -raw21662step1 := by apply Matrix.ext; change ∀ i j, raw21662step2 i j = -(raw21662step1 i j); unfold raw21662step2 raw21662step1; decide +kernel
      have hl : raw21662step2Labels = raw21662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21662step2 raw21662step2Labels = mixedMoment B raw21662step3 raw21662step3Labels := by
      have ha : raw21662step3 = raw21662step2 := by apply Matrix.ext; unfold raw21662step3 raw21662step2; decide +kernel
      have hl : raw21662step2Labels = labelEmbedding1 ∘ raw21662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21662step2 raw21662step2Labels raw21662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21663 raw21663Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21663 raw21663Labels = mixedMoment B raw21663step0 raw21663step0Labels := by
      have hz : ∀ j, raw21663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21663step0 = (fun i j => raw21663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21663step0 raw21663; decide +kernel
      have hl : raw21663step0Labels = raw21663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21663 raw21663Labels permutation346 hz
    mixedMoment B raw21663step0 raw21663step0Labels = mixedMoment B raw21663step1 raw21663step1Labels := by
      have ha : raw21663step1 = (fun i j => raw21663step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21663step1 raw21663step0; decide +kernel
      have hl : raw21663step1Labels = raw21663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21663step0 raw21663step0Labels permutation39 permutation7
    mixedMoment B raw21663step1 raw21663step1Labels = mixedMoment B raw21663step2 raw21663step2Labels := by
      have ha : raw21663step2 = -raw21663step1 := by apply Matrix.ext; change ∀ i j, raw21663step2 i j = -(raw21663step1 i j); unfold raw21663step2 raw21663step1; decide +kernel
      have hl : raw21663step2Labels = raw21663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21663step2 raw21663step2Labels = mixedMoment B raw21663step3 raw21663step3Labels := by
      have ha : raw21663step3 = raw21663step2 := by apply Matrix.ext; unfold raw21663step3 raw21663step2; decide +kernel
      have hl : raw21663step2Labels = labelEmbedding1 ∘ raw21663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21663step2 raw21663step2Labels raw21663step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21664 raw21664Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21664 raw21664Labels = mixedMoment B raw21664step0 raw21664step0Labels := by
      have hz : ∀ j, raw21664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21664step0 = (fun i j => raw21664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21664step0 raw21664; decide +kernel
      have hl : raw21664step0Labels = raw21664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21664 raw21664Labels permutation434 hz
    mixedMoment B raw21664step0 raw21664step0Labels = mixedMoment B raw21664step1 raw21664step1Labels := by
      have hz : ∀ j, raw21664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21664step1 = (fun i j => raw21664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21664step1 raw21664step0; decide +kernel
      have hl : raw21664step1Labels = raw21664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21664step0 raw21664step0Labels permutation80 hz
    mixedMoment B raw21664step1 raw21664step1Labels = mixedMoment B raw21664step2 raw21664step2Labels := by
      have ha : raw21664step2 = (fun i j => raw21664step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21664step2 raw21664step1; decide +kernel
      have hl : raw21664step2Labels = raw21664step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21664step1 raw21664step1Labels permutation9 permutation7
    mixedMoment B raw21664step2 raw21664step2Labels = mixedMoment B raw21664step3 raw21664step3Labels := by
      have ha : raw21664step3 = -raw21664step2 := by apply Matrix.ext; change ∀ i j, raw21664step3 i j = -(raw21664step2 i j); unfold raw21664step3 raw21664step2; decide +kernel
      have hl : raw21664step3Labels = raw21664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21664step3 raw21664step3Labels = mixedMoment B raw21664step4 raw21664step4Labels := by
      have ha : raw21664step4 = raw21664step3 := by apply Matrix.ext; unfold raw21664step4 raw21664step3; decide +kernel
      have hl : raw21664step3Labels = labelEmbedding1 ∘ raw21664step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21664step3 raw21664step3Labels raw21664step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical21665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21665 raw21665Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21665 raw21665Labels = mixedMoment B raw21665step0 raw21665step0Labels := by
      have hz : ∀ j, raw21665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21665step0 = (fun i j => raw21665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21665step0 raw21665; decide +kernel
      have hl : raw21665step0Labels = raw21665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665 raw21665Labels permutation434 hz
    mixedMoment B raw21665step0 raw21665step0Labels = mixedMoment B raw21665step1 raw21665step1Labels := by
      have hz : ∀ j, raw21665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21665step1 = (fun i j => raw21665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21665step1 raw21665step0; decide +kernel
      have hl : raw21665step1Labels = raw21665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665step0 raw21665step0Labels permutation80 hz
    mixedMoment B raw21665step1 raw21665step1Labels = mixedMoment B raw21665step2 raw21665step2Labels := by
      have ha : raw21665step2 = (fun i j => raw21665step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21665step2 raw21665step1; decide +kernel
      have hl : raw21665step2Labels = raw21665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21665step1 raw21665step1Labels permutation9 permutation7
    mixedMoment B raw21665step2 raw21665step2Labels = mixedMoment B raw21665step3 raw21665step3Labels := by
      have ha : raw21665step3 = -raw21665step2 := by apply Matrix.ext; change ∀ i j, raw21665step3 i j = -(raw21665step2 i j); unfold raw21665step3 raw21665step2; decide +kernel
      have hl : raw21665step3Labels = raw21665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21665step3 raw21665step3Labels = mixedMoment B raw21665step4 raw21665step4Labels := by
      have ha : raw21665step4 = raw21665step3 := by apply Matrix.ext; unfold raw21665step4 raw21665step3; decide +kernel
      have hl : raw21665step3Labels = labelEmbedding1 ∘ raw21665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21665step3 raw21665step3Labels raw21665step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21666 raw21666Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21666 raw21666Labels = mixedMoment B raw21666step0 raw21666step0Labels := by
      have hz : ∀ j, raw21666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21666step0 = (fun i j => raw21666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21666step0 raw21666; decide +kernel
      have hl : raw21666step0Labels = raw21666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21666 raw21666Labels permutation434 hz
    mixedMoment B raw21666step0 raw21666step0Labels = mixedMoment B raw21666step1 raw21666step1Labels := by
      have hz : ∀ j, raw21666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21666step1 = (fun i j => raw21666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21666step1 raw21666step0; decide +kernel
      have hl : raw21666step1Labels = raw21666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21666step0 raw21666step0Labels permutation56 hz
    mixedMoment B raw21666step1 raw21666step1Labels = mixedMoment B raw21666step2 raw21666step2Labels := by
      have ha : raw21666step2 = (fun i j => raw21666step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21666step2 raw21666step1; decide +kernel
      have hl : raw21666step2Labels = raw21666step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21666step1 raw21666step1Labels permutation9 permutation7
    mixedMoment B raw21666step2 raw21666step2Labels = mixedMoment B raw21666step3 raw21666step3Labels := by
      have ha : raw21666step3 = -raw21666step2 := by apply Matrix.ext; change ∀ i j, raw21666step3 i j = -(raw21666step2 i j); unfold raw21666step3 raw21666step2; decide +kernel
      have hl : raw21666step3Labels = raw21666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21666step3 raw21666step3Labels = mixedMoment B raw21666step4 raw21666step4Labels := by
      have ha : raw21666step4 = raw21666step3 := by apply Matrix.ext; unfold raw21666step4 raw21666step3; decide +kernel
      have hl : raw21666step3Labels = labelEmbedding1 ∘ raw21666step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21666step3 raw21666step3Labels raw21666step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical21667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21667 raw21667Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21667 raw21667Labels = mixedMoment B raw21667step0 raw21667step0Labels := by
      have hz : ∀ j, raw21667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21667step0 = (fun i j => raw21667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21667step0 raw21667; decide +kernel
      have hl : raw21667step0Labels = raw21667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21667 raw21667Labels permutation434 hz
    mixedMoment B raw21667step0 raw21667step0Labels = mixedMoment B raw21667step1 raw21667step1Labels := by
      have ha : raw21667step1 = (fun i j => raw21667step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21667step1 raw21667step0; decide +kernel
      have hl : raw21667step1Labels = raw21667step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21667step0 raw21667step0Labels permutation33 permutation7
    mixedMoment B raw21667step1 raw21667step1Labels = mixedMoment B raw21667step2 raw21667step2Labels := by
      have ha : raw21667step2 = -raw21667step1 := by apply Matrix.ext; change ∀ i j, raw21667step2 i j = -(raw21667step1 i j); unfold raw21667step2 raw21667step1; decide +kernel
      have hl : raw21667step2Labels = raw21667step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21667step2 raw21667step2Labels = mixedMoment B raw21667step3 raw21667step3Labels := by
      have ha : raw21667step3 = raw21667step2 := by apply Matrix.ext; unfold raw21667step3 raw21667step2; decide +kernel
      have hl : raw21667step2Labels = labelEmbedding1 ∘ raw21667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21667step2 raw21667step2Labels raw21667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21668 raw21668Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21668 raw21668Labels = mixedMoment B raw21668step0 raw21668step0Labels := by
      have hz : ∀ j, raw21668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21668step0 = (fun i j => raw21668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21668step0 raw21668; decide +kernel
      have hl : raw21668step0Labels = raw21668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21668 raw21668Labels permutation265 hz
    mixedMoment B raw21668step0 raw21668step0Labels = mixedMoment B raw21668step1 raw21668step1Labels := by
      have ha : raw21668step1 = (fun i j => raw21668step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21668step1 raw21668step0; decide +kernel
      have hl : raw21668step1Labels = raw21668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21668step0 raw21668step0Labels permutation39 permutation7
    mixedMoment B raw21668step1 raw21668step1Labels = mixedMoment B raw21668step2 raw21668step2Labels := by
      have ha : raw21668step2 = -raw21668step1 := by apply Matrix.ext; change ∀ i j, raw21668step2 i j = -(raw21668step1 i j); unfold raw21668step2 raw21668step1; decide +kernel
      have hl : raw21668step2Labels = raw21668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21668step2 raw21668step2Labels = mixedMoment B raw21668step3 raw21668step3Labels := by
      have ha : raw21668step3 = raw21668step2 := by apply Matrix.ext; unfold raw21668step3 raw21668step2; decide +kernel
      have hl : raw21668step2Labels = labelEmbedding1 ∘ raw21668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21668step2 raw21668step2Labels raw21668step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21669 raw21669Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21669 raw21669Labels = mixedMoment B raw21669step0 raw21669step0Labels := by
      have hz : ∀ j, raw21669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21669step0 = (fun i j => raw21669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21669step0 raw21669; decide +kernel
      have hl : raw21669step0Labels = raw21669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21669 raw21669Labels permutation434 hz
    mixedMoment B raw21669step0 raw21669step0Labels = mixedMoment B raw21669step1 raw21669step1Labels := by
      have hz : ∀ j, raw21669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21669step1 = (fun i j => raw21669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21669step1 raw21669step0; decide +kernel
      have hl : raw21669step1Labels = raw21669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21669step0 raw21669step0Labels permutation56 hz
    mixedMoment B raw21669step1 raw21669step1Labels = mixedMoment B raw21669step2 raw21669step2Labels := by
      have ha : raw21669step2 = (fun i j => raw21669step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21669step2 raw21669step1; decide +kernel
      have hl : raw21669step2Labels = raw21669step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21669step1 raw21669step1Labels permutation9 permutation7
    mixedMoment B raw21669step2 raw21669step2Labels = mixedMoment B raw21669step3 raw21669step3Labels := by
      have ha : raw21669step3 = -raw21669step2 := by apply Matrix.ext; change ∀ i j, raw21669step3 i j = -(raw21669step2 i j); unfold raw21669step3 raw21669step2; decide +kernel
      have hl : raw21669step3Labels = raw21669step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21669step3 raw21669step3Labels = mixedMoment B raw21669step4 raw21669step4Labels := by
      have ha : raw21669step4 = raw21669step3 := by apply Matrix.ext; unfold raw21669step4 raw21669step3; decide +kernel
      have hl : raw21669step3Labels = labelEmbedding1 ∘ raw21669step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21669step3 raw21669step3Labels raw21669step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical21670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21670 raw21670Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21670 raw21670Labels = mixedMoment B raw21670step0 raw21670step0Labels := by
      have hz : ∀ j, raw21670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21670step0 = (fun i j => raw21670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21670step0 raw21670; decide +kernel
      have hl : raw21670step0Labels = raw21670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670 raw21670Labels permutation434 hz
    mixedMoment B raw21670step0 raw21670step0Labels = mixedMoment B raw21670step1 raw21670step1Labels := by
      have hz : ∀ j, raw21670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21670step1 = (fun i j => raw21670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21670step1 raw21670step0; decide +kernel
      have hl : raw21670step1Labels = raw21670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670step0 raw21670step0Labels permutation56 hz
    mixedMoment B raw21670step1 raw21670step1Labels = mixedMoment B raw21670step2 raw21670step2Labels := by
      have ha : raw21670step2 = (fun i j => raw21670step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21670step2 raw21670step1; decide +kernel
      have hl : raw21670step2Labels = raw21670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21670step1 raw21670step1Labels permutation9 permutation7
    mixedMoment B raw21670step2 raw21670step2Labels = mixedMoment B raw21670step3 raw21670step3Labels := by
      have ha : raw21670step3 = -raw21670step2 := by apply Matrix.ext; change ∀ i j, raw21670step3 i j = -(raw21670step2 i j); unfold raw21670step3 raw21670step2; decide +kernel
      have hl : raw21670step3Labels = raw21670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21670step3 raw21670step3Labels = mixedMoment B raw21670step4 raw21670step4Labels := by
      have ha : raw21670step4 = raw21670step3 := by apply Matrix.ext; unfold raw21670step4 raw21670step3; decide +kernel
      have hl : raw21670step3Labels = labelEmbedding1 ∘ raw21670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21670step3 raw21670step3Labels raw21670step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21671 raw21671Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21671 raw21671Labels = mixedMoment B raw21671step0 raw21671step0Labels := by
      have hz : ∀ j, raw21671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21671step0 = (fun i j => raw21671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21671step0 raw21671; decide +kernel
      have hl : raw21671step0Labels = raw21671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21671 raw21671Labels permutation346 hz
    mixedMoment B raw21671step0 raw21671step0Labels = mixedMoment B raw21671step1 raw21671step1Labels := by
      have hz : ∀ j, raw21671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21671step1 = (fun i j => raw21671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21671step1 raw21671step0; decide +kernel
      have hl : raw21671step1Labels = raw21671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21671step0 raw21671step0Labels permutation56 hz
    mixedMoment B raw21671step1 raw21671step1Labels = mixedMoment B raw21671step2 raw21671step2Labels := by
      have ha : raw21671step2 = (fun i j => raw21671step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21671step2 raw21671step1; decide +kernel
      have hl : raw21671step2Labels = raw21671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21671step1 raw21671step1Labels permutation9 permutation7
    mixedMoment B raw21671step2 raw21671step2Labels = mixedMoment B raw21671step3 raw21671step3Labels := by
      have ha : raw21671step3 = -raw21671step2 := by apply Matrix.ext; change ∀ i j, raw21671step3 i j = -(raw21671step2 i j); unfold raw21671step3 raw21671step2; decide +kernel
      have hl : raw21671step3Labels = raw21671step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21671step3 raw21671step3Labels = mixedMoment B raw21671step4 raw21671step4Labels := by
      have ha : raw21671step4 = raw21671step3 := by apply Matrix.ext; unfold raw21671step4 raw21671step3; decide +kernel
      have hl : raw21671step3Labels = labelEmbedding1 ∘ raw21671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21671step3 raw21671step3Labels raw21671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

theorem canonical21672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21672 raw21672Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21672 raw21672Labels = mixedMoment B raw21672step0 raw21672step0Labels := by
      have hz : ∀ j, raw21672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21672step0 = (fun i j => raw21672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21672step0 raw21672; decide +kernel
      have hl : raw21672step0Labels = raw21672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21672 raw21672Labels permutation346 hz
    mixedMoment B raw21672step0 raw21672step0Labels = mixedMoment B raw21672step1 raw21672step1Labels := by
      have ha : raw21672step1 = (fun i j => raw21672step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21672step1 raw21672step0; decide +kernel
      have hl : raw21672step1Labels = raw21672step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21672step0 raw21672step0Labels permutation33 permutation7
    mixedMoment B raw21672step1 raw21672step1Labels = mixedMoment B raw21672step2 raw21672step2Labels := by
      have ha : raw21672step2 = -raw21672step1 := by apply Matrix.ext; change ∀ i j, raw21672step2 i j = -(raw21672step1 i j); unfold raw21672step2 raw21672step1; decide +kernel
      have hl : raw21672step2Labels = raw21672step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21672step2 raw21672step2Labels = mixedMoment B raw21672step3 raw21672step3Labels := by
      have ha : raw21672step3 = raw21672step2 := by apply Matrix.ext; unfold raw21672step3 raw21672step2; decide +kernel
      have hl : raw21672step2Labels = labelEmbedding1 ∘ raw21672step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21672step2 raw21672step2Labels raw21672step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21673 raw21673Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21673 raw21673Labels = mixedMoment B raw21673step0 raw21673step0Labels := by
      have hz : ∀ j, raw21673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21673step0 = (fun i j => raw21673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21673step0 raw21673; decide +kernel
      have hl : raw21673step0Labels = raw21673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21673 raw21673Labels permutation265 hz
    mixedMoment B raw21673step0 raw21673step0Labels = mixedMoment B raw21673step1 raw21673step1Labels := by
      have ha : raw21673step1 = (fun i j => raw21673step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21673step1 raw21673step0; decide +kernel
      have hl : raw21673step1Labels = raw21673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21673step0 raw21673step0Labels permutation33 permutation7
    mixedMoment B raw21673step1 raw21673step1Labels = mixedMoment B raw21673step2 raw21673step2Labels := by
      have ha : raw21673step2 = -raw21673step1 := by apply Matrix.ext; change ∀ i j, raw21673step2 i j = -(raw21673step1 i j); unfold raw21673step2 raw21673step1; decide +kernel
      have hl : raw21673step2Labels = raw21673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21673step2 raw21673step2Labels = mixedMoment B raw21673step3 raw21673step3Labels := by
      have ha : raw21673step3 = raw21673step2 := by apply Matrix.ext; unfold raw21673step3 raw21673step2; decide +kernel
      have hl : raw21673step2Labels = labelEmbedding1 ∘ raw21673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21673step2 raw21673step2Labels raw21673step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical21674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21674 raw21674Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21674 raw21674Labels = mixedMoment B raw21674step0 raw21674step0Labels := by
      have hz : ∀ j, raw21674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21674step0 = (fun i j => raw21674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21674step0 raw21674; decide +kernel
      have hl : raw21674step0Labels = raw21674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21674 raw21674Labels permutation346 hz
    mixedMoment B raw21674step0 raw21674step0Labels = mixedMoment B raw21674step1 raw21674step1Labels := by
      have hz : ∀ j, raw21674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21674step1 = (fun i j => raw21674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21674step1 raw21674step0; decide +kernel
      have hl : raw21674step1Labels = raw21674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21674step0 raw21674step0Labels permutation56 hz
    mixedMoment B raw21674step1 raw21674step1Labels = mixedMoment B raw21674step2 raw21674step2Labels := by
      have ha : raw21674step2 = (fun i j => raw21674step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21674step2 raw21674step1; decide +kernel
      have hl : raw21674step2Labels = raw21674step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21674step1 raw21674step1Labels permutation9 permutation7
    mixedMoment B raw21674step2 raw21674step2Labels = mixedMoment B raw21674step3 raw21674step3Labels := by
      have ha : raw21674step3 = -raw21674step2 := by apply Matrix.ext; change ∀ i j, raw21674step3 i j = -(raw21674step2 i j); unfold raw21674step3 raw21674step2; decide +kernel
      have hl : raw21674step3Labels = raw21674step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21674step3 raw21674step3Labels = mixedMoment B raw21674step4 raw21674step4Labels := by
      have ha : raw21674step4 = raw21674step3 := by apply Matrix.ext; unfold raw21674step4 raw21674step3; decide +kernel
      have hl : raw21674step3Labels = labelEmbedding1 ∘ raw21674step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21674step3 raw21674step3Labels raw21674step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical21675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21675 raw21675Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21675 raw21675Labels = mixedMoment B raw21675step0 raw21675step0Labels := by
      have hz : ∀ j, raw21675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21675step0 = (fun i j => raw21675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21675step0 raw21675; decide +kernel
      have hl : raw21675step0Labels = raw21675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675 raw21675Labels permutation346 hz
    mixedMoment B raw21675step0 raw21675step0Labels = mixedMoment B raw21675step1 raw21675step1Labels := by
      have hz : ∀ j, raw21675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21675step1 = (fun i j => raw21675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21675step1 raw21675step0; decide +kernel
      have hl : raw21675step1Labels = raw21675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675step0 raw21675step0Labels permutation56 hz
    mixedMoment B raw21675step1 raw21675step1Labels = mixedMoment B raw21675step2 raw21675step2Labels := by
      have ha : raw21675step2 = (fun i j => raw21675step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21675step2 raw21675step1; decide +kernel
      have hl : raw21675step2Labels = raw21675step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21675step1 raw21675step1Labels permutation9 permutation7
    mixedMoment B raw21675step2 raw21675step2Labels = mixedMoment B raw21675step3 raw21675step3Labels := by
      have ha : raw21675step3 = -raw21675step2 := by apply Matrix.ext; change ∀ i j, raw21675step3 i j = -(raw21675step2 i j); unfold raw21675step3 raw21675step2; decide +kernel
      have hl : raw21675step3Labels = raw21675step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21675step3 raw21675step3Labels = mixedMoment B raw21675step4 raw21675step4Labels := by
      have ha : raw21675step4 = raw21675step3 := by apply Matrix.ext; unfold raw21675step4 raw21675step3; decide +kernel
      have hl : raw21675step3Labels = labelEmbedding1 ∘ raw21675step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21675step3 raw21675step3Labels raw21675step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical21676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21676 raw21676Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw21676 raw21676Labels = mixedMoment B raw21676step0 raw21676step0Labels := by
      have hz : ∀ j, raw21676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21676step0 = (fun i j => raw21676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21676step0 raw21676; decide +kernel
      have hl : raw21676step0Labels = raw21676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676 raw21676Labels permutation434 hz
    mixedMoment B raw21676step0 raw21676step0Labels = mixedMoment B raw21676step1 raw21676step1Labels := by
      have hz : ∀ j, raw21676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21676step1 = (fun i j => raw21676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21676step1 raw21676step0; decide +kernel
      have hl : raw21676step1Labels = raw21676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step0 raw21676step0Labels permutation80 hz
    mixedMoment B raw21676step1 raw21676step1Labels = mixedMoment B raw21676step2 raw21676step2Labels := by
      have hz : ∀ j, raw21676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21676step2 = (fun i j => raw21676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21676step2 raw21676step1; decide +kernel
      have hl : raw21676step2Labels = raw21676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step1 raw21676step1Labels permutation14 hz
    mixedMoment B raw21676step2 raw21676step2Labels = mixedMoment B raw21676step3 raw21676step3Labels := by
      have ha : raw21676step3 = (fun i j => raw21676step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21676step3 raw21676step2; decide +kernel
      have hl : raw21676step3Labels = raw21676step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21676step2 raw21676step2Labels permutation3 permutation7
    mixedMoment B raw21676step3 raw21676step3Labels = mixedMoment B raw21676step4 raw21676step4Labels := by
      have ha : raw21676step4 = -raw21676step3 := by apply Matrix.ext; change ∀ i j, raw21676step4 i j = -(raw21676step3 i j); unfold raw21676step4 raw21676step3; decide +kernel
      have hl : raw21676step4Labels = raw21676step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21676step4 raw21676step4Labels = mixedMoment B raw21676step5 raw21676step5Labels := by
      have ha : raw21676step5 = raw21676step4 := by apply Matrix.ext; unfold raw21676step5 raw21676step4; decide +kernel
      have hl : raw21676step4Labels = labelEmbedding1 ∘ raw21676step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21676step4 raw21676step4Labels raw21676step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

theorem canonical21677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21677 raw21677Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21677 raw21677Labels = mixedMoment B raw21677step0 raw21677step0Labels := by
      have hz : ∀ j, raw21677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21677step0 = (fun i j => raw21677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21677step0 raw21677; decide +kernel
      have hl : raw21677step0Labels = raw21677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677 raw21677Labels permutation434 hz
    mixedMoment B raw21677step0 raw21677step0Labels = mixedMoment B raw21677step1 raw21677step1Labels := by
      have hz : ∀ j, raw21677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21677step1 = (fun i j => raw21677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21677step1 raw21677step0; decide +kernel
      have hl : raw21677step1Labels = raw21677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677step0 raw21677step0Labels permutation80 hz
    mixedMoment B raw21677step1 raw21677step1Labels = mixedMoment B raw21677step2 raw21677step2Labels := by
      have ha : raw21677step2 = (fun i j => raw21677step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21677step2 raw21677step1; decide +kernel
      have hl : raw21677step2Labels = raw21677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21677step1 raw21677step1Labels permutation9 permutation7
    mixedMoment B raw21677step2 raw21677step2Labels = mixedMoment B raw21677step3 raw21677step3Labels := by
      have ha : raw21677step3 = -raw21677step2 := by apply Matrix.ext; change ∀ i j, raw21677step3 i j = -(raw21677step2 i j); unfold raw21677step3 raw21677step2; decide +kernel
      have hl : raw21677step3Labels = raw21677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21677step3 raw21677step3Labels = mixedMoment B raw21677step4 raw21677step4Labels := by
      have ha : raw21677step4 = raw21677step3 := by apply Matrix.ext; unfold raw21677step4 raw21677step3; decide +kernel
      have hl : raw21677step3Labels = labelEmbedding1 ∘ raw21677step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21677step3 raw21677step3Labels raw21677step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21678 raw21678Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21678 raw21678Labels = mixedMoment B raw21678step0 raw21678step0Labels := by
      have hz : ∀ j, raw21678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21678step0 = (fun i j => raw21678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21678step0 raw21678; decide +kernel
      have hl : raw21678step0Labels = raw21678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678 raw21678Labels permutation434 hz
    mixedMoment B raw21678step0 raw21678step0Labels = mixedMoment B raw21678step1 raw21678step1Labels := by
      have hz : ∀ j, raw21678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21678step1 = (fun i j => raw21678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21678step1 raw21678step0; decide +kernel
      have hl : raw21678step1Labels = raw21678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678step0 raw21678step0Labels permutation56 hz
    mixedMoment B raw21678step1 raw21678step1Labels = mixedMoment B raw21678step2 raw21678step2Labels := by
      have ha : raw21678step2 = (fun i j => raw21678step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21678step2 raw21678step1; decide +kernel
      have hl : raw21678step2Labels = raw21678step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21678step1 raw21678step1Labels permutation9 permutation7
    mixedMoment B raw21678step2 raw21678step2Labels = mixedMoment B raw21678step3 raw21678step3Labels := by
      have ha : raw21678step3 = -raw21678step2 := by apply Matrix.ext; change ∀ i j, raw21678step3 i j = -(raw21678step2 i j); unfold raw21678step3 raw21678step2; decide +kernel
      have hl : raw21678step3Labels = raw21678step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21678step3 raw21678step3Labels = mixedMoment B raw21678step4 raw21678step4Labels := by
      have ha : raw21678step4 = raw21678step3 := by apply Matrix.ext; unfold raw21678step4 raw21678step3; decide +kernel
      have hl : raw21678step3Labels = labelEmbedding1 ∘ raw21678step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21678step3 raw21678step3Labels raw21678step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21679 raw21679Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21679 raw21679Labels = mixedMoment B raw21679step0 raw21679step0Labels := by
      have hz : ∀ j, raw21679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21679step0 = (fun i j => raw21679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21679step0 raw21679; decide +kernel
      have hl : raw21679step0Labels = raw21679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679 raw21679Labels permutation346 hz
    mixedMoment B raw21679step0 raw21679step0Labels = mixedMoment B raw21679step1 raw21679step1Labels := by
      have hz : ∀ j, raw21679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21679step1 = (fun i j => raw21679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21679step1 raw21679step0; decide +kernel
      have hl : raw21679step1Labels = raw21679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679step0 raw21679step0Labels permutation56 hz
    mixedMoment B raw21679step1 raw21679step1Labels = mixedMoment B raw21679step2 raw21679step2Labels := by
      have ha : raw21679step2 = (fun i j => raw21679step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21679step2 raw21679step1; decide +kernel
      have hl : raw21679step2Labels = raw21679step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21679step1 raw21679step1Labels permutation9 permutation7
    mixedMoment B raw21679step2 raw21679step2Labels = mixedMoment B raw21679step3 raw21679step3Labels := by
      have ha : raw21679step3 = -raw21679step2 := by apply Matrix.ext; change ∀ i j, raw21679step3 i j = -(raw21679step2 i j); unfold raw21679step3 raw21679step2; decide +kernel
      have hl : raw21679step3Labels = raw21679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21679step3 raw21679step3Labels = mixedMoment B raw21679step4 raw21679step4Labels := by
      have ha : raw21679step4 = raw21679step3 := by apply Matrix.ext; unfold raw21679step4 raw21679step3; decide +kernel
      have hl : raw21679step3Labels = labelEmbedding1 ∘ raw21679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21679step3 raw21679step3Labels raw21679step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical21680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21680 raw21680Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw21680 raw21680Labels = mixedMoment B raw21680step0 raw21680step0Labels := by
      have hz : ∀ j, raw21680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21680step0 = (fun i j => raw21680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21680step0 raw21680; decide +kernel
      have hl : raw21680step0Labels = raw21680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680 raw21680Labels permutation434 hz
    mixedMoment B raw21680step0 raw21680step0Labels = mixedMoment B raw21680step1 raw21680step1Labels := by
      have hz : ∀ j, raw21680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21680step1 = (fun i j => raw21680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21680step1 raw21680step0; decide +kernel
      have hl : raw21680step1Labels = raw21680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step0 raw21680step0Labels permutation80 hz
    mixedMoment B raw21680step1 raw21680step1Labels = mixedMoment B raw21680step2 raw21680step2Labels := by
      have hz : ∀ j, raw21680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21680step2 = (fun i j => raw21680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21680step2 raw21680step1; decide +kernel
      have hl : raw21680step2Labels = raw21680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step1 raw21680step1Labels permutation14 hz
    mixedMoment B raw21680step2 raw21680step2Labels = mixedMoment B raw21680step3 raw21680step3Labels := by
      have ha : raw21680step3 = (fun i j => raw21680step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21680step3 raw21680step2; decide +kernel
      have hl : raw21680step3Labels = raw21680step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21680step2 raw21680step2Labels permutation3 permutation7
    mixedMoment B raw21680step3 raw21680step3Labels = mixedMoment B raw21680step4 raw21680step4Labels := by
      have ha : raw21680step4 = -raw21680step3 := by apply Matrix.ext; change ∀ i j, raw21680step4 i j = -(raw21680step3 i j); unfold raw21680step4 raw21680step3; decide +kernel
      have hl : raw21680step4Labels = raw21680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21680step4 raw21680step4Labels = mixedMoment B raw21680step5 raw21680step5Labels := by
      have ha : raw21680step5 = raw21680step4 := by apply Matrix.ext; unfold raw21680step5 raw21680step4; decide +kernel
      have hl : raw21680step4Labels = labelEmbedding1 ∘ raw21680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21680step4 raw21680step4Labels raw21680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

theorem canonical21681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21681 raw21681Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw21681 raw21681Labels = mixedMoment B raw21681step0 raw21681step0Labels := by
      have hz : ∀ j, raw21681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21681step0 = (fun i j => raw21681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21681step0 raw21681; decide +kernel
      have hl : raw21681step0Labels = raw21681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681 raw21681Labels permutation434 hz
    mixedMoment B raw21681step0 raw21681step0Labels = mixedMoment B raw21681step1 raw21681step1Labels := by
      have hz : ∀ j, raw21681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21681step1 = (fun i j => raw21681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21681step1 raw21681step0; decide +kernel
      have hl : raw21681step1Labels = raw21681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681step0 raw21681step0Labels permutation80 hz
    mixedMoment B raw21681step1 raw21681step1Labels = mixedMoment B raw21681step2 raw21681step2Labels := by
      have hz : ∀ j, raw21681step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21681step2 = (fun i j => raw21681step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21681step2 raw21681step1; decide +kernel
      have hl : raw21681step2Labels = raw21681step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681step1 raw21681step1Labels permutation14 hz
    mixedMoment B raw21681step2 raw21681step2Labels = mixedMoment B raw21681step3 raw21681step3Labels := by
      have ha : raw21681step3 = (fun i j => raw21681step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21681step3 raw21681step2; decide +kernel
      have hl : raw21681step3Labels = raw21681step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21681step2 raw21681step2Labels permutation3 permutation7
    mixedMoment B raw21681step3 raw21681step3Labels = mixedMoment B raw21681step4 raw21681step4Labels := by
      have ha : raw21681step4 = -raw21681step3 := by apply Matrix.ext; change ∀ i j, raw21681step4 i j = -(raw21681step3 i j); unfold raw21681step4 raw21681step3; decide +kernel
      have hl : raw21681step4Labels = raw21681step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21681step4 raw21681step4Labels = mixedMoment B raw21681step5 raw21681step5Labels := by
      have ha : raw21681step5 = raw21681step4 := by apply Matrix.ext; unfold raw21681step5 raw21681step4; decide +kernel
      have hl : raw21681step4Labels = labelEmbedding1 ∘ raw21681step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21681step4 raw21681step4Labels raw21681step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

theorem canonical21682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21682 raw21682Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21682 raw21682Labels = mixedMoment B raw21682step0 raw21682step0Labels := by
      have hz : ∀ j, raw21682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21682step0 = (fun i j => raw21682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21682step0 raw21682; decide +kernel
      have hl : raw21682step0Labels = raw21682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21682 raw21682Labels permutation434 hz
    mixedMoment B raw21682step0 raw21682step0Labels = mixedMoment B raw21682step1 raw21682step1Labels := by
      have hz : ∀ j, raw21682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21682step1 = (fun i j => raw21682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21682step1 raw21682step0; decide +kernel
      have hl : raw21682step1Labels = raw21682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21682step0 raw21682step0Labels permutation80 hz
    mixedMoment B raw21682step1 raw21682step1Labels = mixedMoment B raw21682step2 raw21682step2Labels := by
      have ha : raw21682step2 = (fun i j => raw21682step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21682step2 raw21682step1; decide +kernel
      have hl : raw21682step2Labels = raw21682step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21682step1 raw21682step1Labels permutation9 permutation7
    mixedMoment B raw21682step2 raw21682step2Labels = mixedMoment B raw21682step3 raw21682step3Labels := by
      have ha : raw21682step3 = -raw21682step2 := by apply Matrix.ext; change ∀ i j, raw21682step3 i j = -(raw21682step2 i j); unfold raw21682step3 raw21682step2; decide +kernel
      have hl : raw21682step3Labels = raw21682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21682step3 raw21682step3Labels = mixedMoment B raw21682step4 raw21682step4Labels := by
      have ha : raw21682step4 = raw21682step3 := by apply Matrix.ext; unfold raw21682step4 raw21682step3; decide +kernel
      have hl : raw21682step3Labels = labelEmbedding1 ∘ raw21682step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21682step3 raw21682step3Labels raw21682step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical21683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21683 raw21683Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21683 raw21683Labels = mixedMoment B raw21683step0 raw21683step0Labels := by
      have hz : ∀ j, raw21683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21683step0 = (fun i j => raw21683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21683step0 raw21683; decide +kernel
      have hl : raw21683step0Labels = raw21683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21683 raw21683Labels permutation434 hz
    mixedMoment B raw21683step0 raw21683step0Labels = mixedMoment B raw21683step1 raw21683step1Labels := by
      have hz : ∀ j, raw21683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21683step1 = (fun i j => raw21683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21683step1 raw21683step0; decide +kernel
      have hl : raw21683step1Labels = raw21683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21683step0 raw21683step0Labels permutation56 hz
    mixedMoment B raw21683step1 raw21683step1Labels = mixedMoment B raw21683step2 raw21683step2Labels := by
      have ha : raw21683step2 = (fun i j => raw21683step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21683step2 raw21683step1; decide +kernel
      have hl : raw21683step2Labels = raw21683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21683step1 raw21683step1Labels permutation9 permutation7
    mixedMoment B raw21683step2 raw21683step2Labels = mixedMoment B raw21683step3 raw21683step3Labels := by
      have ha : raw21683step3 = -raw21683step2 := by apply Matrix.ext; change ∀ i j, raw21683step3 i j = -(raw21683step2 i j); unfold raw21683step3 raw21683step2; decide +kernel
      have hl : raw21683step3Labels = raw21683step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21683step3 raw21683step3Labels = mixedMoment B raw21683step4 raw21683step4Labels := by
      have ha : raw21683step4 = raw21683step3 := by apply Matrix.ext; unfold raw21683step4 raw21683step3; decide +kernel
      have hl : raw21683step3Labels = labelEmbedding1 ∘ raw21683step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21683step3 raw21683step3Labels raw21683step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical21684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21684 raw21684Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21684 raw21684Labels = mixedMoment B raw21684step0 raw21684step0Labels := by
      have hz : ∀ j, raw21684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21684step0 = (fun i j => raw21684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21684step0 raw21684; decide +kernel
      have hl : raw21684step0Labels = raw21684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21684 raw21684Labels permutation346 hz
    mixedMoment B raw21684step0 raw21684step0Labels = mixedMoment B raw21684step1 raw21684step1Labels := by
      have hz : ∀ j, raw21684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21684step1 = (fun i j => raw21684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21684step1 raw21684step0; decide +kernel
      have hl : raw21684step1Labels = raw21684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21684step0 raw21684step0Labels permutation56 hz
    mixedMoment B raw21684step1 raw21684step1Labels = mixedMoment B raw21684step2 raw21684step2Labels := by
      have ha : raw21684step2 = (fun i j => raw21684step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21684step2 raw21684step1; decide +kernel
      have hl : raw21684step2Labels = raw21684step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21684step1 raw21684step1Labels permutation9 permutation7
    mixedMoment B raw21684step2 raw21684step2Labels = mixedMoment B raw21684step3 raw21684step3Labels := by
      have ha : raw21684step3 = -raw21684step2 := by apply Matrix.ext; change ∀ i j, raw21684step3 i j = -(raw21684step2 i j); unfold raw21684step3 raw21684step2; decide +kernel
      have hl : raw21684step3Labels = raw21684step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21684step3 raw21684step3Labels = mixedMoment B raw21684step4 raw21684step4Labels := by
      have ha : raw21684step4 = raw21684step3 := by apply Matrix.ext; unfold raw21684step4 raw21684step3; decide +kernel
      have hl : raw21684step3Labels = labelEmbedding1 ∘ raw21684step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21684step3 raw21684step3Labels raw21684step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

theorem canonical21685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21685 raw21685Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw21685 raw21685Labels = mixedMoment B raw21685step0 raw21685step0Labels := by
      have hz : ∀ j, raw21685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21685step0 = (fun i j => raw21685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21685step0 raw21685; decide +kernel
      have hl : raw21685step0Labels = raw21685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685 raw21685Labels permutation434 hz
    mixedMoment B raw21685step0 raw21685step0Labels = mixedMoment B raw21685step1 raw21685step1Labels := by
      have hz : ∀ j, raw21685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21685step1 = (fun i j => raw21685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21685step1 raw21685step0; decide +kernel
      have hl : raw21685step1Labels = raw21685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685step0 raw21685step0Labels permutation80 hz
    mixedMoment B raw21685step1 raw21685step1Labels = mixedMoment B raw21685step2 raw21685step2Labels := by
      have hz : ∀ j, raw21685step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21685step2 = (fun i j => raw21685step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21685step2 raw21685step1; decide +kernel
      have hl : raw21685step2Labels = raw21685step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685step1 raw21685step1Labels permutation14 hz
    mixedMoment B raw21685step2 raw21685step2Labels = mixedMoment B raw21685step3 raw21685step3Labels := by
      have ha : raw21685step3 = (fun i j => raw21685step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21685step3 raw21685step2; decide +kernel
      have hl : raw21685step3Labels = raw21685step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21685step2 raw21685step2Labels permutation6 permutation5
    mixedMoment B raw21685step3 raw21685step3Labels = mixedMoment B raw21685step4 raw21685step4Labels := by
      have ha : raw21685step4 = raw21685step3 := by apply Matrix.ext; unfold raw21685step4 raw21685step3; decide +kernel
      have hl : raw21685step3Labels = labelEmbedding1 ∘ raw21685step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21685step3 raw21685step3Labels raw21685step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

theorem canonical21686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21686 raw21686Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw21686 raw21686Labels = mixedMoment B raw21686step0 raw21686step0Labels := by
      have hz : ∀ j, raw21686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21686step0 = (fun i j => raw21686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21686step0 raw21686; decide +kernel
      have hl : raw21686step0Labels = raw21686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21686 raw21686Labels permutation434 hz
    mixedMoment B raw21686step0 raw21686step0Labels = mixedMoment B raw21686step1 raw21686step1Labels := by
      have hz : ∀ j, raw21686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21686step1 = (fun i j => raw21686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21686step1 raw21686step0; decide +kernel
      have hl : raw21686step1Labels = raw21686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21686step0 raw21686step0Labels permutation80 hz
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical21687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21687 raw21687Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw21687 raw21687Labels = mixedMoment B raw21687step0 raw21687step0Labels := by
      have hz : ∀ j, raw21687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21687step0 = (fun i j => raw21687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21687step0 raw21687; decide +kernel
      have hl : raw21687step0Labels = raw21687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21687 raw21687Labels permutation434 hz
    _ = mixedMoment B node925 node925Labels := by rfl

theorem canonical21688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21688 raw21688Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw21688 raw21688Labels = mixedMoment B raw21688step0 raw21688step0Labels := by
      have hz : ∀ j, raw21688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21688step0 = (fun i j => raw21688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21688step0 raw21688; decide +kernel
      have hl : raw21688step0Labels = raw21688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21688 raw21688Labels permutation346 hz
    _ = mixedMoment B node925 node925Labels := by rfl

theorem canonical21689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21689 raw21689Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw21689 raw21689Labels = mixedMoment B raw21689step0 raw21689step0Labels := by
      have hz : ∀ j, raw21689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21689step0 = (fun i j => raw21689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21689step0 raw21689; decide +kernel
      have hl : raw21689step0Labels = raw21689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21689 raw21689Labels permutation434 hz
    mixedMoment B raw21689step0 raw21689step0Labels = mixedMoment B raw21689step1 raw21689step1Labels := by
      have hz : ∀ j, raw21689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21689step1 = (fun i j => raw21689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21689step1 raw21689step0; decide +kernel
      have hl : raw21689step1Labels = raw21689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21689step0 raw21689step0Labels permutation80 hz
    _ = mixedMoment B node939 node939Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21801 raw21801Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21801 raw21801Labels = mixedMoment B raw21801step0 raw21801step0Labels := by
      have hz : ∀ j, raw21801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21801step0 = (fun i j => raw21801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21801step0 raw21801; decide +kernel
      have hl : raw21801step0Labels = raw21801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21801 raw21801Labels permutation434 hz
    mixedMoment B raw21801step0 raw21801step0Labels = mixedMoment B raw21801step1 raw21801step1Labels := by
      have hz : ∀ j, raw21801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21801step1 = (fun i j => raw21801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21801step1 raw21801step0; decide +kernel
      have hl : raw21801step1Labels = raw21801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21801step0 raw21801step0Labels permutation80 hz
    mixedMoment B raw21801step1 raw21801step1Labels = mixedMoment B raw21801step2 raw21801step2Labels := by
      have ha : raw21801step2 = (fun i j => raw21801step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21801step2 raw21801step1; decide +kernel
      have hl : raw21801step2Labels = raw21801step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21801step1 raw21801step1Labels permutation8 permutation7
    mixedMoment B raw21801step2 raw21801step2Labels = mixedMoment B raw21801step3 raw21801step3Labels := by
      have ha : raw21801step3 = -raw21801step2 := by apply Matrix.ext; change ∀ i j, raw21801step3 i j = -(raw21801step2 i j); unfold raw21801step3 raw21801step2; decide +kernel
      have hl : raw21801step3Labels = raw21801step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21801step3 raw21801step3Labels = mixedMoment B raw21801step4 raw21801step4Labels := by
      have ha : raw21801step4 = raw21801step3 := by apply Matrix.ext; unfold raw21801step4 raw21801step3; decide +kernel
      have hl : raw21801step3Labels = labelEmbedding1 ∘ raw21801step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21801step3 raw21801step3Labels raw21801step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical21802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21802 raw21802Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21802 raw21802Labels = mixedMoment B raw21802step0 raw21802step0Labels := by
      have hz : ∀ j, raw21802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21802step0 = (fun i j => raw21802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21802step0 raw21802; decide +kernel
      have hl : raw21802step0Labels = raw21802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21802 raw21802Labels permutation434 hz
    mixedMoment B raw21802step0 raw21802step0Labels = mixedMoment B raw21802step1 raw21802step1Labels := by
      have hz : ∀ j, raw21802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21802step1 = (fun i j => raw21802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21802step1 raw21802step0; decide +kernel
      have hl : raw21802step1Labels = raw21802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21802step0 raw21802step0Labels permutation56 hz
    mixedMoment B raw21802step1 raw21802step1Labels = mixedMoment B raw21802step2 raw21802step2Labels := by
      have ha : raw21802step2 = (fun i j => raw21802step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21802step2 raw21802step1; decide +kernel
      have hl : raw21802step2Labels = raw21802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21802step1 raw21802step1Labels permutation8 permutation7
    mixedMoment B raw21802step2 raw21802step2Labels = mixedMoment B raw21802step3 raw21802step3Labels := by
      have ha : raw21802step3 = -raw21802step2 := by apply Matrix.ext; change ∀ i j, raw21802step3 i j = -(raw21802step2 i j); unfold raw21802step3 raw21802step2; decide +kernel
      have hl : raw21802step3Labels = raw21802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21802step3 raw21802step3Labels = mixedMoment B raw21802step4 raw21802step4Labels := by
      have ha : raw21802step4 = raw21802step3 := by apply Matrix.ext; unfold raw21802step4 raw21802step3; decide +kernel
      have hl : raw21802step3Labels = labelEmbedding1 ∘ raw21802step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21802step3 raw21802step3Labels raw21802step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical21803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21803 raw21803Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21803 raw21803Labels = mixedMoment B raw21803step0 raw21803step0Labels := by
      have hz : ∀ j, raw21803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21803step0 = (fun i j => raw21803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21803step0 raw21803; decide +kernel
      have hl : raw21803step0Labels = raw21803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21803 raw21803Labels permutation346 hz
    mixedMoment B raw21803step0 raw21803step0Labels = mixedMoment B raw21803step1 raw21803step1Labels := by
      have hz : ∀ j, raw21803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21803step1 = (fun i j => raw21803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21803step1 raw21803step0; decide +kernel
      have hl : raw21803step1Labels = raw21803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21803step0 raw21803step0Labels permutation56 hz
    mixedMoment B raw21803step1 raw21803step1Labels = mixedMoment B raw21803step2 raw21803step2Labels := by
      have ha : raw21803step2 = (fun i j => raw21803step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21803step2 raw21803step1; decide +kernel
      have hl : raw21803step2Labels = raw21803step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21803step1 raw21803step1Labels permutation8 permutation7
    mixedMoment B raw21803step2 raw21803step2Labels = mixedMoment B raw21803step3 raw21803step3Labels := by
      have ha : raw21803step3 = -raw21803step2 := by apply Matrix.ext; change ∀ i j, raw21803step3 i j = -(raw21803step2 i j); unfold raw21803step3 raw21803step2; decide +kernel
      have hl : raw21803step3Labels = raw21803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21803step3 raw21803step3Labels = mixedMoment B raw21803step4 raw21803step4Labels := by
      have ha : raw21803step4 = raw21803step3 := by apply Matrix.ext; unfold raw21803step4 raw21803step3; decide +kernel
      have hl : raw21803step3Labels = labelEmbedding1 ∘ raw21803step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21803step3 raw21803step3Labels raw21803step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical21804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21804 raw21804Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw21804 raw21804Labels = mixedMoment B raw21804step0 raw21804step0Labels := by
      have hz : ∀ j, raw21804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21804step0 = (fun i j => raw21804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21804step0 raw21804; decide +kernel
      have hl : raw21804step0Labels = raw21804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804 raw21804Labels permutation434 hz
    mixedMoment B raw21804step0 raw21804step0Labels = mixedMoment B raw21804step1 raw21804step1Labels := by
      have hz : ∀ j, raw21804step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21804step1 = (fun i j => raw21804step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21804step1 raw21804step0; decide +kernel
      have hl : raw21804step1Labels = raw21804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804step0 raw21804step0Labels permutation80 hz
    mixedMoment B raw21804step1 raw21804step1Labels = mixedMoment B raw21804step2 raw21804step2Labels := by
      have hz : ∀ j, raw21804step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21804step2 = (fun i j => raw21804step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21804step2 raw21804step1; decide +kernel
      have hl : raw21804step2Labels = raw21804step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804step1 raw21804step1Labels permutation14 hz
    mixedMoment B raw21804step2 raw21804step2Labels = mixedMoment B raw21804step3 raw21804step3Labels := by
      have ha : raw21804step3 = (fun i j => raw21804step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21804step3 raw21804step2; decide +kernel
      have hl : raw21804step3Labels = raw21804step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21804step2 raw21804step2Labels permutation2 permutation7
    mixedMoment B raw21804step3 raw21804step3Labels = mixedMoment B raw21804step4 raw21804step4Labels := by
      have ha : raw21804step4 = -raw21804step3 := by apply Matrix.ext; change ∀ i j, raw21804step4 i j = -(raw21804step3 i j); unfold raw21804step4 raw21804step3; decide +kernel
      have hl : raw21804step4Labels = raw21804step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21804step4 raw21804step4Labels = mixedMoment B raw21804step5 raw21804step5Labels := by
      have ha : raw21804step5 = raw21804step4 := by apply Matrix.ext; unfold raw21804step5 raw21804step4; decide +kernel
      have hl : raw21804step4Labels = labelEmbedding1 ∘ raw21804step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21804step4 raw21804step4Labels raw21804step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical21805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21805 raw21805Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21805 raw21805Labels = mixedMoment B raw21805step0 raw21805step0Labels := by
      have hz : ∀ j, raw21805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21805step0 = (fun i j => raw21805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21805step0 raw21805; decide +kernel
      have hl : raw21805step0Labels = raw21805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805 raw21805Labels permutation434 hz
    mixedMoment B raw21805step0 raw21805step0Labels = mixedMoment B raw21805step1 raw21805step1Labels := by
      have hz : ∀ j, raw21805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21805step1 = (fun i j => raw21805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21805step1 raw21805step0; decide +kernel
      have hl : raw21805step1Labels = raw21805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805step0 raw21805step0Labels permutation80 hz
    mixedMoment B raw21805step1 raw21805step1Labels = mixedMoment B raw21805step2 raw21805step2Labels := by
      have hz : ∀ j, raw21805step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21805step2 = (fun i j => raw21805step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21805step2 raw21805step1; decide +kernel
      have hl : raw21805step2Labels = raw21805step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805step1 raw21805step1Labels permutation14 hz
    mixedMoment B raw21805step2 raw21805step2Labels = mixedMoment B raw21805step3 raw21805step3Labels := by
      have hz : ∀ i, raw21805step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21805step3 = (fun i j => raw21805step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21805step3 raw21805step2; decide +kernel
      have hl : raw21805step3Labels = (fun j => raw21805step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21805step2 raw21805step2Labels permutation4 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical21806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21806 raw21806Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21806 raw21806Labels = mixedMoment B raw21806step0 raw21806step0Labels := by
      have hz : ∀ j, raw21806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21806step0 = (fun i j => raw21806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21806step0 raw21806; decide +kernel
      have hl : raw21806step0Labels = raw21806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21806 raw21806Labels permutation434 hz
    mixedMoment B raw21806step0 raw21806step0Labels = mixedMoment B raw21806step1 raw21806step1Labels := by
      have hz : ∀ j, raw21806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21806step1 = (fun i j => raw21806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21806step1 raw21806step0; decide +kernel
      have hl : raw21806step1Labels = raw21806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21806step0 raw21806step0Labels permutation80 hz
    mixedMoment B raw21806step1 raw21806step1Labels = mixedMoment B raw21806step2 raw21806step2Labels := by
      have ha : raw21806step2 = (fun i j => raw21806step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21806step2 raw21806step1; decide +kernel
      have hl : raw21806step2Labels = raw21806step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21806step1 raw21806step1Labels permutation8 permutation7
    mixedMoment B raw21806step2 raw21806step2Labels = mixedMoment B raw21806step3 raw21806step3Labels := by
      have ha : raw21806step3 = -raw21806step2 := by apply Matrix.ext; change ∀ i j, raw21806step3 i j = -(raw21806step2 i j); unfold raw21806step3 raw21806step2; decide +kernel
      have hl : raw21806step3Labels = raw21806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21806step3 raw21806step3Labels = mixedMoment B raw21806step4 raw21806step4Labels := by
      have ha : raw21806step4 = raw21806step3 := by apply Matrix.ext; unfold raw21806step4 raw21806step3; decide +kernel
      have hl : raw21806step3Labels = labelEmbedding1 ∘ raw21806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21806step3 raw21806step3Labels raw21806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical21807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21807 raw21807Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21807 raw21807Labels = mixedMoment B raw21807step0 raw21807step0Labels := by
      have hz : ∀ j, raw21807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21807step0 = (fun i j => raw21807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21807step0 raw21807; decide +kernel
      have hl : raw21807step0Labels = raw21807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21807 raw21807Labels permutation434 hz
    mixedMoment B raw21807step0 raw21807step0Labels = mixedMoment B raw21807step1 raw21807step1Labels := by
      have ha : raw21807step1 = (fun i j => raw21807step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21807step1 raw21807step0; decide +kernel
      have hl : raw21807step1Labels = raw21807step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21807step0 raw21807step0Labels permutation38 permutation7
    mixedMoment B raw21807step1 raw21807step1Labels = mixedMoment B raw21807step2 raw21807step2Labels := by
      have ha : raw21807step2 = -raw21807step1 := by apply Matrix.ext; change ∀ i j, raw21807step2 i j = -(raw21807step1 i j); unfold raw21807step2 raw21807step1; decide +kernel
      have hl : raw21807step2Labels = raw21807step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21807step2 raw21807step2Labels = mixedMoment B raw21807step3 raw21807step3Labels := by
      have ha : raw21807step3 = raw21807step2 := by apply Matrix.ext; unfold raw21807step3 raw21807step2; decide +kernel
      have hl : raw21807step2Labels = labelEmbedding1 ∘ raw21807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21807step2 raw21807step2Labels raw21807step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21808 raw21808Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21808 raw21808Labels = mixedMoment B raw21808step0 raw21808step0Labels := by
      have hz : ∀ j, raw21808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21808step0 = (fun i j => raw21808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21808step0 raw21808; decide +kernel
      have hl : raw21808step0Labels = raw21808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21808 raw21808Labels permutation346 hz
    mixedMoment B raw21808step0 raw21808step0Labels = mixedMoment B raw21808step1 raw21808step1Labels := by
      have ha : raw21808step1 = (fun i j => raw21808step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21808step1 raw21808step0; decide +kernel
      have hl : raw21808step1Labels = raw21808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21808step0 raw21808step0Labels permutation38 permutation7
    mixedMoment B raw21808step1 raw21808step1Labels = mixedMoment B raw21808step2 raw21808step2Labels := by
      have ha : raw21808step2 = -raw21808step1 := by apply Matrix.ext; change ∀ i j, raw21808step2 i j = -(raw21808step1 i j); unfold raw21808step2 raw21808step1; decide +kernel
      have hl : raw21808step2Labels = raw21808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21808step2 raw21808step2Labels = mixedMoment B raw21808step3 raw21808step3Labels := by
      have ha : raw21808step3 = raw21808step2 := by apply Matrix.ext; unfold raw21808step3 raw21808step2; decide +kernel
      have hl : raw21808step2Labels = labelEmbedding1 ∘ raw21808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21808step2 raw21808step2Labels raw21808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21809 raw21809Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21809 raw21809Labels = mixedMoment B raw21809step0 raw21809step0Labels := by
      have hz : ∀ j, raw21809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21809step0 = (fun i j => raw21809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21809step0 raw21809; decide +kernel
      have hl : raw21809step0Labels = raw21809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21809 raw21809Labels permutation434 hz
    mixedMoment B raw21809step0 raw21809step0Labels = mixedMoment B raw21809step1 raw21809step1Labels := by
      have hz : ∀ j, raw21809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21809step1 = (fun i j => raw21809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21809step1 raw21809step0; decide +kernel
      have hl : raw21809step1Labels = raw21809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21809step0 raw21809step0Labels permutation80 hz
    mixedMoment B raw21809step1 raw21809step1Labels = mixedMoment B raw21809step2 raw21809step2Labels := by
      have ha : raw21809step2 = (fun i j => raw21809step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21809step2 raw21809step1; decide +kernel
      have hl : raw21809step2Labels = raw21809step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21809step1 raw21809step1Labels permutation8 permutation7
    mixedMoment B raw21809step2 raw21809step2Labels = mixedMoment B raw21809step3 raw21809step3Labels := by
      have ha : raw21809step3 = -raw21809step2 := by apply Matrix.ext; change ∀ i j, raw21809step3 i j = -(raw21809step2 i j); unfold raw21809step3 raw21809step2; decide +kernel
      have hl : raw21809step3Labels = raw21809step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21809step3 raw21809step3Labels = mixedMoment B raw21809step4 raw21809step4Labels := by
      have ha : raw21809step4 = raw21809step3 := by apply Matrix.ext; unfold raw21809step4 raw21809step3; decide +kernel
      have hl : raw21809step3Labels = labelEmbedding1 ∘ raw21809step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21809step3 raw21809step3Labels raw21809step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21810 raw21810Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21810 raw21810Labels = mixedMoment B raw21810step0 raw21810step0Labels := by
      have hz : ∀ j, raw21810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21810step0 = (fun i j => raw21810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21810step0 raw21810; decide +kernel
      have hl : raw21810step0Labels = raw21810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21810 raw21810Labels permutation434 hz
    mixedMoment B raw21810step0 raw21810step0Labels = mixedMoment B raw21810step1 raw21810step1Labels := by
      have hz : ∀ j, raw21810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21810step1 = (fun i j => raw21810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21810step1 raw21810step0; decide +kernel
      have hl : raw21810step1Labels = raw21810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21810step0 raw21810step0Labels permutation80 hz
    mixedMoment B raw21810step1 raw21810step1Labels = mixedMoment B raw21810step2 raw21810step2Labels := by
      have ha : raw21810step2 = (fun i j => raw21810step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21810step2 raw21810step1; decide +kernel
      have hl : raw21810step2Labels = raw21810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21810step1 raw21810step1Labels permutation8 permutation7
    mixedMoment B raw21810step2 raw21810step2Labels = mixedMoment B raw21810step3 raw21810step3Labels := by
      have ha : raw21810step3 = -raw21810step2 := by apply Matrix.ext; change ∀ i j, raw21810step3 i j = -(raw21810step2 i j); unfold raw21810step3 raw21810step2; decide +kernel
      have hl : raw21810step3Labels = raw21810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21810step3 raw21810step3Labels = mixedMoment B raw21810step4 raw21810step4Labels := by
      have ha : raw21810step4 = raw21810step3 := by apply Matrix.ext; unfold raw21810step4 raw21810step3; decide +kernel
      have hl : raw21810step3Labels = labelEmbedding1 ∘ raw21810step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21810step3 raw21810step3Labels raw21810step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical21811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21811 raw21811Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21811 raw21811Labels = mixedMoment B raw21811step0 raw21811step0Labels := by
      have hz : ∀ j, raw21811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21811step0 = (fun i j => raw21811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21811step0 raw21811; decide +kernel
      have hl : raw21811step0Labels = raw21811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21811 raw21811Labels permutation434 hz
    mixedMoment B raw21811step0 raw21811step0Labels = mixedMoment B raw21811step1 raw21811step1Labels := by
      have hz : ∀ j, raw21811step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21811step1 = (fun i j => raw21811step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21811step1 raw21811step0; decide +kernel
      have hl : raw21811step1Labels = raw21811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21811step0 raw21811step0Labels permutation56 hz
    mixedMoment B raw21811step1 raw21811step1Labels = mixedMoment B raw21811step2 raw21811step2Labels := by
      have ha : raw21811step2 = (fun i j => raw21811step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21811step2 raw21811step1; decide +kernel
      have hl : raw21811step2Labels = raw21811step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21811step1 raw21811step1Labels permutation8 permutation7
    mixedMoment B raw21811step2 raw21811step2Labels = mixedMoment B raw21811step3 raw21811step3Labels := by
      have ha : raw21811step3 = -raw21811step2 := by apply Matrix.ext; change ∀ i j, raw21811step3 i j = -(raw21811step2 i j); unfold raw21811step3 raw21811step2; decide +kernel
      have hl : raw21811step3Labels = raw21811step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21811step3 raw21811step3Labels = mixedMoment B raw21811step4 raw21811step4Labels := by
      have ha : raw21811step4 = raw21811step3 := by apply Matrix.ext; unfold raw21811step4 raw21811step3; decide +kernel
      have hl : raw21811step3Labels = labelEmbedding1 ∘ raw21811step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21811step3 raw21811step3Labels raw21811step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical21812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21812 raw21812Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21812 raw21812Labels = mixedMoment B raw21812step0 raw21812step0Labels := by
      have hz : ∀ j, raw21812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21812step0 = (fun i j => raw21812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21812step0 raw21812; decide +kernel
      have hl : raw21812step0Labels = raw21812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21812 raw21812Labels permutation434 hz
    mixedMoment B raw21812step0 raw21812step0Labels = mixedMoment B raw21812step1 raw21812step1Labels := by
      have ha : raw21812step1 = (fun i j => raw21812step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21812step1 raw21812step0; decide +kernel
      have hl : raw21812step1Labels = raw21812step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21812step0 raw21812step0Labels permutation32 permutation7
    mixedMoment B raw21812step1 raw21812step1Labels = mixedMoment B raw21812step2 raw21812step2Labels := by
      have ha : raw21812step2 = -raw21812step1 := by apply Matrix.ext; change ∀ i j, raw21812step2 i j = -(raw21812step1 i j); unfold raw21812step2 raw21812step1; decide +kernel
      have hl : raw21812step2Labels = raw21812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21812step2 raw21812step2Labels = mixedMoment B raw21812step3 raw21812step3Labels := by
      have ha : raw21812step3 = raw21812step2 := by apply Matrix.ext; unfold raw21812step3 raw21812step2; decide +kernel
      have hl : raw21812step2Labels = labelEmbedding1 ∘ raw21812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21812step2 raw21812step2Labels raw21812step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21813 raw21813Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21813 raw21813Labels = mixedMoment B raw21813step0 raw21813step0Labels := by
      have hz : ∀ j, raw21813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21813step0 = (fun i j => raw21813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21813step0 raw21813; decide +kernel
      have hl : raw21813step0Labels = raw21813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21813 raw21813Labels permutation265 hz
    mixedMoment B raw21813step0 raw21813step0Labels = mixedMoment B raw21813step1 raw21813step1Labels := by
      have ha : raw21813step1 = (fun i j => raw21813step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21813step1 raw21813step0; decide +kernel
      have hl : raw21813step1Labels = raw21813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21813step0 raw21813step0Labels permutation38 permutation7
    mixedMoment B raw21813step1 raw21813step1Labels = mixedMoment B raw21813step2 raw21813step2Labels := by
      have ha : raw21813step2 = -raw21813step1 := by apply Matrix.ext; change ∀ i j, raw21813step2 i j = -(raw21813step1 i j); unfold raw21813step2 raw21813step1; decide +kernel
      have hl : raw21813step2Labels = raw21813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21813step2 raw21813step2Labels = mixedMoment B raw21813step3 raw21813step3Labels := by
      have ha : raw21813step3 = raw21813step2 := by apply Matrix.ext; unfold raw21813step3 raw21813step2; decide +kernel
      have hl : raw21813step2Labels = labelEmbedding1 ∘ raw21813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21813step2 raw21813step2Labels raw21813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21814 raw21814Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21814 raw21814Labels = mixedMoment B raw21814step0 raw21814step0Labels := by
      have hz : ∀ j, raw21814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21814step0 = (fun i j => raw21814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21814step0 raw21814; decide +kernel
      have hl : raw21814step0Labels = raw21814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21814 raw21814Labels permutation434 hz
    mixedMoment B raw21814step0 raw21814step0Labels = mixedMoment B raw21814step1 raw21814step1Labels := by
      have hz : ∀ j, raw21814step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21814step1 = (fun i j => raw21814step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21814step1 raw21814step0; decide +kernel
      have hl : raw21814step1Labels = raw21814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21814step0 raw21814step0Labels permutation56 hz
    mixedMoment B raw21814step1 raw21814step1Labels = mixedMoment B raw21814step2 raw21814step2Labels := by
      have ha : raw21814step2 = (fun i j => raw21814step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21814step2 raw21814step1; decide +kernel
      have hl : raw21814step2Labels = raw21814step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21814step1 raw21814step1Labels permutation8 permutation7
    mixedMoment B raw21814step2 raw21814step2Labels = mixedMoment B raw21814step3 raw21814step3Labels := by
      have ha : raw21814step3 = -raw21814step2 := by apply Matrix.ext; change ∀ i j, raw21814step3 i j = -(raw21814step2 i j); unfold raw21814step3 raw21814step2; decide +kernel
      have hl : raw21814step3Labels = raw21814step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21814step3 raw21814step3Labels = mixedMoment B raw21814step4 raw21814step4Labels := by
      have ha : raw21814step4 = raw21814step3 := by apply Matrix.ext; unfold raw21814step4 raw21814step3; decide +kernel
      have hl : raw21814step3Labels = labelEmbedding1 ∘ raw21814step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21814step3 raw21814step3Labels raw21814step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21815 raw21815Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21815 raw21815Labels = mixedMoment B raw21815step0 raw21815step0Labels := by
      have hz : ∀ j, raw21815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21815step0 = (fun i j => raw21815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21815step0 raw21815; decide +kernel
      have hl : raw21815step0Labels = raw21815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21815 raw21815Labels permutation434 hz
    mixedMoment B raw21815step0 raw21815step0Labels = mixedMoment B raw21815step1 raw21815step1Labels := by
      have hz : ∀ j, raw21815step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21815step1 = (fun i j => raw21815step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21815step1 raw21815step0; decide +kernel
      have hl : raw21815step1Labels = raw21815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21815step0 raw21815step0Labels permutation56 hz
    mixedMoment B raw21815step1 raw21815step1Labels = mixedMoment B raw21815step2 raw21815step2Labels := by
      have ha : raw21815step2 = (fun i j => raw21815step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21815step2 raw21815step1; decide +kernel
      have hl : raw21815step2Labels = raw21815step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21815step1 raw21815step1Labels permutation8 permutation7
    mixedMoment B raw21815step2 raw21815step2Labels = mixedMoment B raw21815step3 raw21815step3Labels := by
      have ha : raw21815step3 = -raw21815step2 := by apply Matrix.ext; change ∀ i j, raw21815step3 i j = -(raw21815step2 i j); unfold raw21815step3 raw21815step2; decide +kernel
      have hl : raw21815step3Labels = raw21815step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21815step3 raw21815step3Labels = mixedMoment B raw21815step4 raw21815step4Labels := by
      have ha : raw21815step4 = raw21815step3 := by apply Matrix.ext; unfold raw21815step4 raw21815step3; decide +kernel
      have hl : raw21815step3Labels = labelEmbedding1 ∘ raw21815step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21815step3 raw21815step3Labels raw21815step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical21816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21816 raw21816Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21816 raw21816Labels = mixedMoment B raw21816step0 raw21816step0Labels := by
      have hz : ∀ j, raw21816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21816step0 = (fun i j => raw21816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21816step0 raw21816; decide +kernel
      have hl : raw21816step0Labels = raw21816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21816 raw21816Labels permutation346 hz
    mixedMoment B raw21816step0 raw21816step0Labels = mixedMoment B raw21816step1 raw21816step1Labels := by
      have hz : ∀ j, raw21816step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21816step1 = (fun i j => raw21816step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21816step1 raw21816step0; decide +kernel
      have hl : raw21816step1Labels = raw21816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21816step0 raw21816step0Labels permutation56 hz
    mixedMoment B raw21816step1 raw21816step1Labels = mixedMoment B raw21816step2 raw21816step2Labels := by
      have ha : raw21816step2 = (fun i j => raw21816step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21816step2 raw21816step1; decide +kernel
      have hl : raw21816step2Labels = raw21816step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21816step1 raw21816step1Labels permutation8 permutation7
    mixedMoment B raw21816step2 raw21816step2Labels = mixedMoment B raw21816step3 raw21816step3Labels := by
      have ha : raw21816step3 = -raw21816step2 := by apply Matrix.ext; change ∀ i j, raw21816step3 i j = -(raw21816step2 i j); unfold raw21816step3 raw21816step2; decide +kernel
      have hl : raw21816step3Labels = raw21816step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21816step3 raw21816step3Labels = mixedMoment B raw21816step4 raw21816step4Labels := by
      have ha : raw21816step4 = raw21816step3 := by apply Matrix.ext; unfold raw21816step4 raw21816step3; decide +kernel
      have hl : raw21816step3Labels = labelEmbedding1 ∘ raw21816step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21816step3 raw21816step3Labels raw21816step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical21817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21817 raw21817Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21817 raw21817Labels = mixedMoment B raw21817step0 raw21817step0Labels := by
      have hz : ∀ j, raw21817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21817step0 = (fun i j => raw21817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21817step0 raw21817; decide +kernel
      have hl : raw21817step0Labels = raw21817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21817 raw21817Labels permutation346 hz
    mixedMoment B raw21817step0 raw21817step0Labels = mixedMoment B raw21817step1 raw21817step1Labels := by
      have ha : raw21817step1 = (fun i j => raw21817step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21817step1 raw21817step0; decide +kernel
      have hl : raw21817step1Labels = raw21817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21817step0 raw21817step0Labels permutation32 permutation7
    mixedMoment B raw21817step1 raw21817step1Labels = mixedMoment B raw21817step2 raw21817step2Labels := by
      have ha : raw21817step2 = -raw21817step1 := by apply Matrix.ext; change ∀ i j, raw21817step2 i j = -(raw21817step1 i j); unfold raw21817step2 raw21817step1; decide +kernel
      have hl : raw21817step2Labels = raw21817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21817step2 raw21817step2Labels = mixedMoment B raw21817step3 raw21817step3Labels := by
      have ha : raw21817step3 = raw21817step2 := by apply Matrix.ext; unfold raw21817step3 raw21817step2; decide +kernel
      have hl : raw21817step2Labels = labelEmbedding1 ∘ raw21817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21817step2 raw21817step2Labels raw21817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21818 raw21818Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21818 raw21818Labels = mixedMoment B raw21818step0 raw21818step0Labels := by
      have hz : ∀ j, raw21818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21818step0 = (fun i j => raw21818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21818step0 raw21818; decide +kernel
      have hl : raw21818step0Labels = raw21818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21818 raw21818Labels permutation265 hz
    mixedMoment B raw21818step0 raw21818step0Labels = mixedMoment B raw21818step1 raw21818step1Labels := by
      have ha : raw21818step1 = (fun i j => raw21818step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21818step1 raw21818step0; decide +kernel
      have hl : raw21818step1Labels = raw21818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21818step0 raw21818step0Labels permutation32 permutation7
    mixedMoment B raw21818step1 raw21818step1Labels = mixedMoment B raw21818step2 raw21818step2Labels := by
      have ha : raw21818step2 = -raw21818step1 := by apply Matrix.ext; change ∀ i j, raw21818step2 i j = -(raw21818step1 i j); unfold raw21818step2 raw21818step1; decide +kernel
      have hl : raw21818step2Labels = raw21818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21818step2 raw21818step2Labels = mixedMoment B raw21818step3 raw21818step3Labels := by
      have ha : raw21818step3 = raw21818step2 := by apply Matrix.ext; unfold raw21818step3 raw21818step2; decide +kernel
      have hl : raw21818step2Labels = labelEmbedding1 ∘ raw21818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21818step2 raw21818step2Labels raw21818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21819 raw21819Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21819 raw21819Labels = mixedMoment B raw21819step0 raw21819step0Labels := by
      have hz : ∀ j, raw21819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21819step0 = (fun i j => raw21819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21819step0 raw21819; decide +kernel
      have hl : raw21819step0Labels = raw21819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21819 raw21819Labels permutation346 hz
    mixedMoment B raw21819step0 raw21819step0Labels = mixedMoment B raw21819step1 raw21819step1Labels := by
      have hz : ∀ j, raw21819step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21819step1 = (fun i j => raw21819step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21819step1 raw21819step0; decide +kernel
      have hl : raw21819step1Labels = raw21819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21819step0 raw21819step0Labels permutation56 hz
    mixedMoment B raw21819step1 raw21819step1Labels = mixedMoment B raw21819step2 raw21819step2Labels := by
      have ha : raw21819step2 = (fun i j => raw21819step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21819step2 raw21819step1; decide +kernel
      have hl : raw21819step2Labels = raw21819step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21819step1 raw21819step1Labels permutation8 permutation7
    mixedMoment B raw21819step2 raw21819step2Labels = mixedMoment B raw21819step3 raw21819step3Labels := by
      have ha : raw21819step3 = -raw21819step2 := by apply Matrix.ext; change ∀ i j, raw21819step3 i j = -(raw21819step2 i j); unfold raw21819step3 raw21819step2; decide +kernel
      have hl : raw21819step3Labels = raw21819step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21819step3 raw21819step3Labels = mixedMoment B raw21819step4 raw21819step4Labels := by
      have ha : raw21819step4 = raw21819step3 := by apply Matrix.ext; unfold raw21819step4 raw21819step3; decide +kernel
      have hl : raw21819step3Labels = labelEmbedding1 ∘ raw21819step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21819step3 raw21819step3Labels raw21819step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21820 raw21820Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21820 raw21820Labels = mixedMoment B raw21820step0 raw21820step0Labels := by
      have hz : ∀ j, raw21820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21820step0 = (fun i j => raw21820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21820step0 raw21820; decide +kernel
      have hl : raw21820step0Labels = raw21820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21820 raw21820Labels permutation346 hz
    mixedMoment B raw21820step0 raw21820step0Labels = mixedMoment B raw21820step1 raw21820step1Labels := by
      have hz : ∀ j, raw21820step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21820step1 = (fun i j => raw21820step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21820step1 raw21820step0; decide +kernel
      have hl : raw21820step1Labels = raw21820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21820step0 raw21820step0Labels permutation56 hz
    mixedMoment B raw21820step1 raw21820step1Labels = mixedMoment B raw21820step2 raw21820step2Labels := by
      have ha : raw21820step2 = (fun i j => raw21820step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21820step2 raw21820step1; decide +kernel
      have hl : raw21820step2Labels = raw21820step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21820step1 raw21820step1Labels permutation8 permutation7
    mixedMoment B raw21820step2 raw21820step2Labels = mixedMoment B raw21820step3 raw21820step3Labels := by
      have ha : raw21820step3 = -raw21820step2 := by apply Matrix.ext; change ∀ i j, raw21820step3 i j = -(raw21820step2 i j); unfold raw21820step3 raw21820step2; decide +kernel
      have hl : raw21820step3Labels = raw21820step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21820step3 raw21820step3Labels = mixedMoment B raw21820step4 raw21820step4Labels := by
      have ha : raw21820step4 = raw21820step3 := by apply Matrix.ext; unfold raw21820step4 raw21820step3; decide +kernel
      have hl : raw21820step3Labels = labelEmbedding1 ∘ raw21820step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21820step3 raw21820step3Labels raw21820step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical21821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21821 raw21821Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw21821 raw21821Labels = mixedMoment B raw21821step0 raw21821step0Labels := by
      have hz : ∀ j, raw21821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21821step0 = (fun i j => raw21821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21821step0 raw21821; decide +kernel
      have hl : raw21821step0Labels = raw21821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821 raw21821Labels permutation434 hz
    mixedMoment B raw21821step0 raw21821step0Labels = mixedMoment B raw21821step1 raw21821step1Labels := by
      have hz : ∀ j, raw21821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21821step1 = (fun i j => raw21821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21821step1 raw21821step0; decide +kernel
      have hl : raw21821step1Labels = raw21821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821step0 raw21821step0Labels permutation80 hz
    mixedMoment B raw21821step1 raw21821step1Labels = mixedMoment B raw21821step2 raw21821step2Labels := by
      have hz : ∀ j, raw21821step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21821step2 = (fun i j => raw21821step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21821step2 raw21821step1; decide +kernel
      have hl : raw21821step2Labels = raw21821step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821step1 raw21821step1Labels permutation14 hz
    mixedMoment B raw21821step2 raw21821step2Labels = mixedMoment B raw21821step3 raw21821step3Labels := by
      have ha : raw21821step3 = (fun i j => raw21821step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21821step3 raw21821step2; decide +kernel
      have hl : raw21821step3Labels = raw21821step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21821step2 raw21821step2Labels permutation2 permutation7
    mixedMoment B raw21821step3 raw21821step3Labels = mixedMoment B raw21821step4 raw21821step4Labels := by
      have ha : raw21821step4 = -raw21821step3 := by apply Matrix.ext; change ∀ i j, raw21821step4 i j = -(raw21821step3 i j); unfold raw21821step4 raw21821step3; decide +kernel
      have hl : raw21821step4Labels = raw21821step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21821step4 raw21821step4Labels = mixedMoment B raw21821step5 raw21821step5Labels := by
      have ha : raw21821step5 = raw21821step4 := by apply Matrix.ext; unfold raw21821step5 raw21821step4; decide +kernel
      have hl : raw21821step4Labels = labelEmbedding1 ∘ raw21821step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21821step4 raw21821step4Labels raw21821step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

theorem canonical21822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21822 raw21822Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21822 raw21822Labels = mixedMoment B raw21822step0 raw21822step0Labels := by
      have hz : ∀ j, raw21822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21822step0 = (fun i j => raw21822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21822step0 raw21822; decide +kernel
      have hl : raw21822step0Labels = raw21822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21822 raw21822Labels permutation434 hz
    mixedMoment B raw21822step0 raw21822step0Labels = mixedMoment B raw21822step1 raw21822step1Labels := by
      have hz : ∀ j, raw21822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21822step1 = (fun i j => raw21822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21822step1 raw21822step0; decide +kernel
      have hl : raw21822step1Labels = raw21822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21822step0 raw21822step0Labels permutation80 hz
    mixedMoment B raw21822step1 raw21822step1Labels = mixedMoment B raw21822step2 raw21822step2Labels := by
      have ha : raw21822step2 = (fun i j => raw21822step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21822step2 raw21822step1; decide +kernel
      have hl : raw21822step2Labels = raw21822step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21822step1 raw21822step1Labels permutation8 permutation7
    mixedMoment B raw21822step2 raw21822step2Labels = mixedMoment B raw21822step3 raw21822step3Labels := by
      have ha : raw21822step3 = -raw21822step2 := by apply Matrix.ext; change ∀ i j, raw21822step3 i j = -(raw21822step2 i j); unfold raw21822step3 raw21822step2; decide +kernel
      have hl : raw21822step3Labels = raw21822step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21822step3 raw21822step3Labels = mixedMoment B raw21822step4 raw21822step4Labels := by
      have ha : raw21822step4 = raw21822step3 := by apply Matrix.ext; unfold raw21822step4 raw21822step3; decide +kernel
      have hl : raw21822step3Labels = labelEmbedding1 ∘ raw21822step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21822step3 raw21822step3Labels raw21822step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical21823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21823 raw21823Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21823 raw21823Labels = mixedMoment B raw21823step0 raw21823step0Labels := by
      have hz : ∀ j, raw21823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21823step0 = (fun i j => raw21823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21823step0 raw21823; decide +kernel
      have hl : raw21823step0Labels = raw21823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21823 raw21823Labels permutation434 hz
    mixedMoment B raw21823step0 raw21823step0Labels = mixedMoment B raw21823step1 raw21823step1Labels := by
      have hz : ∀ j, raw21823step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21823step1 = (fun i j => raw21823step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21823step1 raw21823step0; decide +kernel
      have hl : raw21823step1Labels = raw21823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21823step0 raw21823step0Labels permutation56 hz
    mixedMoment B raw21823step1 raw21823step1Labels = mixedMoment B raw21823step2 raw21823step2Labels := by
      have ha : raw21823step2 = (fun i j => raw21823step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21823step2 raw21823step1; decide +kernel
      have hl : raw21823step2Labels = raw21823step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21823step1 raw21823step1Labels permutation8 permutation7
    mixedMoment B raw21823step2 raw21823step2Labels = mixedMoment B raw21823step3 raw21823step3Labels := by
      have ha : raw21823step3 = -raw21823step2 := by apply Matrix.ext; change ∀ i j, raw21823step3 i j = -(raw21823step2 i j); unfold raw21823step3 raw21823step2; decide +kernel
      have hl : raw21823step3Labels = raw21823step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21823step3 raw21823step3Labels = mixedMoment B raw21823step4 raw21823step4Labels := by
      have ha : raw21823step4 = raw21823step3 := by apply Matrix.ext; unfold raw21823step4 raw21823step3; decide +kernel
      have hl : raw21823step3Labels = labelEmbedding1 ∘ raw21823step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21823step3 raw21823step3Labels raw21823step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical21824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21824 raw21824Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21824 raw21824Labels = mixedMoment B raw21824step0 raw21824step0Labels := by
      have hz : ∀ j, raw21824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21824step0 = (fun i j => raw21824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21824step0 raw21824; decide +kernel
      have hl : raw21824step0Labels = raw21824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21824 raw21824Labels permutation346 hz
    mixedMoment B raw21824step0 raw21824step0Labels = mixedMoment B raw21824step1 raw21824step1Labels := by
      have hz : ∀ j, raw21824step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21824step1 = (fun i j => raw21824step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21824step1 raw21824step0; decide +kernel
      have hl : raw21824step1Labels = raw21824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21824step0 raw21824step0Labels permutation56 hz
    mixedMoment B raw21824step1 raw21824step1Labels = mixedMoment B raw21824step2 raw21824step2Labels := by
      have ha : raw21824step2 = (fun i j => raw21824step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21824step2 raw21824step1; decide +kernel
      have hl : raw21824step2Labels = raw21824step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21824step1 raw21824step1Labels permutation8 permutation7
    mixedMoment B raw21824step2 raw21824step2Labels = mixedMoment B raw21824step3 raw21824step3Labels := by
      have ha : raw21824step3 = -raw21824step2 := by apply Matrix.ext; change ∀ i j, raw21824step3 i j = -(raw21824step2 i j); unfold raw21824step3 raw21824step2; decide +kernel
      have hl : raw21824step3Labels = raw21824step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21824step3 raw21824step3Labels = mixedMoment B raw21824step4 raw21824step4Labels := by
      have ha : raw21824step4 = raw21824step3 := by apply Matrix.ext; unfold raw21824step4 raw21824step3; decide +kernel
      have hl : raw21824step3Labels = labelEmbedding1 ∘ raw21824step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21824step3 raw21824step3Labels raw21824step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical21825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21825 raw21825Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw21825 raw21825Labels = mixedMoment B raw21825step0 raw21825step0Labels := by
      have hz : ∀ j, raw21825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21825step0 = (fun i j => raw21825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21825step0 raw21825; decide +kernel
      have hl : raw21825step0Labels = raw21825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825 raw21825Labels permutation434 hz
    mixedMoment B raw21825step0 raw21825step0Labels = mixedMoment B raw21825step1 raw21825step1Labels := by
      have hz : ∀ j, raw21825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21825step1 = (fun i j => raw21825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21825step1 raw21825step0; decide +kernel
      have hl : raw21825step1Labels = raw21825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825step0 raw21825step0Labels permutation80 hz
    mixedMoment B raw21825step1 raw21825step1Labels = mixedMoment B raw21825step2 raw21825step2Labels := by
      have hz : ∀ j, raw21825step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21825step2 = (fun i j => raw21825step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21825step2 raw21825step1; decide +kernel
      have hl : raw21825step2Labels = raw21825step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825step1 raw21825step1Labels permutation14 hz
    mixedMoment B raw21825step2 raw21825step2Labels = mixedMoment B raw21825step3 raw21825step3Labels := by
      have ha : raw21825step3 = (fun i j => raw21825step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21825step3 raw21825step2; decide +kernel
      have hl : raw21825step3Labels = raw21825step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21825step2 raw21825step2Labels permutation2 permutation7
    mixedMoment B raw21825step3 raw21825step3Labels = mixedMoment B raw21825step4 raw21825step4Labels := by
      have ha : raw21825step4 = -raw21825step3 := by apply Matrix.ext; change ∀ i j, raw21825step4 i j = -(raw21825step3 i j); unfold raw21825step4 raw21825step3; decide +kernel
      have hl : raw21825step4Labels = raw21825step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21825step4 raw21825step4Labels = mixedMoment B raw21825step5 raw21825step5Labels := by
      have ha : raw21825step5 = raw21825step4 := by apply Matrix.ext; unfold raw21825step5 raw21825step4; decide +kernel
      have hl : raw21825step4Labels = labelEmbedding1 ∘ raw21825step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21825step4 raw21825step4Labels raw21825step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

theorem canonical21826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21826 raw21826Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw21826 raw21826Labels = mixedMoment B raw21826step0 raw21826step0Labels := by
      have hz : ∀ j, raw21826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21826step0 = (fun i j => raw21826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21826step0 raw21826; decide +kernel
      have hl : raw21826step0Labels = raw21826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826 raw21826Labels permutation434 hz
    mixedMoment B raw21826step0 raw21826step0Labels = mixedMoment B raw21826step1 raw21826step1Labels := by
      have hz : ∀ j, raw21826step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21826step1 = (fun i j => raw21826step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21826step1 raw21826step0; decide +kernel
      have hl : raw21826step1Labels = raw21826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826step0 raw21826step0Labels permutation80 hz
    mixedMoment B raw21826step1 raw21826step1Labels = mixedMoment B raw21826step2 raw21826step2Labels := by
      have hz : ∀ j, raw21826step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21826step2 = (fun i j => raw21826step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21826step2 raw21826step1; decide +kernel
      have hl : raw21826step2Labels = raw21826step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826step1 raw21826step1Labels permutation14 hz
    mixedMoment B raw21826step2 raw21826step2Labels = mixedMoment B raw21826step3 raw21826step3Labels := by
      have ha : raw21826step3 = (fun i j => raw21826step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21826step3 raw21826step2; decide +kernel
      have hl : raw21826step3Labels = raw21826step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21826step2 raw21826step2Labels permutation2 permutation7
    mixedMoment B raw21826step3 raw21826step3Labels = mixedMoment B raw21826step4 raw21826step4Labels := by
      have ha : raw21826step4 = -raw21826step3 := by apply Matrix.ext; change ∀ i j, raw21826step4 i j = -(raw21826step3 i j); unfold raw21826step4 raw21826step3; decide +kernel
      have hl : raw21826step4Labels = raw21826step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21826step4 raw21826step4Labels = mixedMoment B raw21826step5 raw21826step5Labels := by
      have ha : raw21826step5 = raw21826step4 := by apply Matrix.ext; unfold raw21826step5 raw21826step4; decide +kernel
      have hl : raw21826step4Labels = labelEmbedding1 ∘ raw21826step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21826step4 raw21826step4Labels raw21826step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

theorem canonical21827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21827 raw21827Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21827 raw21827Labels = mixedMoment B raw21827step0 raw21827step0Labels := by
      have hz : ∀ j, raw21827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21827step0 = (fun i j => raw21827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21827step0 raw21827; decide +kernel
      have hl : raw21827step0Labels = raw21827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21827 raw21827Labels permutation434 hz
    mixedMoment B raw21827step0 raw21827step0Labels = mixedMoment B raw21827step1 raw21827step1Labels := by
      have hz : ∀ j, raw21827step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21827step1 = (fun i j => raw21827step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21827step1 raw21827step0; decide +kernel
      have hl : raw21827step1Labels = raw21827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21827step0 raw21827step0Labels permutation80 hz
    mixedMoment B raw21827step1 raw21827step1Labels = mixedMoment B raw21827step2 raw21827step2Labels := by
      have ha : raw21827step2 = (fun i j => raw21827step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21827step2 raw21827step1; decide +kernel
      have hl : raw21827step2Labels = raw21827step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21827step1 raw21827step1Labels permutation8 permutation7
    mixedMoment B raw21827step2 raw21827step2Labels = mixedMoment B raw21827step3 raw21827step3Labels := by
      have ha : raw21827step3 = -raw21827step2 := by apply Matrix.ext; change ∀ i j, raw21827step3 i j = -(raw21827step2 i j); unfold raw21827step3 raw21827step2; decide +kernel
      have hl : raw21827step3Labels = raw21827step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21827step3 raw21827step3Labels = mixedMoment B raw21827step4 raw21827step4Labels := by
      have ha : raw21827step4 = raw21827step3 := by apply Matrix.ext; unfold raw21827step4 raw21827step3; decide +kernel
      have hl : raw21827step3Labels = labelEmbedding1 ∘ raw21827step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21827step3 raw21827step3Labels raw21827step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical21828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21828 raw21828Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21828 raw21828Labels = mixedMoment B raw21828step0 raw21828step0Labels := by
      have hz : ∀ j, raw21828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21828step0 = (fun i j => raw21828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21828step0 raw21828; decide +kernel
      have hl : raw21828step0Labels = raw21828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21828 raw21828Labels permutation434 hz
    mixedMoment B raw21828step0 raw21828step0Labels = mixedMoment B raw21828step1 raw21828step1Labels := by
      have hz : ∀ j, raw21828step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21828step1 = (fun i j => raw21828step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21828step1 raw21828step0; decide +kernel
      have hl : raw21828step1Labels = raw21828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21828step0 raw21828step0Labels permutation56 hz
    mixedMoment B raw21828step1 raw21828step1Labels = mixedMoment B raw21828step2 raw21828step2Labels := by
      have ha : raw21828step2 = (fun i j => raw21828step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21828step2 raw21828step1; decide +kernel
      have hl : raw21828step2Labels = raw21828step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21828step1 raw21828step1Labels permutation8 permutation7
    mixedMoment B raw21828step2 raw21828step2Labels = mixedMoment B raw21828step3 raw21828step3Labels := by
      have ha : raw21828step3 = -raw21828step2 := by apply Matrix.ext; change ∀ i j, raw21828step3 i j = -(raw21828step2 i j); unfold raw21828step3 raw21828step2; decide +kernel
      have hl : raw21828step3Labels = raw21828step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21828step3 raw21828step3Labels = mixedMoment B raw21828step4 raw21828step4Labels := by
      have ha : raw21828step4 = raw21828step3 := by apply Matrix.ext; unfold raw21828step4 raw21828step3; decide +kernel
      have hl : raw21828step3Labels = labelEmbedding1 ∘ raw21828step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21828step3 raw21828step3Labels raw21828step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical21829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21829 raw21829Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21829 raw21829Labels = mixedMoment B raw21829step0 raw21829step0Labels := by
      have hz : ∀ j, raw21829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21829step0 = (fun i j => raw21829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21829step0 raw21829; decide +kernel
      have hl : raw21829step0Labels = raw21829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21829 raw21829Labels permutation346 hz
    mixedMoment B raw21829step0 raw21829step0Labels = mixedMoment B raw21829step1 raw21829step1Labels := by
      have hz : ∀ j, raw21829step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21829step1 = (fun i j => raw21829step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21829step1 raw21829step0; decide +kernel
      have hl : raw21829step1Labels = raw21829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21829step0 raw21829step0Labels permutation56 hz
    mixedMoment B raw21829step1 raw21829step1Labels = mixedMoment B raw21829step2 raw21829step2Labels := by
      have ha : raw21829step2 = (fun i j => raw21829step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21829step2 raw21829step1; decide +kernel
      have hl : raw21829step2Labels = raw21829step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21829step1 raw21829step1Labels permutation8 permutation7
    mixedMoment B raw21829step2 raw21829step2Labels = mixedMoment B raw21829step3 raw21829step3Labels := by
      have ha : raw21829step3 = -raw21829step2 := by apply Matrix.ext; change ∀ i j, raw21829step3 i j = -(raw21829step2 i j); unfold raw21829step3 raw21829step2; decide +kernel
      have hl : raw21829step3Labels = raw21829step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21829step3 raw21829step3Labels = mixedMoment B raw21829step4 raw21829step4Labels := by
      have ha : raw21829step4 = raw21829step3 := by apply Matrix.ext; unfold raw21829step4 raw21829step3; decide +kernel
      have hl : raw21829step3Labels = labelEmbedding1 ∘ raw21829step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21829step3 raw21829step3Labels raw21829step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical21830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21830 raw21830Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw21830 raw21830Labels = mixedMoment B raw21830step0 raw21830step0Labels := by
      have hz : ∀ j, raw21830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21830step0 = (fun i j => raw21830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21830step0 raw21830; decide +kernel
      have hl : raw21830step0Labels = raw21830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830 raw21830Labels permutation434 hz
    mixedMoment B raw21830step0 raw21830step0Labels = mixedMoment B raw21830step1 raw21830step1Labels := by
      have hz : ∀ j, raw21830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21830step1 = (fun i j => raw21830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21830step1 raw21830step0; decide +kernel
      have hl : raw21830step1Labels = raw21830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830step0 raw21830step0Labels permutation80 hz
    mixedMoment B raw21830step1 raw21830step1Labels = mixedMoment B raw21830step2 raw21830step2Labels := by
      have hz : ∀ j, raw21830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21830step2 = (fun i j => raw21830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21830step2 raw21830step1; decide +kernel
      have hl : raw21830step2Labels = raw21830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830step1 raw21830step1Labels permutation14 hz
    mixedMoment B raw21830step2 raw21830step2Labels = mixedMoment B raw21830step3 raw21830step3Labels := by
      have ha : raw21830step3 = (fun i j => raw21830step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21830step3 raw21830step2; decide +kernel
      have hl : raw21830step3Labels = raw21830step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21830step2 raw21830step2Labels permutation2 permutation7
    mixedMoment B raw21830step3 raw21830step3Labels = mixedMoment B raw21830step4 raw21830step4Labels := by
      have ha : raw21830step4 = -raw21830step3 := by apply Matrix.ext; change ∀ i j, raw21830step4 i j = -(raw21830step3 i j); unfold raw21830step4 raw21830step3; decide +kernel
      have hl : raw21830step4Labels = raw21830step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21830step4 raw21830step4Labels = mixedMoment B raw21830step5 raw21830step5Labels := by
      have ha : raw21830step5 = raw21830step4 := by apply Matrix.ext; unfold raw21830step5 raw21830step4; decide +kernel
      have hl : raw21830step4Labels = labelEmbedding1 ∘ raw21830step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21830step4 raw21830step4Labels raw21830step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical21853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21853 raw21853Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21853 raw21853Labels = mixedMoment B raw21853step0 raw21853step0Labels := by
      have hz : ∀ j, raw21853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21853step0 = (fun i j => raw21853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21853step0 raw21853; decide +kernel
      have hl : raw21853step0Labels = raw21853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853 raw21853Labels permutation434 hz
    mixedMoment B raw21853step0 raw21853step0Labels = mixedMoment B raw21853step1 raw21853step1Labels := by
      have hz : ∀ j, raw21853step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21853step1 = (fun i j => raw21853step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21853step1 raw21853step0; decide +kernel
      have hl : raw21853step1Labels = raw21853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853step0 raw21853step0Labels permutation80 hz
    mixedMoment B raw21853step1 raw21853step1Labels = mixedMoment B raw21853step2 raw21853step2Labels := by
      have ha : raw21853step2 = (fun i j => raw21853step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21853step2 raw21853step1; decide +kernel
      have hl : raw21853step2Labels = raw21853step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21853step1 raw21853step1Labels permutation31 permutation7
    mixedMoment B raw21853step2 raw21853step2Labels = mixedMoment B raw21853step3 raw21853step3Labels := by
      have ha : raw21853step3 = raw21853step2 := by apply Matrix.ext; unfold raw21853step3 raw21853step2; decide +kernel
      have hl : raw21853step2Labels = labelEmbedding1 ∘ raw21853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21853step2 raw21853step2Labels raw21853step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21854 raw21854Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21854 raw21854Labels = mixedMoment B raw21854step0 raw21854step0Labels := by
      have hz : ∀ j, raw21854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21854step0 = (fun i j => raw21854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21854step0 raw21854; decide +kernel
      have hl : raw21854step0Labels = raw21854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854 raw21854Labels permutation434 hz
    mixedMoment B raw21854step0 raw21854step0Labels = mixedMoment B raw21854step1 raw21854step1Labels := by
      have hz : ∀ j, raw21854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21854step1 = (fun i j => raw21854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21854step1 raw21854step0; decide +kernel
      have hl : raw21854step1Labels = raw21854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854step0 raw21854step0Labels permutation56 hz
    mixedMoment B raw21854step1 raw21854step1Labels = mixedMoment B raw21854step2 raw21854step2Labels := by
      have ha : raw21854step2 = (fun i j => raw21854step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21854step2 raw21854step1; decide +kernel
      have hl : raw21854step2Labels = raw21854step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21854step1 raw21854step1Labels permutation31 permutation7
    mixedMoment B raw21854step2 raw21854step2Labels = mixedMoment B raw21854step3 raw21854step3Labels := by
      have ha : raw21854step3 = raw21854step2 := by apply Matrix.ext; unfold raw21854step3 raw21854step2; decide +kernel
      have hl : raw21854step2Labels = labelEmbedding1 ∘ raw21854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21854step2 raw21854step2Labels raw21854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21855 raw21855Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21855 raw21855Labels = mixedMoment B raw21855step0 raw21855step0Labels := by
      have hz : ∀ j, raw21855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21855step0 = (fun i j => raw21855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21855step0 raw21855; decide +kernel
      have hl : raw21855step0Labels = raw21855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855 raw21855Labels permutation346 hz
    mixedMoment B raw21855step0 raw21855step0Labels = mixedMoment B raw21855step1 raw21855step1Labels := by
      have hz : ∀ j, raw21855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21855step1 = (fun i j => raw21855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21855step1 raw21855step0; decide +kernel
      have hl : raw21855step1Labels = raw21855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855step0 raw21855step0Labels permutation56 hz
    mixedMoment B raw21855step1 raw21855step1Labels = mixedMoment B raw21855step2 raw21855step2Labels := by
      have ha : raw21855step2 = (fun i j => raw21855step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21855step2 raw21855step1; decide +kernel
      have hl : raw21855step2Labels = raw21855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21855step1 raw21855step1Labels permutation31 permutation7
    mixedMoment B raw21855step2 raw21855step2Labels = mixedMoment B raw21855step3 raw21855step3Labels := by
      have ha : raw21855step3 = raw21855step2 := by apply Matrix.ext; unfold raw21855step3 raw21855step2; decide +kernel
      have hl : raw21855step2Labels = labelEmbedding1 ∘ raw21855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21855step2 raw21855step2Labels raw21855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical21856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21856 raw21856Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw21856 raw21856Labels = mixedMoment B raw21856step0 raw21856step0Labels := by
      have hz : ∀ j, raw21856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21856step0 = (fun i j => raw21856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21856step0 raw21856; decide +kernel
      have hl : raw21856step0Labels = raw21856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856 raw21856Labels permutation434 hz
    mixedMoment B raw21856step0 raw21856step0Labels = mixedMoment B raw21856step1 raw21856step1Labels := by
      have hz : ∀ j, raw21856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21856step1 = (fun i j => raw21856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21856step1 raw21856step0; decide +kernel
      have hl : raw21856step1Labels = raw21856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step0 raw21856step0Labels permutation80 hz
    mixedMoment B raw21856step1 raw21856step1Labels = mixedMoment B raw21856step2 raw21856step2Labels := by
      have hz : ∀ j, raw21856step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21856step2 = (fun i j => raw21856step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21856step2 raw21856step1; decide +kernel
      have hl : raw21856step2Labels = raw21856step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step1 raw21856step1Labels permutation14 hz
    mixedMoment B raw21856step2 raw21856step2Labels = mixedMoment B raw21856step3 raw21856step3Labels := by
      have ha : raw21856step3 = (fun i j => raw21856step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21856step3 raw21856step2; decide +kernel
      have hl : raw21856step3Labels = raw21856step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21856step2 raw21856step2Labels permutation2 permutation7
    mixedMoment B raw21856step3 raw21856step3Labels = mixedMoment B raw21856step4 raw21856step4Labels := by
      have ha : raw21856step4 = -raw21856step3 := by apply Matrix.ext; change ∀ i j, raw21856step4 i j = -(raw21856step3 i j); unfold raw21856step4 raw21856step3; decide +kernel
      have hl : raw21856step4Labels = raw21856step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21856step4 raw21856step4Labels = mixedMoment B raw21856step5 raw21856step5Labels := by
      have ha : raw21856step5 = raw21856step4 := by apply Matrix.ext; unfold raw21856step5 raw21856step4; decide +kernel
      have hl : raw21856step4Labels = labelEmbedding1 ∘ raw21856step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21856step4 raw21856step4Labels raw21856step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

theorem canonical21857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21857 raw21857Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21857 raw21857Labels = mixedMoment B raw21857step0 raw21857step0Labels := by
      have hz : ∀ j, raw21857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21857step0 = (fun i j => raw21857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21857step0 raw21857; decide +kernel
      have hl : raw21857step0Labels = raw21857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21857 raw21857Labels permutation434 hz
    mixedMoment B raw21857step0 raw21857step0Labels = mixedMoment B raw21857step1 raw21857step1Labels := by
      have hz : ∀ j, raw21857step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21857step1 = (fun i j => raw21857step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21857step1 raw21857step0; decide +kernel
      have hl : raw21857step1Labels = raw21857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21857step0 raw21857step0Labels permutation80 hz
    mixedMoment B raw21857step1 raw21857step1Labels = mixedMoment B raw21857step2 raw21857step2Labels := by
      have ha : raw21857step2 = (fun i j => raw21857step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21857step2 raw21857step1; decide +kernel
      have hl : raw21857step2Labels = raw21857step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21857step1 raw21857step1Labels permutation8 permutation7
    mixedMoment B raw21857step2 raw21857step2Labels = mixedMoment B raw21857step3 raw21857step3Labels := by
      have ha : raw21857step3 = -raw21857step2 := by apply Matrix.ext; change ∀ i j, raw21857step3 i j = -(raw21857step2 i j); unfold raw21857step3 raw21857step2; decide +kernel
      have hl : raw21857step3Labels = raw21857step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21857step3 raw21857step3Labels = mixedMoment B raw21857step4 raw21857step4Labels := by
      have ha : raw21857step4 = raw21857step3 := by apply Matrix.ext; unfold raw21857step4 raw21857step3; decide +kernel
      have hl : raw21857step3Labels = labelEmbedding1 ∘ raw21857step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21857step3 raw21857step3Labels raw21857step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical21858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21858 raw21858Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21858 raw21858Labels = mixedMoment B raw21858step0 raw21858step0Labels := by
      have hz : ∀ j, raw21858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21858step0 = (fun i j => raw21858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21858step0 raw21858; decide +kernel
      have hl : raw21858step0Labels = raw21858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21858 raw21858Labels permutation434 hz
    mixedMoment B raw21858step0 raw21858step0Labels = mixedMoment B raw21858step1 raw21858step1Labels := by
      have ha : raw21858step1 = (fun i j => raw21858step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21858step1 raw21858step0; decide +kernel
      have hl : raw21858step1Labels = raw21858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21858step0 raw21858step0Labels permutation38 permutation7
    mixedMoment B raw21858step1 raw21858step1Labels = mixedMoment B raw21858step2 raw21858step2Labels := by
      have ha : raw21858step2 = -raw21858step1 := by apply Matrix.ext; change ∀ i j, raw21858step2 i j = -(raw21858step1 i j); unfold raw21858step2 raw21858step1; decide +kernel
      have hl : raw21858step2Labels = raw21858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21858step2 raw21858step2Labels = mixedMoment B raw21858step3 raw21858step3Labels := by
      have ha : raw21858step3 = raw21858step2 := by apply Matrix.ext; unfold raw21858step3 raw21858step2; decide +kernel
      have hl : raw21858step2Labels = labelEmbedding1 ∘ raw21858step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21858step2 raw21858step2Labels raw21858step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21859 raw21859Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21859 raw21859Labels = mixedMoment B raw21859step0 raw21859step0Labels := by
      have hz : ∀ j, raw21859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21859step0 = (fun i j => raw21859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21859step0 raw21859; decide +kernel
      have hl : raw21859step0Labels = raw21859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21859 raw21859Labels permutation346 hz
    mixedMoment B raw21859step0 raw21859step0Labels = mixedMoment B raw21859step1 raw21859step1Labels := by
      have ha : raw21859step1 = (fun i j => raw21859step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21859step1 raw21859step0; decide +kernel
      have hl : raw21859step1Labels = raw21859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21859step0 raw21859step0Labels permutation38 permutation7
    mixedMoment B raw21859step1 raw21859step1Labels = mixedMoment B raw21859step2 raw21859step2Labels := by
      have ha : raw21859step2 = -raw21859step1 := by apply Matrix.ext; change ∀ i j, raw21859step2 i j = -(raw21859step1 i j); unfold raw21859step2 raw21859step1; decide +kernel
      have hl : raw21859step2Labels = raw21859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21859step2 raw21859step2Labels = mixedMoment B raw21859step3 raw21859step3Labels := by
      have ha : raw21859step3 = raw21859step2 := by apply Matrix.ext; unfold raw21859step3 raw21859step2; decide +kernel
      have hl : raw21859step2Labels = labelEmbedding1 ∘ raw21859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21859step2 raw21859step2Labels raw21859step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21860 raw21860Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21860 raw21860Labels = mixedMoment B raw21860step0 raw21860step0Labels := by
      have hz : ∀ j, raw21860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21860step0 = (fun i j => raw21860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21860step0 raw21860; decide +kernel
      have hl : raw21860step0Labels = raw21860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860 raw21860Labels permutation434 hz
    mixedMoment B raw21860step0 raw21860step0Labels = mixedMoment B raw21860step1 raw21860step1Labels := by
      have hz : ∀ j, raw21860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21860step1 = (fun i j => raw21860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21860step1 raw21860step0; decide +kernel
      have hl : raw21860step1Labels = raw21860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860step0 raw21860step0Labels permutation80 hz
    mixedMoment B raw21860step1 raw21860step1Labels = mixedMoment B raw21860step2 raw21860step2Labels := by
      have ha : raw21860step2 = (fun i j => raw21860step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21860step2 raw21860step1; decide +kernel
      have hl : raw21860step2Labels = raw21860step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21860step1 raw21860step1Labels permutation8 permutation7
    mixedMoment B raw21860step2 raw21860step2Labels = mixedMoment B raw21860step3 raw21860step3Labels := by
      have ha : raw21860step3 = -raw21860step2 := by apply Matrix.ext; change ∀ i j, raw21860step3 i j = -(raw21860step2 i j); unfold raw21860step3 raw21860step2; decide +kernel
      have hl : raw21860step3Labels = raw21860step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21860step3 raw21860step3Labels = mixedMoment B raw21860step4 raw21860step4Labels := by
      have ha : raw21860step4 = raw21860step3 := by apply Matrix.ext; unfold raw21860step4 raw21860step3; decide +kernel
      have hl : raw21860step3Labels = labelEmbedding1 ∘ raw21860step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21860step3 raw21860step3Labels raw21860step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21861 raw21861Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21861 raw21861Labels = mixedMoment B raw21861step0 raw21861step0Labels := by
      have hz : ∀ j, raw21861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21861step0 = (fun i j => raw21861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21861step0 raw21861; decide +kernel
      have hl : raw21861step0Labels = raw21861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21861 raw21861Labels permutation434 hz
    mixedMoment B raw21861step0 raw21861step0Labels = mixedMoment B raw21861step1 raw21861step1Labels := by
      have hz : ∀ j, raw21861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21861step1 = (fun i j => raw21861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21861step1 raw21861step0; decide +kernel
      have hl : raw21861step1Labels = raw21861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21861step0 raw21861step0Labels permutation56 hz
    mixedMoment B raw21861step1 raw21861step1Labels = mixedMoment B raw21861step2 raw21861step2Labels := by
      have ha : raw21861step2 = (fun i j => raw21861step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21861step2 raw21861step1; decide +kernel
      have hl : raw21861step2Labels = raw21861step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21861step1 raw21861step1Labels permutation8 permutation7
    mixedMoment B raw21861step2 raw21861step2Labels = mixedMoment B raw21861step3 raw21861step3Labels := by
      have ha : raw21861step3 = -raw21861step2 := by apply Matrix.ext; change ∀ i j, raw21861step3 i j = -(raw21861step2 i j); unfold raw21861step3 raw21861step2; decide +kernel
      have hl : raw21861step3Labels = raw21861step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21861step3 raw21861step3Labels = mixedMoment B raw21861step4 raw21861step4Labels := by
      have ha : raw21861step4 = raw21861step3 := by apply Matrix.ext; unfold raw21861step4 raw21861step3; decide +kernel
      have hl : raw21861step3Labels = labelEmbedding1 ∘ raw21861step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21861step3 raw21861step3Labels raw21861step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical21862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21862 raw21862Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21862 raw21862Labels = mixedMoment B raw21862step0 raw21862step0Labels := by
      have hz : ∀ j, raw21862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21862step0 = (fun i j => raw21862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21862step0 raw21862; decide +kernel
      have hl : raw21862step0Labels = raw21862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21862 raw21862Labels permutation434 hz
    mixedMoment B raw21862step0 raw21862step0Labels = mixedMoment B raw21862step1 raw21862step1Labels := by
      have ha : raw21862step1 = (fun i j => raw21862step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21862step1 raw21862step0; decide +kernel
      have hl : raw21862step1Labels = raw21862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21862step0 raw21862step0Labels permutation32 permutation7
    mixedMoment B raw21862step1 raw21862step1Labels = mixedMoment B raw21862step2 raw21862step2Labels := by
      have ha : raw21862step2 = -raw21862step1 := by apply Matrix.ext; change ∀ i j, raw21862step2 i j = -(raw21862step1 i j); unfold raw21862step2 raw21862step1; decide +kernel
      have hl : raw21862step2Labels = raw21862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21862step2 raw21862step2Labels = mixedMoment B raw21862step3 raw21862step3Labels := by
      have ha : raw21862step3 = raw21862step2 := by apply Matrix.ext; unfold raw21862step3 raw21862step2; decide +kernel
      have hl : raw21862step2Labels = labelEmbedding1 ∘ raw21862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21862step2 raw21862step2Labels raw21862step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21863 raw21863Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21863 raw21863Labels = mixedMoment B raw21863step0 raw21863step0Labels := by
      have hz : ∀ j, raw21863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21863step0 = (fun i j => raw21863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21863step0 raw21863; decide +kernel
      have hl : raw21863step0Labels = raw21863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21863 raw21863Labels permutation265 hz
    mixedMoment B raw21863step0 raw21863step0Labels = mixedMoment B raw21863step1 raw21863step1Labels := by
      have ha : raw21863step1 = (fun i j => raw21863step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21863step1 raw21863step0; decide +kernel
      have hl : raw21863step1Labels = raw21863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21863step0 raw21863step0Labels permutation38 permutation7
    mixedMoment B raw21863step1 raw21863step1Labels = mixedMoment B raw21863step2 raw21863step2Labels := by
      have ha : raw21863step2 = -raw21863step1 := by apply Matrix.ext; change ∀ i j, raw21863step2 i j = -(raw21863step1 i j); unfold raw21863step2 raw21863step1; decide +kernel
      have hl : raw21863step2Labels = raw21863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21863step2 raw21863step2Labels = mixedMoment B raw21863step3 raw21863step3Labels := by
      have ha : raw21863step3 = raw21863step2 := by apply Matrix.ext; unfold raw21863step3 raw21863step2; decide +kernel
      have hl : raw21863step2Labels = labelEmbedding1 ∘ raw21863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21863step2 raw21863step2Labels raw21863step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21864 raw21864Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21864 raw21864Labels = mixedMoment B raw21864step0 raw21864step0Labels := by
      have hz : ∀ j, raw21864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21864step0 = (fun i j => raw21864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21864step0 raw21864; decide +kernel
      have hl : raw21864step0Labels = raw21864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864 raw21864Labels permutation434 hz
    mixedMoment B raw21864step0 raw21864step0Labels = mixedMoment B raw21864step1 raw21864step1Labels := by
      have hz : ∀ j, raw21864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21864step1 = (fun i j => raw21864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21864step1 raw21864step0; decide +kernel
      have hl : raw21864step1Labels = raw21864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864step0 raw21864step0Labels permutation56 hz
    mixedMoment B raw21864step1 raw21864step1Labels = mixedMoment B raw21864step2 raw21864step2Labels := by
      have ha : raw21864step2 = (fun i j => raw21864step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21864step2 raw21864step1; decide +kernel
      have hl : raw21864step2Labels = raw21864step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21864step1 raw21864step1Labels permutation8 permutation7
    mixedMoment B raw21864step2 raw21864step2Labels = mixedMoment B raw21864step3 raw21864step3Labels := by
      have ha : raw21864step3 = -raw21864step2 := by apply Matrix.ext; change ∀ i j, raw21864step3 i j = -(raw21864step2 i j); unfold raw21864step3 raw21864step2; decide +kernel
      have hl : raw21864step3Labels = raw21864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21864step3 raw21864step3Labels = mixedMoment B raw21864step4 raw21864step4Labels := by
      have ha : raw21864step4 = raw21864step3 := by apply Matrix.ext; unfold raw21864step4 raw21864step3; decide +kernel
      have hl : raw21864step3Labels = labelEmbedding1 ∘ raw21864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21864step3 raw21864step3Labels raw21864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21865 raw21865Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21865 raw21865Labels = mixedMoment B raw21865step0 raw21865step0Labels := by
      have hz : ∀ j, raw21865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21865step0 = (fun i j => raw21865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21865step0 raw21865; decide +kernel
      have hl : raw21865step0Labels = raw21865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865 raw21865Labels permutation346 hz
    mixedMoment B raw21865step0 raw21865step0Labels = mixedMoment B raw21865step1 raw21865step1Labels := by
      have hz : ∀ j, raw21865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21865step1 = (fun i j => raw21865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21865step1 raw21865step0; decide +kernel
      have hl : raw21865step1Labels = raw21865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865step0 raw21865step0Labels permutation56 hz
    mixedMoment B raw21865step1 raw21865step1Labels = mixedMoment B raw21865step2 raw21865step2Labels := by
      have ha : raw21865step2 = (fun i j => raw21865step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21865step2 raw21865step1; decide +kernel
      have hl : raw21865step2Labels = raw21865step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21865step1 raw21865step1Labels permutation8 permutation7
    mixedMoment B raw21865step2 raw21865step2Labels = mixedMoment B raw21865step3 raw21865step3Labels := by
      have ha : raw21865step3 = -raw21865step2 := by apply Matrix.ext; change ∀ i j, raw21865step3 i j = -(raw21865step2 i j); unfold raw21865step3 raw21865step2; decide +kernel
      have hl : raw21865step3Labels = raw21865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21865step3 raw21865step3Labels = mixedMoment B raw21865step4 raw21865step4Labels := by
      have ha : raw21865step4 = raw21865step3 := by apply Matrix.ext; unfold raw21865step4 raw21865step3; decide +kernel
      have hl : raw21865step3Labels = labelEmbedding1 ∘ raw21865step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21865step3 raw21865step3Labels raw21865step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical21866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21866 raw21866Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21866 raw21866Labels = mixedMoment B raw21866step0 raw21866step0Labels := by
      have hz : ∀ j, raw21866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21866step0 = (fun i j => raw21866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21866step0 raw21866; decide +kernel
      have hl : raw21866step0Labels = raw21866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21866 raw21866Labels permutation346 hz
    mixedMoment B raw21866step0 raw21866step0Labels = mixedMoment B raw21866step1 raw21866step1Labels := by
      have ha : raw21866step1 = (fun i j => raw21866step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21866step1 raw21866step0; decide +kernel
      have hl : raw21866step1Labels = raw21866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21866step0 raw21866step0Labels permutation32 permutation7
    mixedMoment B raw21866step1 raw21866step1Labels = mixedMoment B raw21866step2 raw21866step2Labels := by
      have ha : raw21866step2 = -raw21866step1 := by apply Matrix.ext; change ∀ i j, raw21866step2 i j = -(raw21866step1 i j); unfold raw21866step2 raw21866step1; decide +kernel
      have hl : raw21866step2Labels = raw21866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21866step2 raw21866step2Labels = mixedMoment B raw21866step3 raw21866step3Labels := by
      have ha : raw21866step3 = raw21866step2 := by apply Matrix.ext; unfold raw21866step3 raw21866step2; decide +kernel
      have hl : raw21866step2Labels = labelEmbedding1 ∘ raw21866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21866step2 raw21866step2Labels raw21866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21867 raw21867Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21867 raw21867Labels = mixedMoment B raw21867step0 raw21867step0Labels := by
      have hz : ∀ j, raw21867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21867step0 = (fun i j => raw21867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21867step0 raw21867; decide +kernel
      have hl : raw21867step0Labels = raw21867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21867 raw21867Labels permutation265 hz
    mixedMoment B raw21867step0 raw21867step0Labels = mixedMoment B raw21867step1 raw21867step1Labels := by
      have ha : raw21867step1 = (fun i j => raw21867step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21867step1 raw21867step0; decide +kernel
      have hl : raw21867step1Labels = raw21867step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21867step0 raw21867step0Labels permutation32 permutation7
    mixedMoment B raw21867step1 raw21867step1Labels = mixedMoment B raw21867step2 raw21867step2Labels := by
      have ha : raw21867step2 = -raw21867step1 := by apply Matrix.ext; change ∀ i j, raw21867step2 i j = -(raw21867step1 i j); unfold raw21867step2 raw21867step1; decide +kernel
      have hl : raw21867step2Labels = raw21867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21867step2 raw21867step2Labels = mixedMoment B raw21867step3 raw21867step3Labels := by
      have ha : raw21867step3 = raw21867step2 := by apply Matrix.ext; unfold raw21867step3 raw21867step2; decide +kernel
      have hl : raw21867step2Labels = labelEmbedding1 ∘ raw21867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21867step2 raw21867step2Labels raw21867step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical21868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21868 raw21868Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21868 raw21868Labels = mixedMoment B raw21868step0 raw21868step0Labels := by
      have hz : ∀ j, raw21868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21868step0 = (fun i j => raw21868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21868step0 raw21868; decide +kernel
      have hl : raw21868step0Labels = raw21868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868 raw21868Labels permutation346 hz
    mixedMoment B raw21868step0 raw21868step0Labels = mixedMoment B raw21868step1 raw21868step1Labels := by
      have hz : ∀ j, raw21868step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21868step1 = (fun i j => raw21868step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21868step1 raw21868step0; decide +kernel
      have hl : raw21868step1Labels = raw21868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868step0 raw21868step0Labels permutation56 hz
    mixedMoment B raw21868step1 raw21868step1Labels = mixedMoment B raw21868step2 raw21868step2Labels := by
      have ha : raw21868step2 = (fun i j => raw21868step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21868step2 raw21868step1; decide +kernel
      have hl : raw21868step2Labels = raw21868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21868step1 raw21868step1Labels permutation8 permutation7
    mixedMoment B raw21868step2 raw21868step2Labels = mixedMoment B raw21868step3 raw21868step3Labels := by
      have ha : raw21868step3 = -raw21868step2 := by apply Matrix.ext; change ∀ i j, raw21868step3 i j = -(raw21868step2 i j); unfold raw21868step3 raw21868step2; decide +kernel
      have hl : raw21868step3Labels = raw21868step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21868step3 raw21868step3Labels = mixedMoment B raw21868step4 raw21868step4Labels := by
      have ha : raw21868step4 = raw21868step3 := by apply Matrix.ext; unfold raw21868step4 raw21868step3; decide +kernel
      have hl : raw21868step3Labels = labelEmbedding1 ∘ raw21868step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21868step3 raw21868step3Labels raw21868step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical21869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21869 raw21869Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw21869 raw21869Labels = mixedMoment B raw21869step0 raw21869step0Labels := by
      have hz : ∀ j, raw21869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21869step0 = (fun i j => raw21869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21869step0 raw21869; decide +kernel
      have hl : raw21869step0Labels = raw21869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869 raw21869Labels permutation434 hz
    mixedMoment B raw21869step0 raw21869step0Labels = mixedMoment B raw21869step1 raw21869step1Labels := by
      have hz : ∀ j, raw21869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21869step1 = (fun i j => raw21869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21869step1 raw21869step0; decide +kernel
      have hl : raw21869step1Labels = raw21869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869step0 raw21869step0Labels permutation80 hz
    mixedMoment B raw21869step1 raw21869step1Labels = mixedMoment B raw21869step2 raw21869step2Labels := by
      have hz : ∀ j, raw21869step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21869step2 = (fun i j => raw21869step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21869step2 raw21869step1; decide +kernel
      have hl : raw21869step2Labels = raw21869step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869step1 raw21869step1Labels permutation14 hz
    mixedMoment B raw21869step2 raw21869step2Labels = mixedMoment B raw21869step3 raw21869step3Labels := by
      have ha : raw21869step3 = (fun i j => raw21869step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21869step3 raw21869step2; decide +kernel
      have hl : raw21869step3Labels = raw21869step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21869step2 raw21869step2Labels permutation2 permutation7
    mixedMoment B raw21869step3 raw21869step3Labels = mixedMoment B raw21869step4 raw21869step4Labels := by
      have ha : raw21869step4 = -raw21869step3 := by apply Matrix.ext; change ∀ i j, raw21869step4 i j = -(raw21869step3 i j); unfold raw21869step4 raw21869step3; decide +kernel
      have hl : raw21869step4Labels = raw21869step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21869step4 raw21869step4Labels = mixedMoment B raw21869step5 raw21869step5Labels := by
      have ha : raw21869step5 = raw21869step4 := by apply Matrix.ext; unfold raw21869step5 raw21869step4; decide +kernel
      have hl : raw21869step4Labels = labelEmbedding1 ∘ raw21869step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21869step4 raw21869step4Labels raw21869step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

theorem canonical21870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21870 raw21870Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21870 raw21870Labels = mixedMoment B raw21870step0 raw21870step0Labels := by
      have hz : ∀ j, raw21870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21870step0 = (fun i j => raw21870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21870step0 raw21870; decide +kernel
      have hl : raw21870step0Labels = raw21870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870 raw21870Labels permutation434 hz
    mixedMoment B raw21870step0 raw21870step0Labels = mixedMoment B raw21870step1 raw21870step1Labels := by
      have hz : ∀ j, raw21870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21870step1 = (fun i j => raw21870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21870step1 raw21870step0; decide +kernel
      have hl : raw21870step1Labels = raw21870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870step0 raw21870step0Labels permutation80 hz
    mixedMoment B raw21870step1 raw21870step1Labels = mixedMoment B raw21870step2 raw21870step2Labels := by
      have ha : raw21870step2 = (fun i j => raw21870step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21870step2 raw21870step1; decide +kernel
      have hl : raw21870step2Labels = raw21870step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21870step1 raw21870step1Labels permutation8 permutation7
    mixedMoment B raw21870step2 raw21870step2Labels = mixedMoment B raw21870step3 raw21870step3Labels := by
      have ha : raw21870step3 = -raw21870step2 := by apply Matrix.ext; change ∀ i j, raw21870step3 i j = -(raw21870step2 i j); unfold raw21870step3 raw21870step2; decide +kernel
      have hl : raw21870step3Labels = raw21870step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21870step3 raw21870step3Labels = mixedMoment B raw21870step4 raw21870step4Labels := by
      have ha : raw21870step4 = raw21870step3 := by apply Matrix.ext; unfold raw21870step4 raw21870step3; decide +kernel
      have hl : raw21870step3Labels = labelEmbedding1 ∘ raw21870step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21870step3 raw21870step3Labels raw21870step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical21871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21871 raw21871Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21871 raw21871Labels = mixedMoment B raw21871step0 raw21871step0Labels := by
      have hz : ∀ j, raw21871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21871step0 = (fun i j => raw21871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21871step0 raw21871; decide +kernel
      have hl : raw21871step0Labels = raw21871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21871 raw21871Labels permutation434 hz
    mixedMoment B raw21871step0 raw21871step0Labels = mixedMoment B raw21871step1 raw21871step1Labels := by
      have hz : ∀ j, raw21871step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21871step1 = (fun i j => raw21871step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21871step1 raw21871step0; decide +kernel
      have hl : raw21871step1Labels = raw21871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21871step0 raw21871step0Labels permutation56 hz
    mixedMoment B raw21871step1 raw21871step1Labels = mixedMoment B raw21871step2 raw21871step2Labels := by
      have ha : raw21871step2 = (fun i j => raw21871step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21871step2 raw21871step1; decide +kernel
      have hl : raw21871step2Labels = raw21871step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21871step1 raw21871step1Labels permutation8 permutation7
    mixedMoment B raw21871step2 raw21871step2Labels = mixedMoment B raw21871step3 raw21871step3Labels := by
      have ha : raw21871step3 = -raw21871step2 := by apply Matrix.ext; change ∀ i j, raw21871step3 i j = -(raw21871step2 i j); unfold raw21871step3 raw21871step2; decide +kernel
      have hl : raw21871step3Labels = raw21871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21871step3 raw21871step3Labels = mixedMoment B raw21871step4 raw21871step4Labels := by
      have ha : raw21871step4 = raw21871step3 := by apply Matrix.ext; unfold raw21871step4 raw21871step3; decide +kernel
      have hl : raw21871step3Labels = labelEmbedding1 ∘ raw21871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21871step3 raw21871step3Labels raw21871step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical21872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21872 raw21872Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21872 raw21872Labels = mixedMoment B raw21872step0 raw21872step0Labels := by
      have hz : ∀ j, raw21872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21872step0 = (fun i j => raw21872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21872step0 raw21872; decide +kernel
      have hl : raw21872step0Labels = raw21872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21872 raw21872Labels permutation346 hz
    mixedMoment B raw21872step0 raw21872step0Labels = mixedMoment B raw21872step1 raw21872step1Labels := by
      have hz : ∀ j, raw21872step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21872step1 = (fun i j => raw21872step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21872step1 raw21872step0; decide +kernel
      have hl : raw21872step1Labels = raw21872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21872step0 raw21872step0Labels permutation56 hz
    mixedMoment B raw21872step1 raw21872step1Labels = mixedMoment B raw21872step2 raw21872step2Labels := by
      have ha : raw21872step2 = (fun i j => raw21872step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21872step2 raw21872step1; decide +kernel
      have hl : raw21872step2Labels = raw21872step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21872step1 raw21872step1Labels permutation8 permutation7
    mixedMoment B raw21872step2 raw21872step2Labels = mixedMoment B raw21872step3 raw21872step3Labels := by
      have ha : raw21872step3 = -raw21872step2 := by apply Matrix.ext; change ∀ i j, raw21872step3 i j = -(raw21872step2 i j); unfold raw21872step3 raw21872step2; decide +kernel
      have hl : raw21872step3Labels = raw21872step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21872step3 raw21872step3Labels = mixedMoment B raw21872step4 raw21872step4Labels := by
      have ha : raw21872step4 = raw21872step3 := by apply Matrix.ext; unfold raw21872step4 raw21872step3; decide +kernel
      have hl : raw21872step3Labels = labelEmbedding1 ∘ raw21872step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21872step3 raw21872step3Labels raw21872step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical21873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21873 raw21873Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw21873 raw21873Labels = mixedMoment B raw21873step0 raw21873step0Labels := by
      have hz : ∀ j, raw21873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21873step0 = (fun i j => raw21873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21873step0 raw21873; decide +kernel
      have hl : raw21873step0Labels = raw21873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873 raw21873Labels permutation434 hz
    mixedMoment B raw21873step0 raw21873step0Labels = mixedMoment B raw21873step1 raw21873step1Labels := by
      have hz : ∀ j, raw21873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21873step1 = (fun i j => raw21873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21873step1 raw21873step0; decide +kernel
      have hl : raw21873step1Labels = raw21873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step0 raw21873step0Labels permutation80 hz
    mixedMoment B raw21873step1 raw21873step1Labels = mixedMoment B raw21873step2 raw21873step2Labels := by
      have hz : ∀ j, raw21873step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21873step2 = (fun i j => raw21873step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21873step2 raw21873step1; decide +kernel
      have hl : raw21873step2Labels = raw21873step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step1 raw21873step1Labels permutation14 hz
    mixedMoment B raw21873step2 raw21873step2Labels = mixedMoment B raw21873step3 raw21873step3Labels := by
      have ha : raw21873step3 = (fun i j => raw21873step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21873step3 raw21873step2; decide +kernel
      have hl : raw21873step3Labels = raw21873step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21873step2 raw21873step2Labels permutation2 permutation7
    mixedMoment B raw21873step3 raw21873step3Labels = mixedMoment B raw21873step4 raw21873step4Labels := by
      have ha : raw21873step4 = -raw21873step3 := by apply Matrix.ext; change ∀ i j, raw21873step4 i j = -(raw21873step3 i j); unfold raw21873step4 raw21873step3; decide +kernel
      have hl : raw21873step4Labels = raw21873step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21873step4 raw21873step4Labels = mixedMoment B raw21873step5 raw21873step5Labels := by
      have ha : raw21873step5 = raw21873step4 := by apply Matrix.ext; unfold raw21873step5 raw21873step4; decide +kernel
      have hl : raw21873step4Labels = labelEmbedding1 ∘ raw21873step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21873step4 raw21873step4Labels raw21873step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical21874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21874 raw21874Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw21874 raw21874Labels = mixedMoment B raw21874step0 raw21874step0Labels := by
      have hz : ∀ j, raw21874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21874step0 = (fun i j => raw21874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21874step0 raw21874; decide +kernel
      have hl : raw21874step0Labels = raw21874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874 raw21874Labels permutation520 hz
    mixedMoment B raw21874step0 raw21874step0Labels = mixedMoment B raw21874step1 raw21874step1Labels := by
      have hz : ∀ j, raw21874step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21874step1 = (fun i j => raw21874step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21874step1 raw21874step0; decide +kernel
      have hl : raw21874step1Labels = raw21874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step0 raw21874step0Labels permutation104 hz
    mixedMoment B raw21874step1 raw21874step1Labels = mixedMoment B raw21874step2 raw21874step2Labels := by
      have hz : ∀ j, raw21874step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21874step2 = (fun i j => raw21874step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21874step2 raw21874step1; decide +kernel
      have hl : raw21874step2Labels = raw21874step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step1 raw21874step1Labels permutation20 hz
    mixedMoment B raw21874step2 raw21874step2Labels = mixedMoment B raw21874step3 raw21874step3Labels := by
      have hz : ∀ j, raw21874step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw21874step3 = (fun i j => raw21874step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw21874step3 raw21874step2; decide +kernel
      have hl : raw21874step3Labels = raw21874step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step2 raw21874step2Labels permutation4 hz
    mixedMoment B raw21874step3 raw21874step3Labels = mixedMoment B raw21874step4 raw21874step4Labels := by
      have ha : raw21874step4 = (fun i j => raw21874step3 (permutation1 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21874step4 raw21874step3; decide +kernel
      have hl : raw21874step4Labels = raw21874step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21874step3 raw21874step3Labels permutation1 permutation7
    mixedMoment B raw21874step4 raw21874step4Labels = mixedMoment B raw21874step5 raw21874step5Labels := by
      have ha : raw21874step5 = raw21874step4 := by apply Matrix.ext; unfold raw21874step5 raw21874step4; decide +kernel
      have hl : raw21874step4Labels = labelEmbedding1 ∘ raw21874step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21874step4 raw21874step4Labels raw21874step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1758 node1758Labels := by rfl

theorem canonical21875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21875 raw21875Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw21875 raw21875Labels = mixedMoment B raw21875step0 raw21875step0Labels := by
      have hz : ∀ j, raw21875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21875step0 = (fun i j => raw21875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21875step0 raw21875; decide +kernel
      have hl : raw21875step0Labels = raw21875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875 raw21875Labels permutation434 hz
    mixedMoment B raw21875step0 raw21875step0Labels = mixedMoment B raw21875step1 raw21875step1Labels := by
      have hz : ∀ j, raw21875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21875step1 = (fun i j => raw21875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21875step1 raw21875step0; decide +kernel
      have hl : raw21875step1Labels = raw21875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step0 raw21875step0Labels permutation80 hz
    mixedMoment B raw21875step1 raw21875step1Labels = mixedMoment B raw21875step2 raw21875step2Labels := by
      have hz : ∀ j, raw21875step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21875step2 = (fun i j => raw21875step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21875step2 raw21875step1; decide +kernel
      have hl : raw21875step2Labels = raw21875step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step1 raw21875step1Labels permutation14 hz
    _ = mixedMoment B node1085 node1085Labels := by rfl

theorem canonical21876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21876 raw21876Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21876 raw21876Labels = mixedMoment B raw21876step0 raw21876step0Labels := by
      have hz : ∀ j, raw21876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21876step0 = (fun i j => raw21876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21876step0 raw21876; decide +kernel
      have hl : raw21876step0Labels = raw21876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876 raw21876Labels permutation434 hz
    mixedMoment B raw21876step0 raw21876step0Labels = mixedMoment B raw21876step1 raw21876step1Labels := by
      have hz : ∀ j, raw21876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21876step1 = (fun i j => raw21876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21876step1 raw21876step0; decide +kernel
      have hl : raw21876step1Labels = raw21876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876step0 raw21876step0Labels permutation80 hz
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical21877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21877 raw21877Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21877 raw21877Labels = mixedMoment B raw21877step0 raw21877step0Labels := by
      have hz : ∀ j, raw21877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21877step0 = (fun i j => raw21877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21877step0 raw21877; decide +kernel
      have hl : raw21877step0Labels = raw21877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21877 raw21877Labels permutation434 hz
    mixedMoment B raw21877step0 raw21877step0Labels = mixedMoment B raw21877step1 raw21877step1Labels := by
      have hz : ∀ j, raw21877step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21877step1 = (fun i j => raw21877step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21877step1 raw21877step0; decide +kernel
      have hl : raw21877step1Labels = raw21877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21877step0 raw21877step0Labels permutation56 hz
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical21878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21878 raw21878Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21878 raw21878Labels = mixedMoment B raw21878step0 raw21878step0Labels := by
      have hz : ∀ j, raw21878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21878step0 = (fun i j => raw21878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21878step0 raw21878; decide +kernel
      have hl : raw21878step0Labels = raw21878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878 raw21878Labels permutation346 hz
    mixedMoment B raw21878step0 raw21878step0Labels = mixedMoment B raw21878step1 raw21878step1Labels := by
      have hz : ∀ j, raw21878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21878step1 = (fun i j => raw21878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21878step1 raw21878step0; decide +kernel
      have hl : raw21878step1Labels = raw21878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878step0 raw21878step0Labels permutation56 hz
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical21879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21879 raw21879Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw21879 raw21879Labels = mixedMoment B raw21879step0 raw21879step0Labels := by
      have hz : ∀ j, raw21879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21879step0 = (fun i j => raw21879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21879step0 raw21879; decide +kernel
      have hl : raw21879step0Labels = raw21879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879 raw21879Labels permutation434 hz
    mixedMoment B raw21879step0 raw21879step0Labels = mixedMoment B raw21879step1 raw21879step1Labels := by
      have hz : ∀ j, raw21879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21879step1 = (fun i j => raw21879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21879step1 raw21879step0; decide +kernel
      have hl : raw21879step1Labels = raw21879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879step0 raw21879step0Labels permutation80 hz
    mixedMoment B raw21879step1 raw21879step1Labels = mixedMoment B raw21879step2 raw21879step2Labels := by
      have hz : ∀ j, raw21879step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21879step2 = (fun i j => raw21879step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21879step2 raw21879step1; decide +kernel
      have hl : raw21879step2Labels = raw21879step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879step1 raw21879step1Labels permutation14 hz
    _ = mixedMoment B node618 node618Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

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

theorem sound698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node698 node698Labels = Sparse.eval nodeValue698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 698) = mixedMoment B node698 node698Labels := rfl
  simpa [nodeValue698, Sparse.eval] using hc.symm

theorem sound701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node701 node701Labels = Sparse.eval nodeValue701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 701) = mixedMoment B node701 node701Labels := rfl
  simpa [nodeValue701, Sparse.eval] using hc.symm

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

theorem zero714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node714 node714Labels = 0 := by
  exact mixedMoment_order_one B hB node714 node714Labels 1
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

theorem sound706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node706 node706Labels = Sparse.eval nodeValue706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 706) = mixedMoment B node706 node706Labels := rfl
  simpa [nodeValue706, Sparse.eval] using hc.symm

theorem sound714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node714 node714Labels = Sparse.eval nodeValue714 (mixedVector B) := by
  simpa only [nodeValue714, Sparse.eval_nil] using zero714 B _hB _hF

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

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
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

theorem sound809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = Sparse.eval nodeValue809 (mixedVector B) := by
  simpa only [nodeValue809, Sparse.eval_nil] using zero809 B _hB _hF

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

theorem zero880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node880 node880Labels = 0 := by
  exact mixedMoment_order_one B hB node880 node880Labels 1
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

theorem sound864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node864 node864Labels = Sparse.eval nodeValue864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 864) = mixedMoment B node864 node864Labels := rfl
  simpa [nodeValue864, Sparse.eval] using hc.symm

theorem sound867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node867 node867Labels = Sparse.eval nodeValue867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 867) = mixedMoment B node867 node867Labels := rfl
  simpa [nodeValue867, Sparse.eval] using hc.symm

theorem sound872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node872 node872Labels = Sparse.eval nodeValue872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 872) = mixedMoment B node872 node872Labels := rfl
  simpa [nodeValue872, Sparse.eval] using hc.symm

theorem sound880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node880 node880Labels = Sparse.eval nodeValue880 (mixedVector B) := by
  simpa only [nodeValue880, Sparse.eval_nil] using zero880 B _hB _hF

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

theorem sound925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node925 node925Labels = Sparse.eval nodeValue925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 925) = mixedMoment B node925 node925Labels := rfl
  simpa [nodeValue925, Sparse.eval] using hc.symm

theorem sound936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node936 node936Labels = Sparse.eval nodeValue936 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 936) = mixedMoment B node936 node936Labels := rfl
  simpa [nodeValue936, Sparse.eval] using hc.symm

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node976 node976Labels = 0 := by
  exact mixedMoment_alpha B hF node976 node976Labels 1 permutation203
    (by decide +kernel)

theorem zero978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node978 node978Labels = 0 := by
  exact mixedMoment_alpha B hF node978 node978Labels 1 permutation202
    (by decide +kernel)

theorem zero1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1004 node1004Labels = 0 := by
  exact mixedMoment_order_one B hB node1004 node1004Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node976 node976Labels = Sparse.eval nodeValue976 (mixedVector B) := by
  simpa only [nodeValue976, Sparse.eval_nil] using zero976 B _hB _hF

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

theorem sound978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node978 node978Labels = Sparse.eval nodeValue978 (mixedVector B) := by
  simpa only [nodeValue978, Sparse.eval_nil] using zero978 B _hB _hF

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

theorem sound982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node982 node982Labels = Sparse.eval nodeValue982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 982) = mixedMoment B node982 node982Labels := rfl
  simpa [nodeValue982, Sparse.eval] using hc.symm

theorem sound983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node983 node983Labels = Sparse.eval nodeValue983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 983) = mixedMoment B node983 node983Labels := rfl
  simpa [nodeValue983, Sparse.eval] using hc.symm

theorem sound984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node984 node984Labels = Sparse.eval nodeValue984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 984) = mixedMoment B node984 node984Labels := rfl
  simpa [nodeValue984, Sparse.eval] using hc.symm

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

theorem sound999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node999 node999Labels = Sparse.eval nodeValue999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 999) = mixedMoment B node999 node999Labels := rfl
  simpa [nodeValue999, Sparse.eval] using hc.symm

theorem sound1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1004 node1004Labels = Sparse.eval nodeValue1004 (mixedVector B) := by
  simpa only [nodeValue1004, Sparse.eval_nil] using zero1004 B _hB _hF

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

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

theorem zero1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = 0 := by
  exact mixedMoment_order_one B hB node1085 node1085Labels 1
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

theorem sound1033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1033 node1033Labels = Sparse.eval nodeValue1033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1033) = mixedMoment B node1033 node1033Labels := rfl
  simpa [nodeValue1033, Sparse.eval] using hc.symm

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1036 node1036Labels = Sparse.eval nodeValue1036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1036) = mixedMoment B node1036 node1036Labels := rfl
  simpa [nodeValue1036, Sparse.eval] using hc.symm

theorem sound1085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = Sparse.eval nodeValue1085 (mixedVector B) := by
  simpa only [nodeValue1085, Sparse.eval_nil] using zero1085 B _hB _hF

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

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1520 node1520Labels = Sparse.eval nodeValue1520 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1520) = mixedMoment B node1520 node1520Labels := rfl
  simpa [nodeValue1520, Sparse.eval] using hc.symm

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

theorem sound1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1527 node1527Labels = Sparse.eval nodeValue1527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1527) = mixedMoment B node1527 node1527Labels := rfl
  simpa [nodeValue1527, Sparse.eval] using hc.symm

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

theorem sound1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1537 node1537Labels = Sparse.eval nodeValue1537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1537) = mixedMoment B node1537 node1537Labels := rfl
  simpa [nodeValue1537, Sparse.eval] using hc.symm

theorem sound1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1538 node1538Labels = Sparse.eval nodeValue1538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1538) = mixedMoment B node1538 node1538Labels := rfl
  simpa [nodeValue1538, Sparse.eval] using hc.symm

theorem sound1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1539 node1539Labels = Sparse.eval nodeValue1539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1539) = mixedMoment B node1539 node1539Labels := rfl
  simpa [nodeValue1539, Sparse.eval] using hc.symm

theorem sound1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1540 node1540Labels = Sparse.eval nodeValue1540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1540) = mixedMoment B node1540 node1540Labels := rfl
  simpa [nodeValue1540, Sparse.eval] using hc.symm

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

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

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1677 node1677Labels = Sparse.eval nodeValue1677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1677) = mixedMoment B node1677 node1677Labels := rfl
  simpa [nodeValue1677, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

theorem sound1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1694 node1694Labels = Sparse.eval nodeValue1694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1694) = mixedMoment B node1694 node1694Labels := rfl
  simpa [nodeValue1694, Sparse.eval] using hc.symm

theorem sound1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1695 node1695Labels = Sparse.eval nodeValue1695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1695) = mixedMoment B node1695 node1695Labels := rfl
  simpa [nodeValue1695, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = 0 := by
  exact mixedMoment_order_one B hB node1730 node1730Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = 0 := by
  exact mixedMoment_order_one B hB node1755 node1755Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1758 node1758Labels = 0 := by
  exact mixedMoment_order_one B hB node1758 node1758Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = Sparse.eval nodeValue1730 (mixedVector B) := by
  simpa only [nodeValue1730, Sparse.eval_nil] using zero1730 B _hB _hF

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = Sparse.eval nodeValue1755 (mixedVector B) := by
  simpa only [nodeValue1755, Sparse.eval_nil] using zero1755 B _hB _hF

theorem sound1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1757 node1757Labels = Sparse.eval nodeValue1757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1757) = mixedMoment B node1757 node1757Labels := rfl
  simpa [nodeValue1757, Sparse.eval] using hc.symm

theorem sound1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1758 node1758Labels = Sparse.eval nodeValue1758 (mixedVector B) := by
  simpa only [nodeValue1758, Sparse.eval_nil] using zero1758 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = 0 := by
  exact mixedMoment_order_one B hB node1911 node1911Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1914 node1914Labels = 0 := by
  exact mixedMoment_order_one B hB node1914 node1914Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = Sparse.eval nodeValue1911 (mixedVector B) := by
  simpa only [nodeValue1911, Sparse.eval_nil] using zero1911 B _hB _hF

theorem sound1914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1914 node1914Labels = Sparse.eval nodeValue1914 (mixedVector B) := by
  simpa only [nodeValue1914, Sparse.eval_nil] using zero1914 B _hB _hF

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

theorem sound1986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1986 node1986Labels = Sparse.eval nodeValue1986 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1986) = mixedMoment B node1986 node1986Labels := rfl
  simpa [nodeValue1986, Sparse.eval] using hc.symm

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

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

theorem zero2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = 0 := by
  exact mixedMoment_order_one B hB node2208 node2208Labels 1
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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem zero2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = 0 := by
  exact mixedMoment_order_one B hB node2268 node2268Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
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

theorem sound2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2268 node2268Labels = Sparse.eval nodeValue2268 (mixedVector B) := by
  simpa only [nodeValue2268, Sparse.eval_nil] using zero2268 B _hB _hF

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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

theorem sound602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node602 node602Labels = Sparse.eval nodeValue602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 602) = mixedMoment B node602 node602Labels := rfl
  simpa [nodeValue602, Sparse.eval] using hc.symm

theorem sound609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node609 node609Labels = Sparse.eval nodeValue609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 609) = mixedMoment B node609 node609Labels := rfl
  simpa [nodeValue609, Sparse.eval] using hc.symm

theorem sound618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node618 node618Labels = Sparse.eval nodeValue618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 618) = mixedMoment B node618 node618Labels := rfl
  simpa [nodeValue618, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1366 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1366 + difference 0 5) (sourceB1366 + difference 5 0) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1366 + difference 0 5) (sourceB1366 + difference 5 0) sourceC1366) = raw21585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21585; decide +kernel
    rw [ha]
    exact (canonical21585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1366 + difference 1 5) (sourceB1366 + difference 5 1) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1366 + difference 1 5) (sourceB1366 + difference 5 1) sourceC1366) = raw21587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21587; decide +kernel
    rw [ha]
    exact (canonical21587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1366 + difference 2 5) (sourceB1366 + difference 5 2) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1366 + difference 2 5) (sourceB1366 + difference 5 2) sourceC1366) = raw21588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21588; decide +kernel
    rw [ha]
    exact (canonical21588 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1366 + difference 3 5) (sourceB1366 + difference 5 3) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1366 + difference 3 5) (sourceB1366 + difference 5 3) sourceC1366) = raw21589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21589; decide +kernel
    rw [ha]
    exact (canonical21589 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1366 + difference 4 5) (sourceB1366 + difference 5 4) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1366 + difference 4 5) (sourceB1366 + difference 5 4) sourceC1366) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1366 + difference 5 5) (sourceB1366 + difference 5 5) sourceC1366) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1366 + difference 5 5) (sourceB1366 + difference 5 5) sourceC1366) = raw21580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1366 sourceB1366 sourceC1366 difference raw21580; decide +kernel
    rw [ha]
    exact (canonical21580 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1366 + sourceB1366) sourceC1366) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1366 + sourceB1366) sourceC1366) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1366 sourceB1366 sourceC1366 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1366 sourceB1366 sourceC1366
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1366, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 0) (sourceB1367 + difference 0 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 0) (sourceB1367 + difference 0 0) sourceC1367) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 1) (sourceB1367 + difference 1 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 1) (sourceB1367 + difference 1 0) sourceC1367) = raw21592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21592; decide +kernel
    rw [ha]
    exact (canonical21592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 2) (sourceB1367 + difference 2 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 2) (sourceB1367 + difference 2 0) sourceC1367) = raw21593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21593; decide +kernel
    rw [ha]
    exact (canonical21593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 3) (sourceB1367 + difference 3 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1914) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 3) (sourceB1367 + difference 3 0) sourceC1367) = raw21594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21594; decide +kernel
    rw [ha]
    exact (canonical21594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 4) (sourceB1367 + difference 4 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 4) (sourceB1367 + difference 4 0) sourceC1367) = raw21595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21595; decide +kernel
    rw [ha]
    exact (canonical21595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1367 + difference 0 5) (sourceB1367 + difference 5 0) sourceC1367) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1367 + difference 0 5) (sourceB1367 + difference 5 0) sourceC1367) = raw21596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1367 sourceB1367 sourceC1367 difference raw21596; decide +kernel
    rw [ha]
    exact (canonical21596 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1367 + sourceB1367) sourceC1367) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1367 + sourceB1367) sourceC1367) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1367 sourceB1367 sourceC1367 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1367 sourceB1367 sourceC1367
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1367, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1370 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1370 + difference 0 5) (sourceB1370 + difference 5 0) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1370 + difference 0 5) (sourceB1370 + difference 5 0) sourceC1370) = raw21596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21596; decide +kernel
    rw [ha]
    exact (canonical21596 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1370 + difference 1 5) (sourceB1370 + difference 5 1) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1370 + difference 1 5) (sourceB1370 + difference 5 1) sourceC1370) = raw21602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21602; decide +kernel
    rw [ha]
    exact (canonical21602 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1370 + difference 2 5) (sourceB1370 + difference 5 2) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1370 + difference 2 5) (sourceB1370 + difference 5 2) sourceC1370) = raw21606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21606; decide +kernel
    rw [ha]
    exact (canonical21606 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1370 + difference 3 5) (sourceB1370 + difference 5 3) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1370 + difference 3 5) (sourceB1370 + difference 5 3) sourceC1370) = raw21607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21607; decide +kernel
    rw [ha]
    exact (canonical21607 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1370 + difference 4 5) (sourceB1370 + difference 5 4) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1370 + difference 4 5) (sourceB1370 + difference 5 4) sourceC1370) = raw21608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21608; decide +kernel
    rw [ha]
    exact (canonical21608 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1370 + difference 5 5) (sourceB1370 + difference 5 5) sourceC1370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1370 + difference 5 5) (sourceB1370 + difference 5 5) sourceC1370) = raw21591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1370 sourceB1370 sourceC1370 difference raw21591; decide +kernel
    rw [ha]
    exact (canonical21591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1370 + sourceB1370) sourceC1370) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1370 + sourceB1370) sourceC1370) = raw21597 := by
      apply Matrix.ext; unfold doubleCharges sourceA1370 sourceB1370 sourceC1370 raw21597; decide +kernel
    rw [ha]
    exact (canonical21597 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1370 sourceB1370 sourceC1370
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1370, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1373 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 0) (sourceB1373 + difference 0 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 0) (sourceB1373 + difference 0 0) sourceC1373) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 1) (sourceB1373 + difference 1 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 1) (sourceB1373 + difference 1 0) sourceC1373) = raw21614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21614; decide +kernel
    rw [ha]
    exact (canonical21614 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 2) (sourceB1373 + difference 2 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1986) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 2) (sourceB1373 + difference 2 0) sourceC1373) = raw21615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21615; decide +kernel
    rw [ha]
    exact (canonical21615 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 3) (sourceB1373 + difference 3 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 3) (sourceB1373 + difference 3 0) sourceC1373) = raw21616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21616; decide +kernel
    rw [ha]
    exact (canonical21616 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 4) (sourceB1373 + difference 4 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 4) (sourceB1373 + difference 4 0) sourceC1373) = raw21617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21617; decide +kernel
    rw [ha]
    exact (canonical21617 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1373 + difference 0 5) (sourceB1373 + difference 5 0) sourceC1373) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1373 + difference 0 5) (sourceB1373 + difference 5 0) sourceC1373) = raw21618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1373 sourceB1373 sourceC1373 difference raw21618; decide +kernel
    rw [ha]
    exact (canonical21618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1373 + sourceB1373) sourceC1373) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1373 + sourceB1373) sourceC1373) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1373 sourceB1373 sourceC1373 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1373 sourceB1373 sourceC1373
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1373, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1375 + difference 0 3) (sourceB1375 + difference 3 0) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1375 + difference 0 3) (sourceB1375 + difference 3 0) sourceC1375) = raw21616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21616; decide +kernel
    rw [ha]
    exact (canonical21616 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1375 + difference 1 3) (sourceB1375 + difference 3 1) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 880) := by
    have ha : (tripleCharges (sourceA1375 + difference 1 3) (sourceB1375 + difference 3 1) sourceC1375) = raw21622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21622; decide +kernel
    rw [ha]
    exact (canonical21622 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1375 + difference 2 3) (sourceB1375 + difference 3 2) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA1375 + difference 2 3) (sourceB1375 + difference 3 2) sourceC1375) = raw21625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21625; decide +kernel
    rw [ha]
    exact (canonical21625 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1375 + difference 3 3) (sourceB1375 + difference 3 3) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1375 + difference 3 3) (sourceB1375 + difference 3 3) sourceC1375) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1375 + difference 4 3) (sourceB1375 + difference 3 4) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA1375 + difference 4 3) (sourceB1375 + difference 3 4) sourceC1375) = raw21626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21626; decide +kernel
    rw [ha]
    exact (canonical21626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1375 + difference 5 3) (sourceB1375 + difference 3 5) sourceC1375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1375 + difference 5 3) (sourceB1375 + difference 3 5) sourceC1375) = raw21627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1375 sourceB1375 sourceC1375 difference raw21627; decide +kernel
    rw [ha]
    exact (canonical21627 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1375 + sourceB1375) sourceC1375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1375 + sourceB1375) sourceC1375) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1375 sourceB1375 sourceC1375 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1375 sourceB1375 sourceC1375
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1375, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1376 + difference 0 5) (sourceB1376 + difference 5 0) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1376 + difference 0 5) (sourceB1376 + difference 5 0) sourceC1376) = raw21618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21618; decide +kernel
    rw [ha]
    exact (canonical21618 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1376 + difference 1 5) (sourceB1376 + difference 5 1) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1376 + difference 1 5) (sourceB1376 + difference 5 1) sourceC1376) = raw21624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21624; decide +kernel
    rw [ha]
    exact (canonical21624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1376 + difference 2 5) (sourceB1376 + difference 5 2) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 976) := by
    have ha : (tripleCharges (sourceA1376 + difference 2 5) (sourceB1376 + difference 5 2) sourceC1376) = raw21628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21628; decide +kernel
    rw [ha]
    exact (canonical21628 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1376 + difference 3 5) (sourceB1376 + difference 5 3) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1376 + difference 3 5) (sourceB1376 + difference 5 3) sourceC1376) = raw21629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21629; decide +kernel
    rw [ha]
    exact (canonical21629 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1376 + difference 4 5) (sourceB1376 + difference 5 4) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1376 + difference 4 5) (sourceB1376 + difference 5 4) sourceC1376) = raw21630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21630; decide +kernel
    rw [ha]
    exact (canonical21630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1376 + difference 5 5) (sourceB1376 + difference 5 5) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1376 + difference 5 5) (sourceB1376 + difference 5 5) sourceC1376) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1376 + sourceB1376) sourceC1376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1376 + sourceB1376) sourceC1376) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1376 sourceB1376 sourceC1376 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1376 sourceB1376 sourceC1376
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1376, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1377 + difference 0 0) (sourceB1377 + difference 0 0) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1377 + difference 0 0) (sourceB1377 + difference 0 0) sourceC1377) = raw20995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw20995; decide +kernel
    rw [ha]
    exact (canonical20995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1377 + difference 1 0) (sourceB1377 + difference 0 1) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1377 + difference 1 0) (sourceB1377 + difference 0 1) sourceC1377) = raw21631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21631; decide +kernel
    rw [ha]
    exact (canonical21631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1377 + difference 2 0) (sourceB1377 + difference 0 2) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 698) := by
    have ha : (tripleCharges (sourceA1377 + difference 2 0) (sourceB1377 + difference 0 2) sourceC1377) = raw21632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21632; decide +kernel
    rw [ha]
    exact (canonical21632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1377 + difference 3 0) (sourceB1377 + difference 0 3) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1377 + difference 3 0) (sourceB1377 + difference 0 3) sourceC1377) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1377 + difference 4 0) (sourceB1377 + difference 0 4) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 714) := by
    have ha : (tripleCharges (sourceA1377 + difference 4 0) (sourceB1377 + difference 0 4) sourceC1377) = raw21612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21612; decide +kernel
    rw [ha]
    exact (canonical21612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1377 + difference 5 0) (sourceB1377 + difference 0 5) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1377 + difference 5 0) (sourceB1377 + difference 0 5) sourceC1377) = raw21633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21633; decide +kernel
    rw [ha]
    exact (canonical21633 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1377 + sourceB1377) sourceC1377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1377 + sourceB1377) sourceC1377) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1377 sourceB1377 sourceC1377 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1377 sourceB1377 sourceC1377
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1377, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1379 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 1) (sourceB1379 + difference 1 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 1) (sourceB1379 + difference 1 0) sourceC1379) = raw21656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21656; decide +kernel
    rw [ha]
    exact (canonical21656 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 2) (sourceB1379 + difference 2 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 2) (sourceB1379 + difference 2 0) sourceC1379) = raw21657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21657; decide +kernel
    rw [ha]
    exact (canonical21657 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 3) (sourceB1379 + difference 3 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 3) (sourceB1379 + difference 3 0) sourceC1379) = raw21658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21658; decide +kernel
    rw [ha]
    exact (canonical21658 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 4) (sourceB1379 + difference 4 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 4) (sourceB1379 + difference 4 0) sourceC1379) = raw21659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21659; decide +kernel
    rw [ha]
    exact (canonical21659 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 5) (sourceB1379 + difference 5 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 5) (sourceB1379 + difference 5 0) sourceC1379) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 0) (sourceB1379 + difference 0 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 0) (sourceB1379 + difference 0 1) sourceC1379) = raw21661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21661; decide +kernel
    rw [ha]
    exact (canonical21661 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 2) (sourceB1379 + difference 2 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 2) (sourceB1379 + difference 2 1) sourceC1379) = raw21662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21662; decide +kernel
    rw [ha]
    exact (canonical21662 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 3) (sourceB1379 + difference 3 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 3) (sourceB1379 + difference 3 1) sourceC1379) = raw21663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21663; decide +kernel
    rw [ha]
    exact (canonical21663 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 4) (sourceB1379 + difference 4 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 4) (sourceB1379 + difference 4 1) sourceC1379) = raw21664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21664; decide +kernel
    rw [ha]
    exact (canonical21664 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 5) (sourceB1379 + difference 5 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 5) (sourceB1379 + difference 5 1) sourceC1379) = raw21665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21665; decide +kernel
    rw [ha]
    exact (canonical21665 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 0) (sourceB1379 + difference 0 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 0) (sourceB1379 + difference 0 2) sourceC1379) = raw21666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21666; decide +kernel
    rw [ha]
    exact (canonical21666 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 1) (sourceB1379 + difference 1 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 1) (sourceB1379 + difference 1 2) sourceC1379) = raw21667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21667; decide +kernel
    rw [ha]
    exact (canonical21667 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 3) (sourceB1379 + difference 3 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 3) (sourceB1379 + difference 3 2) sourceC1379) = raw21668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21668; decide +kernel
    rw [ha]
    exact (canonical21668 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 4) (sourceB1379 + difference 4 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 4) (sourceB1379 + difference 4 2) sourceC1379) = raw21669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21669; decide +kernel
    rw [ha]
    exact (canonical21669 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 5) (sourceB1379 + difference 5 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 5) (sourceB1379 + difference 5 2) sourceC1379) = raw21670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21670; decide +kernel
    rw [ha]
    exact (canonical21670 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 0) (sourceB1379 + difference 0 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 0) (sourceB1379 + difference 0 3) sourceC1379) = raw21671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21671; decide +kernel
    rw [ha]
    exact (canonical21671 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 1) (sourceB1379 + difference 1 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 1) (sourceB1379 + difference 1 3) sourceC1379) = raw21672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21672; decide +kernel
    rw [ha]
    exact (canonical21672 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 2) (sourceB1379 + difference 2 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 2) (sourceB1379 + difference 2 3) sourceC1379) = raw21673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21673; decide +kernel
    rw [ha]
    exact (canonical21673 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 4) (sourceB1379 + difference 4 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 4) (sourceB1379 + difference 4 3) sourceC1379) = raw21674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21674; decide +kernel
    rw [ha]
    exact (canonical21674 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 5) (sourceB1379 + difference 5 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 5) (sourceB1379 + difference 5 3) sourceC1379) = raw21675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21675; decide +kernel
    rw [ha]
    exact (canonical21675 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 0) (sourceB1379 + difference 0 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 0) (sourceB1379 + difference 0 4) sourceC1379) = raw21676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21676; decide +kernel
    rw [ha]
    exact (canonical21676 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 1) (sourceB1379 + difference 1 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 1) (sourceB1379 + difference 1 4) sourceC1379) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 2) (sourceB1379 + difference 2 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 2) (sourceB1379 + difference 2 4) sourceC1379) = raw21678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21678; decide +kernel
    rw [ha]
    exact (canonical21678 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 3) (sourceB1379 + difference 3 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 3) (sourceB1379 + difference 3 4) sourceC1379) = raw21679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21679; decide +kernel
    rw [ha]
    exact (canonical21679 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 5) (sourceB1379 + difference 5 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 5) (sourceB1379 + difference 5 4) sourceC1379) = raw21680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21680; decide +kernel
    rw [ha]
    exact (canonical21680 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 0) (sourceB1379 + difference 0 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 0) (sourceB1379 + difference 0 5) sourceC1379) = raw21681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21681; decide +kernel
    rw [ha]
    exact (canonical21681 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 1) (sourceB1379 + difference 1 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 1) (sourceB1379 + difference 1 5) sourceC1379) = raw21682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21682; decide +kernel
    rw [ha]
    exact (canonical21682 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 2) (sourceB1379 + difference 2 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 2) (sourceB1379 + difference 2 5) sourceC1379) = raw21683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21683; decide +kernel
    rw [ha]
    exact (canonical21683 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 3) (sourceB1379 + difference 3 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 3) (sourceB1379 + difference 3 5) sourceC1379) = raw21684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21684; decide +kernel
    rw [ha]
    exact (canonical21684 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 4) (sourceB1379 + difference 4 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 4) (sourceB1379 + difference 4 5) sourceC1379) = raw21685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21685; decide +kernel
    rw [ha]
    exact (canonical21685 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1379 sourceB1379 sourceC1379
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1379, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1380 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1380 + difference 0 1) (sourceB1380 + difference 1 0) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1380 + difference 0 1) (sourceB1380 + difference 1 0) sourceC1380) = raw21686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21686; decide +kernel
    rw [ha]
    exact (canonical21686 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1380 + difference 1 1) (sourceB1380 + difference 1 1) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1380 + difference 1 1) (sourceB1380 + difference 1 1) sourceC1380) = raw19412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw19412; decide +kernel
    rw [ha]
    exact (canonical19412 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1380 + difference 2 1) (sourceB1380 + difference 1 2) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1380 + difference 2 1) (sourceB1380 + difference 1 2) sourceC1380) = raw21687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21687; decide +kernel
    rw [ha]
    exact (canonical21687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1380 + difference 3 1) (sourceB1380 + difference 1 3) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1380 + difference 3 1) (sourceB1380 + difference 1 3) sourceC1380) = raw21688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21688; decide +kernel
    rw [ha]
    exact (canonical21688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1380 + difference 4 1) (sourceB1380 + difference 1 4) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA1380 + difference 4 1) (sourceB1380 + difference 1 4) sourceC1380) = raw21689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21689; decide +kernel
    rw [ha]
    exact (canonical21689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1380 + difference 5 1) (sourceB1380 + difference 1 5) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1380 + difference 5 1) (sourceB1380 + difference 1 5) sourceC1380) = raw19408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw19408; decide +kernel
    rw [ha]
    exact (canonical19408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1380 + sourceB1380) sourceC1380) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1380 + sourceB1380) sourceC1380) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1380 sourceB1380 sourceC1380 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1380 sourceB1380 sourceC1380
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1380, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 1) (sourceB1386 + difference 1 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 1) (sourceB1386 + difference 1 0) sourceC1386) = raw21801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21801; decide +kernel
    rw [ha]
    exact (canonical21801 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 2) (sourceB1386 + difference 2 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 2) (sourceB1386 + difference 2 0) sourceC1386) = raw21802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21802; decide +kernel
    rw [ha]
    exact (canonical21802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 3) (sourceB1386 + difference 3 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 3) (sourceB1386 + difference 3 0) sourceC1386) = raw21803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21803; decide +kernel
    rw [ha]
    exact (canonical21803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 4) (sourceB1386 + difference 4 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 4) (sourceB1386 + difference 4 0) sourceC1386) = raw21804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21804; decide +kernel
    rw [ha]
    exact (canonical21804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 5) (sourceB1386 + difference 5 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 5) (sourceB1386 + difference 5 0) sourceC1386) = raw21805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21805; decide +kernel
    rw [ha]
    exact (canonical21805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 0) (sourceB1386 + difference 0 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 0) (sourceB1386 + difference 0 1) sourceC1386) = raw21806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21806; decide +kernel
    rw [ha]
    exact (canonical21806 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 2) (sourceB1386 + difference 2 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 2) (sourceB1386 + difference 2 1) sourceC1386) = raw21807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21807; decide +kernel
    rw [ha]
    exact (canonical21807 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 3) (sourceB1386 + difference 3 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 3) (sourceB1386 + difference 3 1) sourceC1386) = raw21808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21808; decide +kernel
    rw [ha]
    exact (canonical21808 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 4) (sourceB1386 + difference 4 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 4) (sourceB1386 + difference 4 1) sourceC1386) = raw21809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21809; decide +kernel
    rw [ha]
    exact (canonical21809 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 5) (sourceB1386 + difference 5 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 5) (sourceB1386 + difference 5 1) sourceC1386) = raw21810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21810; decide +kernel
    rw [ha]
    exact (canonical21810 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 0) (sourceB1386 + difference 0 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 0) (sourceB1386 + difference 0 2) sourceC1386) = raw21811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21811; decide +kernel
    rw [ha]
    exact (canonical21811 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 1) (sourceB1386 + difference 1 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 1) (sourceB1386 + difference 1 2) sourceC1386) = raw21812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21812; decide +kernel
    rw [ha]
    exact (canonical21812 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 3) (sourceB1386 + difference 3 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 3) (sourceB1386 + difference 3 2) sourceC1386) = raw21813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21813; decide +kernel
    rw [ha]
    exact (canonical21813 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 4) (sourceB1386 + difference 4 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 4) (sourceB1386 + difference 4 2) sourceC1386) = raw21814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21814; decide +kernel
    rw [ha]
    exact (canonical21814 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 5) (sourceB1386 + difference 5 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 5) (sourceB1386 + difference 5 2) sourceC1386) = raw21815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21815; decide +kernel
    rw [ha]
    exact (canonical21815 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 0) (sourceB1386 + difference 0 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 0) (sourceB1386 + difference 0 3) sourceC1386) = raw21816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21816; decide +kernel
    rw [ha]
    exact (canonical21816 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 1) (sourceB1386 + difference 1 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 1) (sourceB1386 + difference 1 3) sourceC1386) = raw21817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21817; decide +kernel
    rw [ha]
    exact (canonical21817 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 2) (sourceB1386 + difference 2 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 2) (sourceB1386 + difference 2 3) sourceC1386) = raw21818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21818; decide +kernel
    rw [ha]
    exact (canonical21818 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 4) (sourceB1386 + difference 4 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 4) (sourceB1386 + difference 4 3) sourceC1386) = raw21819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21819; decide +kernel
    rw [ha]
    exact (canonical21819 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 5) (sourceB1386 + difference 5 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 5) (sourceB1386 + difference 5 3) sourceC1386) = raw21820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21820; decide +kernel
    rw [ha]
    exact (canonical21820 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 0) (sourceB1386 + difference 0 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 0) (sourceB1386 + difference 0 4) sourceC1386) = raw21821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21821; decide +kernel
    rw [ha]
    exact (canonical21821 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 1) (sourceB1386 + difference 1 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 1) (sourceB1386 + difference 1 4) sourceC1386) = raw21822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21822; decide +kernel
    rw [ha]
    exact (canonical21822 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 2) (sourceB1386 + difference 2 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 2) (sourceB1386 + difference 2 4) sourceC1386) = raw21823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21823; decide +kernel
    rw [ha]
    exact (canonical21823 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 3) (sourceB1386 + difference 3 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 3) (sourceB1386 + difference 3 4) sourceC1386) = raw21824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21824; decide +kernel
    rw [ha]
    exact (canonical21824 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 5) (sourceB1386 + difference 5 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 5) (sourceB1386 + difference 5 4) sourceC1386) = raw21825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21825; decide +kernel
    rw [ha]
    exact (canonical21825 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 0) (sourceB1386 + difference 0 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 0) (sourceB1386 + difference 0 5) sourceC1386) = raw21826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21826; decide +kernel
    rw [ha]
    exact (canonical21826 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 1) (sourceB1386 + difference 1 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 1) (sourceB1386 + difference 1 5) sourceC1386) = raw21827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21827; decide +kernel
    rw [ha]
    exact (canonical21827 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 2) (sourceB1386 + difference 2 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 2) (sourceB1386 + difference 2 5) sourceC1386) = raw21828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21828; decide +kernel
    rw [ha]
    exact (canonical21828 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 3) (sourceB1386 + difference 3 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 3) (sourceB1386 + difference 3 5) sourceC1386) = raw21829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21829; decide +kernel
    rw [ha]
    exact (canonical21829 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 4) (sourceB1386 + difference 4 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 4) (sourceB1386 + difference 4 5) sourceC1386) = raw21830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21830; decide +kernel
    rw [ha]
    exact (canonical21830 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1386 sourceB1386 sourceC1386
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1386, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 1) (sourceB1388 + difference 1 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 1) (sourceB1388 + difference 1 0) sourceC1388) = raw21853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21853; decide +kernel
    rw [ha]
    exact (canonical21853 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 2) (sourceB1388 + difference 2 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 2) (sourceB1388 + difference 2 0) sourceC1388) = raw21854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21854; decide +kernel
    rw [ha]
    exact (canonical21854 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 3) (sourceB1388 + difference 3 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 3) (sourceB1388 + difference 3 0) sourceC1388) = raw21855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21855; decide +kernel
    rw [ha]
    exact (canonical21855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 4) (sourceB1388 + difference 4 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 4) (sourceB1388 + difference 4 0) sourceC1388) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 5) (sourceB1388 + difference 5 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 5) (sourceB1388 + difference 5 0) sourceC1388) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 0) (sourceB1388 + difference 0 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 0) (sourceB1388 + difference 0 1) sourceC1388) = raw21857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21857; decide +kernel
    rw [ha]
    exact (canonical21857 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 2) (sourceB1388 + difference 2 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 2) (sourceB1388 + difference 2 1) sourceC1388) = raw21858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21858; decide +kernel
    rw [ha]
    exact (canonical21858 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 3) (sourceB1388 + difference 3 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 3) (sourceB1388 + difference 3 1) sourceC1388) = raw21859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21859; decide +kernel
    rw [ha]
    exact (canonical21859 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 4) (sourceB1388 + difference 4 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 4) (sourceB1388 + difference 4 1) sourceC1388) = raw19926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19926; decide +kernel
    rw [ha]
    exact (canonical19926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 5) (sourceB1388 + difference 5 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 5) (sourceB1388 + difference 5 1) sourceC1388) = raw21860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21860; decide +kernel
    rw [ha]
    exact (canonical21860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 0) (sourceB1388 + difference 0 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 0) (sourceB1388 + difference 0 2) sourceC1388) = raw21861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21861; decide +kernel
    rw [ha]
    exact (canonical21861 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 1) (sourceB1388 + difference 1 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 1) (sourceB1388 + difference 1 2) sourceC1388) = raw21862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21862; decide +kernel
    rw [ha]
    exact (canonical21862 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 3) (sourceB1388 + difference 3 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 3) (sourceB1388 + difference 3 2) sourceC1388) = raw21863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21863; decide +kernel
    rw [ha]
    exact (canonical21863 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 4) (sourceB1388 + difference 4 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 4) (sourceB1388 + difference 4 2) sourceC1388) = raw19931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19931; decide +kernel
    rw [ha]
    exact (canonical19931 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 5) (sourceB1388 + difference 5 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 5) (sourceB1388 + difference 5 2) sourceC1388) = raw21864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21864; decide +kernel
    rw [ha]
    exact (canonical21864 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 0) (sourceB1388 + difference 0 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 0) (sourceB1388 + difference 0 3) sourceC1388) = raw21865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21865; decide +kernel
    rw [ha]
    exact (canonical21865 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 1) (sourceB1388 + difference 1 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 1) (sourceB1388 + difference 1 3) sourceC1388) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 2) (sourceB1388 + difference 2 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 2) (sourceB1388 + difference 2 3) sourceC1388) = raw21867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21867; decide +kernel
    rw [ha]
    exact (canonical21867 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 4) (sourceB1388 + difference 4 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 4) (sourceB1388 + difference 4 3) sourceC1388) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 5) (sourceB1388 + difference 5 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 5) (sourceB1388 + difference 5 3) sourceC1388) = raw21868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21868; decide +kernel
    rw [ha]
    exact (canonical21868 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 0) (sourceB1388 + difference 0 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 0) (sourceB1388 + difference 0 4) sourceC1388) = raw21869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21869; decide +kernel
    rw [ha]
    exact (canonical21869 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 1) (sourceB1388 + difference 1 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 1) (sourceB1388 + difference 1 4) sourceC1388) = raw21870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21870; decide +kernel
    rw [ha]
    exact (canonical21870 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 2) (sourceB1388 + difference 2 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 2) (sourceB1388 + difference 2 4) sourceC1388) = raw21871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21871; decide +kernel
    rw [ha]
    exact (canonical21871 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 3) (sourceB1388 + difference 3 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 3) (sourceB1388 + difference 3 4) sourceC1388) = raw21872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21872; decide +kernel
    rw [ha]
    exact (canonical21872 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 5) (sourceB1388 + difference 5 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 5) (sourceB1388 + difference 5 4) sourceC1388) = raw21873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21873; decide +kernel
    rw [ha]
    exact (canonical21873 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 0) (sourceB1388 + difference 0 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 0) (sourceB1388 + difference 0 5) sourceC1388) = raw19937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19937; decide +kernel
    rw [ha]
    exact (canonical19937 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 1) (sourceB1388 + difference 1 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 1) (sourceB1388 + difference 1 5) sourceC1388) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 2) (sourceB1388 + difference 2 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 2) (sourceB1388 + difference 2 5) sourceC1388) = raw19939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19939; decide +kernel
    rw [ha]
    exact (canonical19939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 3) (sourceB1388 + difference 3 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 3) (sourceB1388 + difference 3 5) sourceC1388) = raw19940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19940; decide +kernel
    rw [ha]
    exact (canonical19940 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 4) (sourceB1388 + difference 4 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 4) (sourceB1388 + difference 4 5) sourceC1388) = raw21874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21874; decide +kernel
    rw [ha]
    exact (canonical21874 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1388 sourceB1388 sourceC1388
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1388, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1389 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1389 + difference 0 0) (sourceB1389 + difference 0 0) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1389 + difference 0 0) (sourceB1389 + difference 0 0) sourceC1389) = raw21875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21875; decide +kernel
    rw [ha]
    exact (canonical21875 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1389 + difference 1 0) (sourceB1389 + difference 0 1) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 1 0) (sourceB1389 + difference 0 1) sourceC1389) = raw21876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21876; decide +kernel
    rw [ha]
    exact (canonical21876 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1389 + difference 2 0) (sourceB1389 + difference 0 2) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 2 0) (sourceB1389 + difference 0 2) sourceC1389) = raw21877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21877; decide +kernel
    rw [ha]
    exact (canonical21877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1389 + difference 3 0) (sourceB1389 + difference 0 3) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 3 0) (sourceB1389 + difference 0 3) sourceC1389) = raw21878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21878; decide +kernel
    rw [ha]
    exact (canonical21878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1389 + difference 4 0) (sourceB1389 + difference 0 4) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1389 + difference 4 0) (sourceB1389 + difference 0 4) sourceC1389) = raw21879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21879; decide +kernel
    rw [ha]
    exact (canonical21879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1389 + difference 5 0) (sourceB1389 + difference 0 5) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1389 + difference 5 0) (sourceB1389 + difference 0 5) sourceC1389) = raw19951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw19951; decide +kernel
    rw [ha]
    exact (canonical19951 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1389 + sourceB1389) sourceC1389) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1389 + sourceB1389) sourceC1389) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1389 sourceB1389 sourceC1389 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1389 sourceB1389 sourceC1389
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1389, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1184 : Integer.Sparse.reindex keyMap MixedData.row1184 = numericRow1184 := by decide +kernel

theorem numericCheck1184 (x : Master → ℝ) : Integer.Sparse.eval numericRow1184 x =
    (1 : ℝ) * reducedSource1184 x := by
  norm_num [numericRow1184, reducedSource1184, Integer.Sparse.eval, Sparse.eval, nodeValue978, nodeValue983, nodeValue985, nodeValue1005, nodeValue1036, nodeValue2206, nodeValue4080]

theorem reindexCheck1185 : Integer.Sparse.reindex keyMap MixedData.row1185 = numericRow1185 := by decide +kernel

theorem numericCheck1185 (x : Master → ℝ) : Integer.Sparse.eval numericRow1185 x =
    (1 : ℝ) * reducedSource1185 x := by
  norm_num [numericRow1185, reducedSource1185, Integer.Sparse.eval, Sparse.eval, nodeValue982, nodeValue1914, nodeValue1987, nodeValue2079, nodeValue2193, nodeValue2205, nodeValue4080]

theorem reindexCheck1186 : Integer.Sparse.reindex keyMap MixedData.row1186 = numericRow1186 := by decide +kernel

theorem numericCheck1186 (x : Master → ℝ) : Integer.Sparse.eval numericRow1186 x =
    (1 : ℝ) * reducedSource1186 x := by
  norm_num [numericRow1186, reducedSource1186, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue982, nodeValue985, nodeValue1004, nodeValue1035, nodeValue2205, nodeValue4080]

theorem reindexCheck1187 : Integer.Sparse.reindex keyMap MixedData.row1187 = numericRow1187 := by decide +kernel

theorem numericCheck1187 (x : Master → ℝ) : Integer.Sparse.eval numericRow1187 x =
    (1 : ℝ) * reducedSource1187 x := by
  norm_num [numericRow1187, reducedSource1187, Integer.Sparse.eval, Sparse.eval, nodeValue979, nodeValue1911, nodeValue1986, nodeValue2018, nodeValue2203, nodeValue2208, nodeValue4081]

theorem reindexCheck1188 : Integer.Sparse.reindex keyMap MixedData.row1188 = numericRow1188 := by decide +kernel

theorem numericCheck1188 (x : Master → ℝ) : Integer.Sparse.eval numericRow1188 x =
    (1 : ℝ) * reducedSource1188 x := by
  norm_num [numericRow1188, reducedSource1188, Integer.Sparse.eval, Sparse.eval, nodeValue864, nodeValue867, nodeValue872, nodeValue880, nodeValue979, nodeValue1911, nodeValue4081]

theorem reindexCheck1189 : Integer.Sparse.reindex keyMap MixedData.row1189 = numericRow1189 := by decide +kernel

theorem numericCheck1189 (x : Master → ℝ) : Integer.Sparse.eval numericRow1189 x =
    (1 : ℝ) * reducedSource1189 x := by
  norm_num [numericRow1189, reducedSource1189, Integer.Sparse.eval, Sparse.eval, nodeValue976, nodeValue979, nodeValue984, nodeValue999, nodeValue1033, nodeValue2203, nodeValue4081]

theorem reindexCheck1190 : Integer.Sparse.reindex keyMap MixedData.row1190 = numericRow1190 := by decide +kernel

theorem numericCheck1190 (x : Master → ℝ) : Integer.Sparse.eval numericRow1190 x =
    (1 : ℝ) * reducedSource1190 x := by
  norm_num [numericRow1190, reducedSource1190, Integer.Sparse.eval, Sparse.eval, nodeValue698, nodeValue701, nodeValue706, nodeValue714, nodeValue809, nodeValue1599, nodeValue4070]

theorem reindexCheck1192 : Integer.Sparse.reindex keyMap MixedData.row1192 = numericRow1192 := by decide +kernel

theorem numericCheck1192 (x : Master → ℝ) : Integer.Sparse.eval numericRow1192 x =
    (1 : ℝ) * reducedSource1192 x := by
  norm_num [numericRow1192, reducedSource1192, Integer.Sparse.eval, Sparse.eval, nodeValue1520, nodeValue1539, nodeValue1540, nodeValue1676, nodeValue1694, nodeValue1695, nodeValue1728, nodeValue1729, nodeValue1755, nodeValue1757, nodeValue2230, nodeValue2293, nodeValue2294]

theorem reindexCheck1193 : Integer.Sparse.reindex keyMap MixedData.row1193 = numericRow1193 := by decide +kernel

theorem numericCheck1193 (x : Master → ℝ) : Integer.Sparse.eval numericRow1193 x =
    (1 : ℝ) * reducedSource1193 x := by
  norm_num [numericRow1193, reducedSource1193, Integer.Sparse.eval, Sparse.eval, nodeValue925, nodeValue936, nodeValue939, nodeValue1091, nodeValue2062, nodeValue4084]

theorem reindexCheck1196 : Integer.Sparse.reindex keyMap MixedData.row1196 = numericRow1196 := by decide +kernel

theorem numericCheck1196 (x : Master → ℝ) : Integer.Sparse.eval numericRow1196 x =
    (1 : ℝ) * reducedSource1196 x := by
  norm_num [numericRow1196, reducedSource1196, Integer.Sparse.eval, Sparse.eval, nodeValue1518, nodeValue1537, nodeValue1538, nodeValue1674, nodeValue1692, nodeValue1693, nodeValue1725, nodeValue1727, nodeValue1752, nodeValue1755, nodeValue2228, nodeValue2292, nodeValue4084]

theorem reindexCheck1198 : Integer.Sparse.reindex keyMap MixedData.row1198 = numericRow1198 := by decide +kernel

theorem numericCheck1198 (x : Master → ℝ) : Integer.Sparse.eval numericRow1198 x =
    (1 : ℝ) * reducedSource1198 x := by
  norm_num [numericRow1198, reducedSource1198, Integer.Sparse.eval, Sparse.eval, nodeValue1509, nodeValue1521, nodeValue1527, nodeValue1666, nodeValue1677, nodeValue1683, nodeValue1710, nodeValue1730, nodeValue1741, nodeValue1758, nodeValue2208, nodeValue2268, nodeValue4085]

theorem reindexCheck1199 : Integer.Sparse.reindex keyMap MixedData.row1199 = numericRow1199 := by decide +kernel

theorem numericCheck1199 (x : Master → ℝ) : Integer.Sparse.eval numericRow1199 x =
    (1 : ℝ) * reducedSource1199 x := by
  norm_num [numericRow1199, reducedSource1199, Integer.Sparse.eval, Sparse.eval, nodeValue602, nodeValue609, nodeValue618, nodeValue1085, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1184 (mixedVector B) = 0 := by
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h983 : mixedVector B (Sum.inr 983) = Sparse.eval nodeValue983 (mixedVector B) := by
    change mixedMoment B node983 node983Labels = _
    exact sound983 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1366, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h978, h983, h985, h1005, h1036, h2206, h4080, reducedSource1184] using sourceEq1366 B hB

theorem rowSound1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1184 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1184, numericCheck1184, reducedZero1184 B hB hF, mul_zero]

theorem reducedZero1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1185 (mixedVector B) = 0 := by
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h1987 : mixedVector B (Sum.inr 1987) = Sparse.eval nodeValue1987 (mixedVector B) := by
    change mixedMoment B node1987 node1987Labels = _
    exact sound1987 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1367, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h982, h1914, h1987, h2079, h2193, h2205, h4080, reducedSource1185] using sourceEq1367 B hB

theorem rowSound1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1185 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1185, numericCheck1185, reducedZero1185 B hB hF, mul_zero]

theorem reducedZero1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1186 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1004 : mixedVector B (Sum.inr 1004) = Sparse.eval nodeValue1004 (mixedVector B) := by
    change mixedMoment B node1004 node1004Labels = _
    exact sound1004 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1370, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h982, h985, h1004, h1035, h2205, h4080, reducedSource1186] using sourceEq1370 B hB

theorem rowSound1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1186 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1186, numericCheck1186, reducedZero1186 B hB hF, mul_zero]

theorem reducedZero1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1187 (mixedVector B) = 0 := by
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h1986 : mixedVector B (Sum.inr 1986) = Sparse.eval nodeValue1986 (mixedVector B) := by
    change mixedMoment B node1986 node1986Labels = _
    exact sound1986 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1373, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h979, h1911, h1986, h2018, h2203, h2208, h4081, reducedSource1187] using sourceEq1373 B hB

theorem rowSound1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1187 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1187, numericCheck1187, reducedZero1187 B hB hF, mul_zero]

theorem reducedZero1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1188 (mixedVector B) = 0 := by
  have h864 : mixedVector B (Sum.inr 864) = Sparse.eval nodeValue864 (mixedVector B) := by
    change mixedMoment B node864 node864Labels = _
    exact sound864 B hB hF
  have h867 : mixedVector B (Sum.inr 867) = Sparse.eval nodeValue867 (mixedVector B) := by
    change mixedMoment B node867 node867Labels = _
    exact sound867 B hB hF
  have h872 : mixedVector B (Sum.inr 872) = Sparse.eval nodeValue872 (mixedVector B) := by
    change mixedMoment B node872 node872Labels = _
    exact sound872 B hB hF
  have h880 : mixedVector B (Sum.inr 880) = Sparse.eval nodeValue880 (mixedVector B) := by
    change mixedMoment B node880 node880Labels = _
    exact sound880 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1375, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h864, h867, h872, h880, h979, h1911, h4081, reducedSource1188] using sourceEq1375 B hB

theorem rowSound1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1188 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1188, numericCheck1188, reducedZero1188 B hB hF, mul_zero]

theorem reducedZero1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1189 (mixedVector B) = 0 := by
  have h976 : mixedVector B (Sum.inr 976) = Sparse.eval nodeValue976 (mixedVector B) := by
    change mixedMoment B node976 node976Labels = _
    exact sound976 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h984 : mixedVector B (Sum.inr 984) = Sparse.eval nodeValue984 (mixedVector B) := by
    change mixedMoment B node984 node984Labels = _
    exact sound984 B hB hF
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1376, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h976, h979, h984, h999, h1033, h2203, h4081, reducedSource1189] using sourceEq1376 B hB

theorem rowSound1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1189 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1189, numericCheck1189, reducedZero1189 B hB hF, mul_zero]

theorem reducedZero1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1190 (mixedVector B) = 0 := by
  have h698 : mixedVector B (Sum.inr 698) = Sparse.eval nodeValue698 (mixedVector B) := by
    change mixedMoment B node698 node698Labels = _
    exact sound698 B hB hF
  have h701 : mixedVector B (Sum.inr 701) = Sparse.eval nodeValue701 (mixedVector B) := by
    change mixedMoment B node701 node701Labels = _
    exact sound701 B hB hF
  have h706 : mixedVector B (Sum.inr 706) = Sparse.eval nodeValue706 (mixedVector B) := by
    change mixedMoment B node706 node706Labels = _
    exact sound706 B hB hF
  have h714 : mixedVector B (Sum.inr 714) = Sparse.eval nodeValue714 (mixedVector B) := by
    change mixedMoment B node714 node714Labels = _
    exact sound714 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1377, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h698, h701, h706, h714, h809, h1599, h4070, reducedSource1190] using sourceEq1377 B hB

theorem rowSound1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1190 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1190, numericCheck1190, reducedZero1190 B hB hF, mul_zero]

theorem reducedZero1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1192 (mixedVector B) = 0 := by
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  simpa only [sourceForm1379, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1520, h1539, h1540, h1676, h1694, h1695, h1728, h1729, h1755, h1757, h2230, h2293, h2294, reducedSource1192] using sourceEq1379 B hB

theorem rowSound1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1192 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1192, numericCheck1192, reducedZero1192 B hB hF, mul_zero]

theorem reducedZero1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1193 (mixedVector B) = 0 := by
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1380, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h925, h936, h939, h1091, h2062, h4084, reducedSource1193] using sourceEq1380 B hB

theorem rowSound1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1193 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1193, numericCheck1193, reducedZero1193 B hB hF, mul_zero]

theorem reducedZero1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1196 (mixedVector B) = 0 := by
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1386, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1518, h1537, h1538, h1674, h1692, h1693, h1725, h1727, h1752, h1755, h2228, h2292, h4084, reducedSource1196] using sourceEq1386 B hB

theorem rowSound1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1196 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1196, numericCheck1196, reducedZero1196 B hB hF, mul_zero]

theorem reducedZero1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1198 (mixedVector B) = 0 := by
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1388, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1509, h1521, h1527, h1666, h1677, h1683, h1710, h1730, h1741, h1758, h2208, h2268, h4085, reducedSource1198] using sourceEq1388 B hB

theorem rowSound1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1198 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1198, numericCheck1198, reducedZero1198 B hB hF, mul_zero]

theorem reducedZero1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1199 (mixedVector B) = 0 := by
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1389, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h602, h609, h618, h1085, h4085, reducedSource1199] using sourceEq1389 B hB

theorem rowSound1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1199 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1199, numericCheck1199, reducedZero1199 B hB hF, mul_zero]

theorem sourceRowsAt1184 : MixedData.sourceRows (1184 : Fin 2425) =
    MixedData.row1184 := by decide +kernel

theorem sourceRowsAt1185 : MixedData.sourceRows (1185 : Fin 2425) =
    MixedData.row1185 := by decide +kernel

theorem sourceRowsAt1186 : MixedData.sourceRows (1186 : Fin 2425) =
    MixedData.row1186 := by decide +kernel

theorem sourceRowsAt1187 : MixedData.sourceRows (1187 : Fin 2425) =
    MixedData.row1187 := by decide +kernel

theorem sourceRowsAt1188 : MixedData.sourceRows (1188 : Fin 2425) =
    MixedData.row1188 := by decide +kernel

theorem sourceRowsAt1189 : MixedData.sourceRows (1189 : Fin 2425) =
    MixedData.row1189 := by decide +kernel

theorem sourceRowsAt1190 : MixedData.sourceRows (1190 : Fin 2425) =
    MixedData.row1190 := by decide +kernel

theorem sourceRowsAt1191 : MixedData.sourceRows (1191 : Fin 2425) =
    MixedData.row1191 := by decide +kernel

theorem sourceRowsAt1192 : MixedData.sourceRows (1192 : Fin 2425) =
    MixedData.row1192 := by decide +kernel

theorem sourceRowsAt1193 : MixedData.sourceRows (1193 : Fin 2425) =
    MixedData.row1193 := by decide +kernel

theorem sourceRowsAt1194 : MixedData.sourceRows (1194 : Fin 2425) =
    MixedData.row1194 := by decide +kernel

theorem sourceRowsAt1195 : MixedData.sourceRows (1195 : Fin 2425) =
    MixedData.row1195 := by decide +kernel

theorem sourceRowsAt1196 : MixedData.sourceRows (1196 : Fin 2425) =
    MixedData.row1196 := by decide +kernel

theorem sourceRowsAt1197 : MixedData.sourceRows (1197 : Fin 2425) =
    MixedData.row1197 := by decide +kernel

theorem sourceRowsAt1198 : MixedData.sourceRows (1198 : Fin 2425) =
    MixedData.row1198 := by decide +kernel

theorem sourceRowsAt1199 : MixedData.sourceRows (1199 : Fin 2425) =
    MixedData.row1199 := by decide +kernel

theorem chunkSound74_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 74) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1184 ∨ k.val = 1185 ∨ k.val = 1186 ∨ k.val = 1187 ∨ k.val = 1188 ∨ k.val = 1189 ∨ k.val = 1190 ∨ k.val = 1191 ∨ k.val = 1192 ∨ k.val = 1193 ∨ k.val = 1194 ∨ k.val = 1195 ∨ k.val = 1196 ∨ k.val = 1197 ∨ k.val = 1198 ∨ k.val = 1199 := by omega
  rcases heq with h1184 | h1185 | h1186 | h1187 | h1188 | h1189 | h1190 | h1191 | h1192 | h1193 | h1194 | h1195 | h1196 | h1197 | h1198 | h1199
  · have he : k = (1184 : Fin 2425) := Fin.ext h1184
    subst k
    rw [sourceRowsAt1184]
    exact rowSound1184 B hB hF
  · have he : k = (1185 : Fin 2425) := Fin.ext h1185
    subst k
    rw [sourceRowsAt1185]
    exact rowSound1185 B hB hF
  · have he : k = (1186 : Fin 2425) := Fin.ext h1186
    subst k
    rw [sourceRowsAt1186]
    exact rowSound1186 B hB hF
  · have he : k = (1187 : Fin 2425) := Fin.ext h1187
    subst k
    rw [sourceRowsAt1187]
    exact rowSound1187 B hB hF
  · have he : k = (1188 : Fin 2425) := Fin.ext h1188
    subst k
    rw [sourceRowsAt1188]
    exact rowSound1188 B hB hF
  · have he : k = (1189 : Fin 2425) := Fin.ext h1189
    subst k
    rw [sourceRowsAt1189]
    exact rowSound1189 B hB hF
  · have he : k = (1190 : Fin 2425) := Fin.ext h1190
    subst k
    rw [sourceRowsAt1190]
    exact rowSound1190 B hB hF
  · have he : k = (1191 : Fin 2425) := Fin.ext h1191
    subst k
    rw [sourceRowsAt1191]
    exact rowSound1191_e B hB hF
  · have he : k = (1192 : Fin 2425) := Fin.ext h1192
    subst k
    rw [sourceRowsAt1192]
    exact rowSound1192 B hB hF
  · have he : k = (1193 : Fin 2425) := Fin.ext h1193
    subst k
    rw [sourceRowsAt1193]
    exact rowSound1193 B hB hF
  · have he : k = (1194 : Fin 2425) := Fin.ext h1194
    subst k
    rw [sourceRowsAt1194]
    exact rowSound1194_e B hB hF
  · have he : k = (1195 : Fin 2425) := Fin.ext h1195
    subst k
    rw [sourceRowsAt1195]
    exact rowSound1195_e B hB hF
  · have he : k = (1196 : Fin 2425) := Fin.ext h1196
    subst k
    rw [sourceRowsAt1196]
    exact rowSound1196 B hB hF
  · have he : k = (1197 : Fin 2425) := Fin.ext h1197
    subst k
    rw [sourceRowsAt1197]
    exact rowSound1197_e B hB hF
  · have he : k = (1198 : Fin 2425) := Fin.ext h1198
    subst k
    rw [sourceRowsAt1198]
    exact rowSound1198 B hB hF
  · have he : k = (1199 : Fin 2425) := Fin.ext h1199
    subst k
    rw [sourceRowsAt1199]
    exact rowSound1199 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound74_e_oai
