-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:42:29.555684+00:00
-- url     : https://prove2.me/submissions/fcf593dd-fe8c-444a-b7a4-b9ae3566734a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1952_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1953_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1954_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1956_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1958_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1960_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1963_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1964_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1965_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25026 raw25026Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw25026 raw25026Labels = mixedMoment B raw25026step0 raw25026step0Labels := by
      have ha : raw25026step0 = (fun i j => raw25026 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25026step0 raw25026; decide +kernel
      have hl : raw25026step0Labels = raw25026Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25026 raw25026Labels permutation194 permutation7
    mixedMoment B raw25026step0 raw25026step0Labels = mixedMoment B raw25026step1 raw25026step1Labels := by
      have ha : raw25026step1 = -raw25026step0 := by apply Matrix.ext; change ∀ i j, raw25026step1 i j = -(raw25026step0 i j); unfold raw25026step1 raw25026step0; decide +kernel
      have hl : raw25026step1Labels = raw25026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25026step1 raw25026step1Labels = mixedMoment B raw25026step2 raw25026step2Labels := by
      have ha : raw25026step2 = raw25026step1 := by apply Matrix.ext; unfold raw25026step2 raw25026step1; decide +kernel
      have hl : raw25026step1Labels = labelEmbedding1 ∘ raw25026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25026step1 raw25026step1Labels raw25026step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical25027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25027 raw25027Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25027 raw25027Labels = mixedMoment B raw25027step0 raw25027step0Labels := by
      have hz : ∀ j, raw25027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25027step0 = (fun i j => raw25027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25027step0 raw25027; decide +kernel
      have hl : raw25027step0Labels = raw25027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25027 raw25027Labels permutation346 hz
    mixedMoment B raw25027step0 raw25027step0Labels = mixedMoment B raw25027step1 raw25027step1Labels := by
      have ha : raw25027step1 = (fun i j => raw25027step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25027step1 raw25027step0; decide +kernel
      have hl : raw25027step1Labels = raw25027step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25027step0 raw25027step0Labels permutation50 permutation7
    mixedMoment B raw25027step1 raw25027step1Labels = mixedMoment B raw25027step2 raw25027step2Labels := by
      have ha : raw25027step2 = -raw25027step1 := by apply Matrix.ext; change ∀ i j, raw25027step2 i j = -(raw25027step1 i j); unfold raw25027step2 raw25027step1; decide +kernel
      have hl : raw25027step2Labels = raw25027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25027step2 raw25027step2Labels = mixedMoment B raw25027step3 raw25027step3Labels := by
      have ha : raw25027step3 = raw25027step2 := by apply Matrix.ext; unfold raw25027step3 raw25027step2; decide +kernel
      have hl : raw25027step2Labels = labelEmbedding1 ∘ raw25027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25027step2 raw25027step2Labels raw25027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical25028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25028 raw25028Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25028 raw25028Labels = mixedMoment B raw25028step0 raw25028step0Labels := by
      have hz : ∀ j, raw25028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25028step0 = (fun i j => raw25028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25028step0 raw25028; decide +kernel
      have hl : raw25028step0Labels = raw25028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25028 raw25028Labels permutation346 hz
    mixedMoment B raw25028step0 raw25028step0Labels = mixedMoment B raw25028step1 raw25028step1Labels := by
      have ha : raw25028step1 = (fun i j => raw25028step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25028step1 raw25028step0; decide +kernel
      have hl : raw25028step1Labels = raw25028step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25028step0 raw25028step0Labels permutation51 permutation7
    mixedMoment B raw25028step1 raw25028step1Labels = mixedMoment B raw25028step2 raw25028step2Labels := by
      have ha : raw25028step2 = -raw25028step1 := by apply Matrix.ext; change ∀ i j, raw25028step2 i j = -(raw25028step1 i j); unfold raw25028step2 raw25028step1; decide +kernel
      have hl : raw25028step2Labels = raw25028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25028step2 raw25028step2Labels = mixedMoment B raw25028step3 raw25028step3Labels := by
      have ha : raw25028step3 = raw25028step2 := by apply Matrix.ext; unfold raw25028step3 raw25028step2; decide +kernel
      have hl : raw25028step2Labels = labelEmbedding1 ∘ raw25028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25028step2 raw25028step2Labels raw25028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical25029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25029 raw25029Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25029 raw25029Labels = mixedMoment B raw25029step0 raw25029step0Labels := by
      have hz : ∀ j, raw25029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25029step0 = (fun i j => raw25029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25029step0 raw25029; decide +kernel
      have hl : raw25029step0Labels = raw25029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25029 raw25029Labels permutation346 hz
    mixedMoment B raw25029step0 raw25029step0Labels = mixedMoment B raw25029step1 raw25029step1Labels := by
      have ha : raw25029step1 = (fun i j => raw25029step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25029step1 raw25029step0; decide +kernel
      have hl : raw25029step1Labels = raw25029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25029step0 raw25029step0Labels permutation50 permutation7
    mixedMoment B raw25029step1 raw25029step1Labels = mixedMoment B raw25029step2 raw25029step2Labels := by
      have ha : raw25029step2 = -raw25029step1 := by apply Matrix.ext; change ∀ i j, raw25029step2 i j = -(raw25029step1 i j); unfold raw25029step2 raw25029step1; decide +kernel
      have hl : raw25029step2Labels = raw25029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25029step2 raw25029step2Labels = mixedMoment B raw25029step3 raw25029step3Labels := by
      have ha : raw25029step3 = raw25029step2 := by apply Matrix.ext; unfold raw25029step3 raw25029step2; decide +kernel
      have hl : raw25029step2Labels = labelEmbedding1 ∘ raw25029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25029step2 raw25029step2Labels raw25029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical25036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25036 raw25036Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw25036 raw25036Labels = mixedMoment B raw25036step0 raw25036step0Labels := by
      have ha : raw25036step0 = (fun i j => raw25036 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25036step0 raw25036; decide +kernel
      have hl : raw25036step0Labels = raw25036Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25036 raw25036Labels permutation194 permutation7
    mixedMoment B raw25036step0 raw25036step0Labels = mixedMoment B raw25036step1 raw25036step1Labels := by
      have ha : raw25036step1 = -raw25036step0 := by apply Matrix.ext; change ∀ i j, raw25036step1 i j = -(raw25036step0 i j); unfold raw25036step1 raw25036step0; decide +kernel
      have hl : raw25036step1Labels = raw25036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25036step1 raw25036step1Labels = mixedMoment B raw25036step2 raw25036step2Labels := by
      have ha : raw25036step2 = raw25036step1 := by apply Matrix.ext; unfold raw25036step2 raw25036step1; decide +kernel
      have hl : raw25036step1Labels = labelEmbedding1 ∘ raw25036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25036step1 raw25036step1Labels raw25036step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical25041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25041 raw25041Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25041 raw25041Labels = mixedMoment B raw25041step0 raw25041step0Labels := by
      have hz : ∀ j, raw25041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25041step0 = (fun i j => raw25041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25041step0 raw25041; decide +kernel
      have hl : raw25041step0Labels = raw25041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25041 raw25041Labels permutation346 hz
    mixedMoment B raw25041step0 raw25041step0Labels = mixedMoment B raw25041step1 raw25041step1Labels := by
      have ha : raw25041step1 = (fun i j => raw25041step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25041step1 raw25041step0; decide +kernel
      have hl : raw25041step1Labels = raw25041step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25041step0 raw25041step0Labels permutation51 permutation7
    mixedMoment B raw25041step1 raw25041step1Labels = mixedMoment B raw25041step2 raw25041step2Labels := by
      have ha : raw25041step2 = -raw25041step1 := by apply Matrix.ext; change ∀ i j, raw25041step2 i j = -(raw25041step1 i j); unfold raw25041step2 raw25041step1; decide +kernel
      have hl : raw25041step2Labels = raw25041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25041step2 raw25041step2Labels = mixedMoment B raw25041step3 raw25041step3Labels := by
      have ha : raw25041step3 = raw25041step2 := by apply Matrix.ext; unfold raw25041step3 raw25041step2; decide +kernel
      have hl : raw25041step2Labels = labelEmbedding1 ∘ raw25041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25041step2 raw25041step2Labels raw25041step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25046 raw25046Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25046 raw25046Labels = mixedMoment B raw25046step0 raw25046step0Labels := by
      have hz : ∀ j, raw25046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25046step0 = (fun i j => raw25046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25046step0 raw25046; decide +kernel
      have hl : raw25046step0Labels = raw25046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25046 raw25046Labels permutation346 hz
    mixedMoment B raw25046step0 raw25046step0Labels = mixedMoment B raw25046step1 raw25046step1Labels := by
      have ha : raw25046step1 = (fun i j => raw25046step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25046step1 raw25046step0; decide +kernel
      have hl : raw25046step1Labels = raw25046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25046step0 raw25046step0Labels permutation50 permutation7
    mixedMoment B raw25046step1 raw25046step1Labels = mixedMoment B raw25046step2 raw25046step2Labels := by
      have ha : raw25046step2 = -raw25046step1 := by apply Matrix.ext; change ∀ i j, raw25046step2 i j = -(raw25046step1 i j); unfold raw25046step2 raw25046step1; decide +kernel
      have hl : raw25046step2Labels = raw25046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25046step2 raw25046step2Labels = mixedMoment B raw25046step3 raw25046step3Labels := by
      have ha : raw25046step3 = raw25046step2 := by apply Matrix.ext; unfold raw25046step3 raw25046step2; decide +kernel
      have hl : raw25046step2Labels = labelEmbedding1 ∘ raw25046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25046step2 raw25046step2Labels raw25046step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25051 raw25051Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw25051 raw25051Labels = mixedMoment B raw25051step0 raw25051step0Labels := by
      have hz : ∀ j, raw25051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25051step0 = (fun i j => raw25051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25051step0 raw25051; decide +kernel
      have hl : raw25051step0Labels = raw25051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25051 raw25051Labels permutation346 hz
    mixedMoment B raw25051step0 raw25051step0Labels = mixedMoment B raw25051step1 raw25051step1Labels := by
      have ha : raw25051step1 = (fun i j => raw25051step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25051step1 raw25051step0; decide +kernel
      have hl : raw25051step1Labels = raw25051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25051step0 raw25051step0Labels permutation50 permutation7
    mixedMoment B raw25051step1 raw25051step1Labels = mixedMoment B raw25051step2 raw25051step2Labels := by
      have ha : raw25051step2 = -raw25051step1 := by apply Matrix.ext; change ∀ i j, raw25051step2 i j = -(raw25051step1 i j); unfold raw25051step2 raw25051step1; decide +kernel
      have hl : raw25051step2Labels = raw25051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25051step2 raw25051step2Labels = mixedMoment B raw25051step3 raw25051step3Labels := by
      have ha : raw25051step3 = raw25051step2 := by apply Matrix.ext; unfold raw25051step3 raw25051step2; decide +kernel
      have hl : raw25051step2Labels = labelEmbedding1 ∘ raw25051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25051step2 raw25051step2Labels raw25051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

theorem canonical25061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25061 raw25061Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25061 raw25061Labels = mixedMoment B raw25061step0 raw25061step0Labels := by
      have hz : ∀ j, raw25061 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw25061step0 = (fun i j => raw25061 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw25061step0 raw25061; decide +kernel
      have hl : raw25061step0Labels = raw25061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061 raw25061Labels permutation590 hz
    mixedMoment B raw25061step0 raw25061step0Labels = mixedMoment B raw25061step1 raw25061step1Labels := by
      have hz : ∀ j, raw25061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25061step1 = (fun i j => raw25061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25061step1 raw25061step0; decide +kernel
      have hl : raw25061step1Labels = raw25061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061step0 raw25061step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25062 raw25062Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw25062 raw25062Labels = mixedMoment B raw25062step0 raw25062step0Labels := by
      have hz : ∀ j, raw25062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25062step0 = (fun i j => raw25062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25062step0 raw25062; decide +kernel
      have hl : raw25062step0Labels = raw25062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25062 raw25062Labels permutation346 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25196 raw25196Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25196 raw25196Labels = mixedMoment B raw25196step0 raw25196step0Labels := by
      have ha : raw25196step0 = (fun i j => raw25196 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25196step0 raw25196; decide +kernel
      have hl : raw25196step0Labels = raw25196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25196 raw25196Labels permutation188 permutation7
    mixedMoment B raw25196step0 raw25196step0Labels = mixedMoment B raw25196step1 raw25196step1Labels := by
      have ha : raw25196step1 = -raw25196step0 := by apply Matrix.ext; change ∀ i j, raw25196step1 i j = -(raw25196step0 i j); unfold raw25196step1 raw25196step0; decide +kernel
      have hl : raw25196step1Labels = raw25196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25196step1 raw25196step1Labels = mixedMoment B raw25196step2 raw25196step2Labels := by
      have ha : raw25196step2 = raw25196step1 := by apply Matrix.ext; unfold raw25196step2 raw25196step1; decide +kernel
      have hl : raw25196step1Labels = labelEmbedding1 ∘ raw25196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25196step1 raw25196step1Labels raw25196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical25197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25197 raw25197Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw25197 raw25197Labels = mixedMoment B raw25197step0 raw25197step0Labels := by
      have hz : ∀ j, raw25197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25197step0 = (fun i j => raw25197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25197step0 raw25197; decide +kernel
      have hl : raw25197step0Labels = raw25197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25197 raw25197Labels permutation346 hz
    mixedMoment B raw25197step0 raw25197step0Labels = mixedMoment B raw25197step1 raw25197step1Labels := by
      have ha : raw25197step1 = (fun i j => raw25197step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25197step1 raw25197step0; decide +kernel
      have hl : raw25197step1Labels = raw25197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25197step0 raw25197step0Labels permutation44 permutation7
    mixedMoment B raw25197step1 raw25197step1Labels = mixedMoment B raw25197step2 raw25197step2Labels := by
      have ha : raw25197step2 = -raw25197step1 := by apply Matrix.ext; change ∀ i j, raw25197step2 i j = -(raw25197step1 i j); unfold raw25197step2 raw25197step1; decide +kernel
      have hl : raw25197step2Labels = raw25197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25197step2 raw25197step2Labels = mixedMoment B raw25197step3 raw25197step3Labels := by
      have ha : raw25197step3 = raw25197step2 := by apply Matrix.ext; unfold raw25197step3 raw25197step2; decide +kernel
      have hl : raw25197step2Labels = labelEmbedding1 ∘ raw25197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25197step2 raw25197step2Labels raw25197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical25198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25198 raw25198Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw25198 raw25198Labels = mixedMoment B raw25198step0 raw25198step0Labels := by
      have hz : ∀ j, raw25198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25198step0 = (fun i j => raw25198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25198step0 raw25198; decide +kernel
      have hl : raw25198step0Labels = raw25198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198 raw25198Labels permutation520 hz
    mixedMoment B raw25198step0 raw25198step0Labels = mixedMoment B raw25198step1 raw25198step1Labels := by
      have hz : ∀ j, raw25198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25198step1 = (fun i j => raw25198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25198step1 raw25198step0; decide +kernel
      have hl : raw25198step1Labels = raw25198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198step0 raw25198step0Labels permutation80 hz
    mixedMoment B raw25198step1 raw25198step1Labels = mixedMoment B raw25198step2 raw25198step2Labels := by
      have ha : raw25198step2 = (fun i j => raw25198step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25198step2 raw25198step1; decide +kernel
      have hl : raw25198step2Labels = raw25198step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25198step1 raw25198step1Labels permutation8 permutation7
    mixedMoment B raw25198step2 raw25198step2Labels = mixedMoment B raw25198step3 raw25198step3Labels := by
      have ha : raw25198step3 = -raw25198step2 := by apply Matrix.ext; change ∀ i j, raw25198step3 i j = -(raw25198step2 i j); unfold raw25198step3 raw25198step2; decide +kernel
      have hl : raw25198step3Labels = raw25198step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25198step3 raw25198step3Labels = mixedMoment B raw25198step4 raw25198step4Labels := by
      have ha : raw25198step4 = raw25198step3 := by apply Matrix.ext; unfold raw25198step4 raw25198step3; decide +kernel
      have hl : raw25198step3Labels = labelEmbedding1 ∘ raw25198step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25198step3 raw25198step3Labels raw25198step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical25199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25199 raw25199Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25199 raw25199Labels = mixedMoment B raw25199step0 raw25199step0Labels := by
      have hz : ∀ j, raw25199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25199step0 = (fun i j => raw25199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25199step0 raw25199; decide +kernel
      have hl : raw25199step0Labels = raw25199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25199 raw25199Labels permutation346 hz
    mixedMoment B raw25199step0 raw25199step0Labels = mixedMoment B raw25199step1 raw25199step1Labels := by
      have ha : raw25199step1 = (fun i j => raw25199step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25199step1 raw25199step0; decide +kernel
      have hl : raw25199step1Labels = raw25199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25199step0 raw25199step0Labels permutation44 permutation7
    mixedMoment B raw25199step1 raw25199step1Labels = mixedMoment B raw25199step2 raw25199step2Labels := by
      have ha : raw25199step2 = -raw25199step1 := by apply Matrix.ext; change ∀ i j, raw25199step2 i j = -(raw25199step1 i j); unfold raw25199step2 raw25199step1; decide +kernel
      have hl : raw25199step2Labels = raw25199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25199step2 raw25199step2Labels = mixedMoment B raw25199step3 raw25199step3Labels := by
      have ha : raw25199step3 = raw25199step2 := by apply Matrix.ext; unfold raw25199step3 raw25199step2; decide +kernel
      have hl : raw25199step2Labels = labelEmbedding1 ∘ raw25199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25199step2 raw25199step2Labels raw25199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical25206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25206 raw25206Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw25206 raw25206Labels = mixedMoment B raw25206step0 raw25206step0Labels := by
      have ha : raw25206step0 = (fun i j => raw25206 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25206step0 raw25206; decide +kernel
      have hl : raw25206step0Labels = raw25206Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25206 raw25206Labels permutation188 permutation7
    mixedMoment B raw25206step0 raw25206step0Labels = mixedMoment B raw25206step1 raw25206step1Labels := by
      have ha : raw25206step1 = -raw25206step0 := by apply Matrix.ext; change ∀ i j, raw25206step1 i j = -(raw25206step0 i j); unfold raw25206step1 raw25206step0; decide +kernel
      have hl : raw25206step1Labels = raw25206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25206step1 raw25206step1Labels = mixedMoment B raw25206step2 raw25206step2Labels := by
      have ha : raw25206step2 = raw25206step1 := by apply Matrix.ext; unfold raw25206step2 raw25206step1; decide +kernel
      have hl : raw25206step1Labels = labelEmbedding1 ∘ raw25206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25206step1 raw25206step1Labels raw25206step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical25211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25211 raw25211Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw25211 raw25211Labels = mixedMoment B raw25211step0 raw25211step0Labels := by
      have hz : ∀ j, raw25211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25211step0 = (fun i j => raw25211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25211step0 raw25211; decide +kernel
      have hl : raw25211step0Labels = raw25211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25211 raw25211Labels permutation346 hz
    mixedMoment B raw25211step0 raw25211step0Labels = mixedMoment B raw25211step1 raw25211step1Labels := by
      have ha : raw25211step1 = (fun i j => raw25211step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25211step1 raw25211step0; decide +kernel
      have hl : raw25211step1Labels = raw25211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25211step0 raw25211step0Labels permutation44 permutation7
    mixedMoment B raw25211step1 raw25211step1Labels = mixedMoment B raw25211step2 raw25211step2Labels := by
      have ha : raw25211step2 = -raw25211step1 := by apply Matrix.ext; change ∀ i j, raw25211step2 i j = -(raw25211step1 i j); unfold raw25211step2 raw25211step1; decide +kernel
      have hl : raw25211step2Labels = raw25211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25211step2 raw25211step2Labels = mixedMoment B raw25211step3 raw25211step3Labels := by
      have ha : raw25211step3 = raw25211step2 := by apply Matrix.ext; unfold raw25211step3 raw25211step2; decide +kernel
      have hl : raw25211step2Labels = labelEmbedding1 ∘ raw25211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25211step2 raw25211step2Labels raw25211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25216 raw25216Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25216 raw25216Labels = mixedMoment B raw25216step0 raw25216step0Labels := by
      have hz : ∀ j, raw25216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25216step0 = (fun i j => raw25216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25216step0 raw25216; decide +kernel
      have hl : raw25216step0Labels = raw25216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25216 raw25216Labels permutation346 hz
    mixedMoment B raw25216step0 raw25216step0Labels = mixedMoment B raw25216step1 raw25216step1Labels := by
      have ha : raw25216step1 = (fun i j => raw25216step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25216step1 raw25216step0; decide +kernel
      have hl : raw25216step1Labels = raw25216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25216step0 raw25216step0Labels permutation44 permutation7
    mixedMoment B raw25216step1 raw25216step1Labels = mixedMoment B raw25216step2 raw25216step2Labels := by
      have ha : raw25216step2 = -raw25216step1 := by apply Matrix.ext; change ∀ i j, raw25216step2 i j = -(raw25216step1 i j); unfold raw25216step2 raw25216step1; decide +kernel
      have hl : raw25216step2Labels = raw25216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25216step2 raw25216step2Labels = mixedMoment B raw25216step3 raw25216step3Labels := by
      have ha : raw25216step3 = raw25216step2 := by apply Matrix.ext; unfold raw25216step3 raw25216step2; decide +kernel
      have hl : raw25216step2Labels = labelEmbedding1 ∘ raw25216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25216step2 raw25216step2Labels raw25216step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25221 raw25221Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw25221 raw25221Labels = mixedMoment B raw25221step0 raw25221step0Labels := by
      have hz : ∀ j, raw25221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25221step0 = (fun i j => raw25221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25221step0 raw25221; decide +kernel
      have hl : raw25221step0Labels = raw25221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25221 raw25221Labels permutation346 hz
    mixedMoment B raw25221step0 raw25221step0Labels = mixedMoment B raw25221step1 raw25221step1Labels := by
      have ha : raw25221step1 = (fun i j => raw25221step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25221step1 raw25221step0; decide +kernel
      have hl : raw25221step1Labels = raw25221step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25221step0 raw25221step0Labels permutation44 permutation7
    mixedMoment B raw25221step1 raw25221step1Labels = mixedMoment B raw25221step2 raw25221step2Labels := by
      have ha : raw25221step2 = -raw25221step1 := by apply Matrix.ext; change ∀ i j, raw25221step2 i j = -(raw25221step1 i j); unfold raw25221step2 raw25221step1; decide +kernel
      have hl : raw25221step2Labels = raw25221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25221step2 raw25221step2Labels = mixedMoment B raw25221step3 raw25221step3Labels := by
      have ha : raw25221step3 = raw25221step2 := by apply Matrix.ext; unfold raw25221step3 raw25221step2; decide +kernel
      have hl : raw25221step2Labels = labelEmbedding1 ∘ raw25221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25221step2 raw25221step2Labels raw25221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical25231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25231 raw25231Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25231 raw25231Labels = mixedMoment B raw25231step0 raw25231step0Labels := by
      have hz : ∀ j, raw25231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25231step0 = (fun i j => raw25231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25231step0 raw25231; decide +kernel
      have hl : raw25231step0Labels = raw25231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231 raw25231Labels permutation520 hz
    mixedMoment B raw25231step0 raw25231step0Labels = mixedMoment B raw25231step1 raw25231step1Labels := by
      have hz : ∀ j, raw25231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25231step1 = (fun i j => raw25231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25231step1 raw25231step0; decide +kernel
      have hl : raw25231step1Labels = raw25231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231step0 raw25231step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25236 raw25236Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw25236 raw25236Labels = mixedMoment B raw25236step0 raw25236step0Labels := by
      have hz : ∀ j, raw25236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25236step0 = (fun i j => raw25236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25236step0 raw25236; decide +kernel
      have hl : raw25236step0Labels = raw25236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25236 raw25236Labels permutation346 hz
    mixedMoment B raw25236step0 raw25236step0Labels = mixedMoment B raw25236step1 raw25236step1Labels := by
      have ha : raw25236step1 = (fun i j => raw25236step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25236step1 raw25236step0; decide +kernel
      have hl : raw25236step1Labels = raw25236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25236step0 raw25236step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27399 raw27399Labels = mixedMoment B node1825 node1825Labels := by
  calc
    mixedMoment B raw27399 raw27399Labels = mixedMoment B raw27399step0 raw27399step0Labels := by
      have hz : ∀ j, raw27399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27399step0 = (fun i j => raw27399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27399step0 raw27399; decide +kernel
      have hl : raw27399step0Labels = raw27399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27399 raw27399Labels permutation346 hz
    mixedMoment B raw27399step0 raw27399step0Labels = mixedMoment B raw27399step1 raw27399step1Labels := by
      have ha : raw27399step1 = (fun i j => raw27399step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27399step1 raw27399step0; decide +kernel
      have hl : raw27399step1Labels = raw27399step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27399step0 raw27399step0Labels permutation34 permutation2
    _ = mixedMoment B node1825 node1825Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29097 raw29097Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw29097 raw29097Labels = mixedMoment B raw29097step0 raw29097step0Labels := by
      have hz : ∀ j, raw29097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29097step0 = (fun i j => raw29097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29097step0 raw29097; decide +kernel
      have hl : raw29097step0Labels = raw29097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097 raw29097Labels permutation434 hz
    mixedMoment B raw29097step0 raw29097step0Labels = mixedMoment B raw29097step1 raw29097step1Labels := by
      have hz : ∀ j, raw29097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29097step1 = (fun i j => raw29097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29097step1 raw29097step0; decide +kernel
      have hl : raw29097step1Labels = raw29097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097step0 raw29097step0Labels permutation80 hz
    mixedMoment B raw29097step1 raw29097step1Labels = mixedMoment B raw29097step2 raw29097step2Labels := by
      have ha : raw29097step2 = (fun i j => raw29097step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29097step2 raw29097step1; decide +kernel
      have hl : raw29097step2Labels = raw29097step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29097step1 raw29097step1Labels permutation31 permutation7
    mixedMoment B raw29097step2 raw29097step2Labels = mixedMoment B raw29097step3 raw29097step3Labels := by
      have ha : raw29097step3 = raw29097step2 := by apply Matrix.ext; unfold raw29097step3 raw29097step2; decide +kernel
      have hl : raw29097step2Labels = labelEmbedding1 ∘ raw29097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29097step2 raw29097step2Labels raw29097step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical29102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29102 raw29102Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw29102 raw29102Labels = mixedMoment B raw29102step0 raw29102step0Labels := by
      have hz : ∀ j, raw29102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29102step0 = (fun i j => raw29102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29102step0 raw29102; decide +kernel
      have hl : raw29102step0Labels = raw29102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102 raw29102Labels permutation434 hz
    mixedMoment B raw29102step0 raw29102step0Labels = mixedMoment B raw29102step1 raw29102step1Labels := by
      have hz : ∀ j, raw29102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29102step1 = (fun i j => raw29102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29102step1 raw29102step0; decide +kernel
      have hl : raw29102step1Labels = raw29102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102step0 raw29102step0Labels permutation80 hz
    mixedMoment B raw29102step1 raw29102step1Labels = mixedMoment B raw29102step2 raw29102step2Labels := by
      have ha : raw29102step2 = (fun i j => raw29102step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29102step2 raw29102step1; decide +kernel
      have hl : raw29102step2Labels = raw29102step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29102step1 raw29102step1Labels permutation31 permutation7
    mixedMoment B raw29102step2 raw29102step2Labels = mixedMoment B raw29102step3 raw29102step3Labels := by
      have ha : raw29102step3 = raw29102step2 := by apply Matrix.ext; unfold raw29102step3 raw29102step2; decide +kernel
      have hl : raw29102step2Labels = labelEmbedding1 ∘ raw29102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29102step2 raw29102step2Labels raw29102step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical29107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29107 raw29107Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw29107 raw29107Labels = mixedMoment B raw29107step0 raw29107step0Labels := by
      have hz : ∀ j, raw29107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29107step0 = (fun i j => raw29107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29107step0 raw29107; decide +kernel
      have hl : raw29107step0Labels = raw29107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29107 raw29107Labels permutation434 hz
    mixedMoment B raw29107step0 raw29107step0Labels = mixedMoment B raw29107step1 raw29107step1Labels := by
      have ha : raw29107step1 = (fun i j => raw29107step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29107step1 raw29107step0; decide +kernel
      have hl : raw29107step1Labels = raw29107step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29107step0 raw29107step0Labels permutation145 permutation7
    mixedMoment B raw29107step1 raw29107step1Labels = mixedMoment B raw29107step2 raw29107step2Labels := by
      have ha : raw29107step2 = raw29107step1 := by apply Matrix.ext; unfold raw29107step2 raw29107step1; decide +kernel
      have hl : raw29107step1Labels = labelEmbedding1 ∘ raw29107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29107step1 raw29107step1Labels raw29107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical29108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29108 raw29108Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw29108 raw29108Labels = mixedMoment B raw29108step0 raw29108step0Labels := by
      have hz : ∀ j, raw29108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29108step0 = (fun i j => raw29108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29108step0 raw29108; decide +kernel
      have hl : raw29108step0Labels = raw29108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29108 raw29108Labels permutation346 hz
    mixedMoment B raw29108step0 raw29108step0Labels = mixedMoment B raw29108step1 raw29108step1Labels := by
      have ha : raw29108step1 = (fun i j => raw29108step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29108step1 raw29108step0; decide +kernel
      have hl : raw29108step1Labels = raw29108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29108step0 raw29108step0Labels permutation145 permutation7
    mixedMoment B raw29108step1 raw29108step1Labels = mixedMoment B raw29108step2 raw29108step2Labels := by
      have ha : raw29108step2 = raw29108step1 := by apply Matrix.ext; unfold raw29108step2 raw29108step1; decide +kernel
      have hl : raw29108step1Labels = labelEmbedding1 ∘ raw29108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29108step1 raw29108step1Labels raw29108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical29109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29109 raw29109Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw29109 raw29109Labels = mixedMoment B raw29109step0 raw29109step0Labels := by
      have hz : ∀ j, raw29109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29109step0 = (fun i j => raw29109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29109step0 raw29109; decide +kernel
      have hl : raw29109step0Labels = raw29109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29109 raw29109Labels permutation346 hz
    mixedMoment B raw29109step0 raw29109step0Labels = mixedMoment B raw29109step1 raw29109step1Labels := by
      have ha : raw29109step1 = (fun i j => raw29109step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29109step1 raw29109step0; decide +kernel
      have hl : raw29109step1Labels = raw29109step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29109step0 raw29109step0Labels permutation145 permutation7
    mixedMoment B raw29109step1 raw29109step1Labels = mixedMoment B raw29109step2 raw29109step2Labels := by
      have ha : raw29109step2 = raw29109step1 := by apply Matrix.ext; unfold raw29109step2 raw29109step1; decide +kernel
      have hl : raw29109step1Labels = labelEmbedding1 ∘ raw29109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29109step1 raw29109step1Labels raw29109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical29110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29110 raw29110Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw29110 raw29110Labels = mixedMoment B raw29110step0 raw29110step0Labels := by
      have ha : raw29110step0 = (fun i j => raw29110 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29110step0 raw29110; decide +kernel
      have hl : raw29110step0Labels = raw29110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29110 raw29110Labels permutation664 permutation7
    mixedMoment B raw29110step0 raw29110step0Labels = mixedMoment B raw29110step1 raw29110step1Labels := by
      have ha : raw29110step1 = raw29110step0 := by apply Matrix.ext; unfold raw29110step1 raw29110step0; decide +kernel
      have hl : raw29110step0Labels = labelEmbedding1 ∘ raw29110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29110step0 raw29110step0Labels raw29110step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical29111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29111 raw29111Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw29111 raw29111Labels = mixedMoment B raw29111step0 raw29111step0Labels := by
      have hz : ∀ j, raw29111 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29111step0 = (fun i j => raw29111 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29111step0 raw29111; decide +kernel
      have hl : raw29111step0Labels = raw29111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111 raw29111Labels permutation520 hz
    mixedMoment B raw29111step0 raw29111step0Labels = mixedMoment B raw29111step1 raw29111step1Labels := by
      have hz : ∀ j, raw29111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29111step1 = (fun i j => raw29111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29111step1 raw29111step0; decide +kernel
      have hl : raw29111step1Labels = raw29111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111step0 raw29111step0Labels permutation80 hz
    mixedMoment B raw29111step1 raw29111step1Labels = mixedMoment B raw29111step2 raw29111step2Labels := by
      have ha : raw29111step2 = (fun i j => raw29111step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29111step2 raw29111step1; decide +kernel
      have hl : raw29111step2Labels = raw29111step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29111step1 raw29111step1Labels permutation31 permutation7
    mixedMoment B raw29111step2 raw29111step2Labels = mixedMoment B raw29111step3 raw29111step3Labels := by
      have ha : raw29111step3 = raw29111step2 := by apply Matrix.ext; unfold raw29111step3 raw29111step2; decide +kernel
      have hl : raw29111step2Labels = labelEmbedding1 ∘ raw29111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29111step2 raw29111step2Labels raw29111step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical29117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29117 raw29117Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw29117 raw29117Labels = mixedMoment B raw29117step0 raw29117step0Labels := by
      have hz : ∀ j, raw29117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29117step0 = (fun i j => raw29117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29117step0 raw29117; decide +kernel
      have hl : raw29117step0Labels = raw29117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117 raw29117Labels permutation434 hz
    mixedMoment B raw29117step0 raw29117step0Labels = mixedMoment B raw29117step1 raw29117step1Labels := by
      have hz : ∀ j, raw29117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29117step1 = (fun i j => raw29117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29117step1 raw29117step0; decide +kernel
      have hl : raw29117step1Labels = raw29117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117step0 raw29117step0Labels permutation80 hz
    mixedMoment B raw29117step1 raw29117step1Labels = mixedMoment B raw29117step2 raw29117step2Labels := by
      have ha : raw29117step2 = (fun i j => raw29117step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29117step2 raw29117step1; decide +kernel
      have hl : raw29117step2Labels = raw29117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29117step1 raw29117step1Labels permutation31 permutation7
    mixedMoment B raw29117step2 raw29117step2Labels = mixedMoment B raw29117step3 raw29117step3Labels := by
      have ha : raw29117step3 = raw29117step2 := by apply Matrix.ext; unfold raw29117step3 raw29117step2; decide +kernel
      have hl : raw29117step2Labels = labelEmbedding1 ∘ raw29117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29117step2 raw29117step2Labels raw29117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

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

theorem canonical29343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29343 raw29343Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw29343 raw29343Labels = mixedMoment B raw29343step0 raw29343step0Labels := by
      have hz : ∀ j, raw29343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29343step0 = (fun i j => raw29343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29343step0 raw29343; decide +kernel
      have hl : raw29343step0Labels = raw29343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29343 raw29343Labels permutation346 hz
    _ = mixedMoment B node1829 node1829Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31902 raw31902Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31902 raw31902Labels = mixedMoment B raw31902step0 raw31902step0Labels := by
      have hz : ∀ j, raw31902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31902step0 = (fun i j => raw31902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31902step0 raw31902; decide +kernel
      have hl : raw31902step0Labels = raw31902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31902 raw31902Labels permutation346 hz
    mixedMoment B raw31902step0 raw31902step0Labels = mixedMoment B raw31902step1 raw31902step1Labels := by
      have ha : raw31902step1 = -raw31902step0 := by apply Matrix.ext; change ∀ i j, raw31902step1 i j = -(raw31902step0 i j); unfold raw31902step1 raw31902step0; decide +kernel
      have hl : raw31902step1Labels = raw31902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical33149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33149 raw33149Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw33149 raw33149Labels = mixedMoment B raw33149step0 raw33149step0Labels := by
      have ha : raw33149step0 = (fun i j => raw33149 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33149step0 raw33149; decide +kernel
      have hl : raw33149step0Labels = raw33149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33149 raw33149Labels permutation164 permutation4
    mixedMoment B raw33149step0 raw33149step0Labels = mixedMoment B raw33149step1 raw33149step1Labels := by
      have ha : raw33149step1 = -raw33149step0 := by apply Matrix.ext; change ∀ i j, raw33149step1 i j = -(raw33149step0 i j); unfold raw33149step1 raw33149step0; decide +kernel
      have hl : raw33149step1Labels = raw33149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3444 node3444Labels := by rfl

theorem canonical33150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33150 raw33150Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw33150 raw33150Labels = mixedMoment B raw33150step0 raw33150step0Labels := by
      have ha : raw33150step0 = (fun i j => raw33150 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33150step0 raw33150; decide +kernel
      have hl : raw33150step0Labels = raw33150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33150 raw33150Labels permutation224 permutation4
    mixedMoment B raw33150step0 raw33150step0Labels = mixedMoment B raw33150step1 raw33150step1Labels := by
      have ha : raw33150step1 = -raw33150step0 := by apply Matrix.ext; change ∀ i j, raw33150step1 i j = -(raw33150step0 i j); unfold raw33150step1 raw33150step0; decide +kernel
      have hl : raw33150step1Labels = raw33150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical33151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33151 raw33151Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw33151 raw33151Labels = mixedMoment B raw33151step0 raw33151step0Labels := by
      have ha : raw33151step0 = (fun i j => raw33151 (permutation166 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33151step0 raw33151; decide +kernel
      have hl : raw33151step0Labels = raw33151Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33151 raw33151Labels permutation166 permutation4
    mixedMoment B raw33151step0 raw33151step0Labels = mixedMoment B raw33151step1 raw33151step1Labels := by
      have ha : raw33151step1 = -raw33151step0 := by apply Matrix.ext; change ∀ i j, raw33151step1 i j = -(raw33151step0 i j); unfold raw33151step1 raw33151step0; decide +kernel
      have hl : raw33151step1Labels = raw33151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1878 node1878Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33152 raw33152Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw33152 raw33152Labels = mixedMoment B raw33152step0 raw33152step0Labels := by
      have ha : raw33152step0 = (fun i j => raw33152 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33152step0 raw33152; decide +kernel
      have hl : raw33152step0Labels = raw33152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33152 raw33152Labels permutation164 permutation4
    mixedMoment B raw33152step0 raw33152step0Labels = mixedMoment B raw33152step1 raw33152step1Labels := by
      have ha : raw33152step1 = -raw33152step0 := by apply Matrix.ext; change ∀ i j, raw33152step1 i j = -(raw33152step0 i j); unfold raw33152step1 raw33152step0; decide +kernel
      have hl : raw33152step1Labels = raw33152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1876 node1876Labels := by rfl

theorem canonical33153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33153 raw33153Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw33153 raw33153Labels = mixedMoment B raw33153step0 raw33153step0Labels := by
      have ha : raw33153step0 = (fun i j => raw33153 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33153step0 raw33153; decide +kernel
      have hl : raw33153step0Labels = raw33153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33153 raw33153Labels permutation164 permutation4
    mixedMoment B raw33153step0 raw33153step0Labels = mixedMoment B raw33153step1 raw33153step1Labels := by
      have ha : raw33153step1 = -raw33153step0 := by apply Matrix.ext; change ∀ i j, raw33153step1 i j = -(raw33153step0 i j); unfold raw33153step1 raw33153step0; decide +kernel
      have hl : raw33153step1Labels = raw33153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1908 node1908Labels := by rfl

theorem canonical33154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33154 raw33154Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw33154 raw33154Labels = mixedMoment B raw33154step0 raw33154step0Labels := by
      have ha : raw33154step0 = (fun i j => raw33154 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33154step0 raw33154; decide +kernel
      have hl : raw33154step0Labels = raw33154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33154 raw33154Labels permutation164 permutation4
    mixedMoment B raw33154step0 raw33154step0Labels = mixedMoment B raw33154step1 raw33154step1Labels := by
      have ha : raw33154step1 = -raw33154step0 := by apply Matrix.ext; change ∀ i j, raw33154step1 i j = -(raw33154step0 i j); unfold raw33154step1 raw33154step0; decide +kernel
      have hl : raw33154step1Labels = raw33154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

theorem canonical33177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33177 raw33177Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw33177 raw33177Labels = mixedMoment B raw33177step0 raw33177step0Labels := by
      have ha : raw33177step0 = (fun i j => raw33177 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33177step0 raw33177; decide +kernel
      have hl : raw33177step0Labels = raw33177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33177 raw33177Labels permutation160 permutation7
    mixedMoment B raw33177step0 raw33177step0Labels = mixedMoment B raw33177step1 raw33177step1Labels := by
      have ha : raw33177step1 = -raw33177step0 := by apply Matrix.ext; change ∀ i j, raw33177step1 i j = -(raw33177step0 i j); unfold raw33177step1 raw33177step0; decide +kernel
      have hl : raw33177step1Labels = raw33177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33177step1 raw33177step1Labels = mixedMoment B raw33177step2 raw33177step2Labels := by
      have ha : raw33177step2 = raw33177step1 := by apply Matrix.ext; unfold raw33177step2 raw33177step1; decide +kernel
      have hl : raw33177step1Labels = labelEmbedding1 ∘ raw33177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33177step1 raw33177step1Labels raw33177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical33178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33178 raw33178Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw33178 raw33178Labels = mixedMoment B raw33178step0 raw33178step0Labels := by
      have ha : raw33178step0 = (fun i j => raw33178 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33178step0 raw33178; decide +kernel
      have hl : raw33178step0Labels = raw33178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33178 raw33178Labels permutation160 permutation7
    mixedMoment B raw33178step0 raw33178step0Labels = mixedMoment B raw33178step1 raw33178step1Labels := by
      have ha : raw33178step1 = -raw33178step0 := by apply Matrix.ext; change ∀ i j, raw33178step1 i j = -(raw33178step0 i j); unfold raw33178step1 raw33178step0; decide +kernel
      have hl : raw33178step1Labels = raw33178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33178step1 raw33178step1Labels = mixedMoment B raw33178step2 raw33178step2Labels := by
      have ha : raw33178step2 = raw33178step1 := by apply Matrix.ext; unfold raw33178step2 raw33178step1; decide +kernel
      have hl : raw33178step1Labels = labelEmbedding1 ∘ raw33178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33178step1 raw33178step1Labels raw33178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical33179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33179 raw33179Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw33179 raw33179Labels = mixedMoment B raw33179step0 raw33179step0Labels := by
      have hz : ∀ j, raw33179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33179step0 = (fun i j => raw33179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33179step0 raw33179; decide +kernel
      have hl : raw33179step0Labels = raw33179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33179 raw33179Labels permutation434 hz
    mixedMoment B raw33179step0 raw33179step0Labels = mixedMoment B raw33179step1 raw33179step1Labels := by
      have ha : raw33179step1 = (fun i j => raw33179step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33179step1 raw33179step0; decide +kernel
      have hl : raw33179step1Labels = raw33179step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33179step0 raw33179step0Labels permutation34 permutation7
    mixedMoment B raw33179step1 raw33179step1Labels = mixedMoment B raw33179step2 raw33179step2Labels := by
      have ha : raw33179step2 = -raw33179step1 := by apply Matrix.ext; change ∀ i j, raw33179step2 i j = -(raw33179step1 i j); unfold raw33179step2 raw33179step1; decide +kernel
      have hl : raw33179step2Labels = raw33179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33179step2 raw33179step2Labels = mixedMoment B raw33179step3 raw33179step3Labels := by
      have ha : raw33179step3 = raw33179step2 := by apply Matrix.ext; unfold raw33179step3 raw33179step2; decide +kernel
      have hl : raw33179step2Labels = labelEmbedding1 ∘ raw33179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33179step2 raw33179step2Labels raw33179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical33180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33180 raw33180Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw33180 raw33180Labels = mixedMoment B raw33180step0 raw33180step0Labels := by
      have hz : ∀ j, raw33180 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33180step0 = (fun i j => raw33180 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33180step0 raw33180; decide +kernel
      have hl : raw33180step0Labels = raw33180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33180 raw33180Labels permutation520 hz
    mixedMoment B raw33180step0 raw33180step0Labels = mixedMoment B raw33180step1 raw33180step1Labels := by
      have ha : raw33180step1 = (fun i j => raw33180step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33180step1 raw33180step0; decide +kernel
      have hl : raw33180step1Labels = raw33180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33180step0 raw33180step0Labels permutation34 permutation7
    mixedMoment B raw33180step1 raw33180step1Labels = mixedMoment B raw33180step2 raw33180step2Labels := by
      have ha : raw33180step2 = -raw33180step1 := by apply Matrix.ext; change ∀ i j, raw33180step2 i j = -(raw33180step1 i j); unfold raw33180step2 raw33180step1; decide +kernel
      have hl : raw33180step2Labels = raw33180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33180step2 raw33180step2Labels = mixedMoment B raw33180step3 raw33180step3Labels := by
      have ha : raw33180step3 = raw33180step2 := by apply Matrix.ext; unfold raw33180step3 raw33180step2; decide +kernel
      have hl : raw33180step2Labels = labelEmbedding1 ∘ raw33180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33180step2 raw33180step2Labels raw33180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical33181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33181 raw33181Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw33181 raw33181Labels = mixedMoment B raw33181step0 raw33181step0Labels := by
      have ha : raw33181step0 = (fun i j => raw33181 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33181step0 raw33181; decide +kernel
      have hl : raw33181step0Labels = raw33181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33181 raw33181Labels permutation160 permutation7
    mixedMoment B raw33181step0 raw33181step0Labels = mixedMoment B raw33181step1 raw33181step1Labels := by
      have ha : raw33181step1 = -raw33181step0 := by apply Matrix.ext; change ∀ i j, raw33181step1 i j = -(raw33181step0 i j); unfold raw33181step1 raw33181step0; decide +kernel
      have hl : raw33181step1Labels = raw33181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33181step1 raw33181step1Labels = mixedMoment B raw33181step2 raw33181step2Labels := by
      have ha : raw33181step2 = raw33181step1 := by apply Matrix.ext; unfold raw33181step2 raw33181step1; decide +kernel
      have hl : raw33181step1Labels = labelEmbedding1 ∘ raw33181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33181step1 raw33181step1Labels raw33181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical33182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33182 raw33182Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw33182 raw33182Labels = mixedMoment B raw33182step0 raw33182step0Labels := by
      have ha : raw33182step0 = (fun i j => raw33182 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33182step0 raw33182; decide +kernel
      have hl : raw33182step0Labels = raw33182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33182 raw33182Labels permutation160 permutation7
    mixedMoment B raw33182step0 raw33182step0Labels = mixedMoment B raw33182step1 raw33182step1Labels := by
      have ha : raw33182step1 = -raw33182step0 := by apply Matrix.ext; change ∀ i j, raw33182step1 i j = -(raw33182step0 i j); unfold raw33182step1 raw33182step0; decide +kernel
      have hl : raw33182step1Labels = raw33182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33182step1 raw33182step1Labels = mixedMoment B raw33182step2 raw33182step2Labels := by
      have ha : raw33182step2 = raw33182step1 := by apply Matrix.ext; unfold raw33182step2 raw33182step1; decide +kernel
      have hl : raw33182step1Labels = labelEmbedding1 ∘ raw33182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33182step1 raw33182step1Labels raw33182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

theorem canonical33183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33183 raw33183Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw33183 raw33183Labels = mixedMoment B raw33183step0 raw33183step0Labels := by
      have ha : raw33183step0 = (fun i j => raw33183 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33183step0 raw33183; decide +kernel
      have hl : raw33183step0Labels = raw33183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33183 raw33183Labels permutation160 permutation7
    mixedMoment B raw33183step0 raw33183step0Labels = mixedMoment B raw33183step1 raw33183step1Labels := by
      have ha : raw33183step1 = -raw33183step0 := by apply Matrix.ext; change ∀ i j, raw33183step1 i j = -(raw33183step0 i j); unfold raw33183step1 raw33183step0; decide +kernel
      have hl : raw33183step1Labels = raw33183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33183step1 raw33183step1Labels = mixedMoment B raw33183step2 raw33183step2Labels := by
      have ha : raw33183step2 = raw33183step1 := by apply Matrix.ext; unfold raw33183step2 raw33183step1; decide +kernel
      have hl : raw33183step1Labels = labelEmbedding1 ∘ raw33183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33183step1 raw33183step1Labels raw33183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

theorem canonical33184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33184 raw33184Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw33184 raw33184Labels = mixedMoment B raw33184step0 raw33184step0Labels := by
      have hz : ∀ j, raw33184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33184step0 = (fun i j => raw33184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33184step0 raw33184; decide +kernel
      have hl : raw33184step0Labels = raw33184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33184 raw33184Labels permutation434 hz
    mixedMoment B raw33184step0 raw33184step0Labels = mixedMoment B raw33184step1 raw33184step1Labels := by
      have ha : raw33184step1 = (fun i j => raw33184step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33184step1 raw33184step0; decide +kernel
      have hl : raw33184step1Labels = raw33184step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33184step0 raw33184step0Labels permutation34 permutation7
    mixedMoment B raw33184step1 raw33184step1Labels = mixedMoment B raw33184step2 raw33184step2Labels := by
      have ha : raw33184step2 = -raw33184step1 := by apply Matrix.ext; change ∀ i j, raw33184step2 i j = -(raw33184step1 i j); unfold raw33184step2 raw33184step1; decide +kernel
      have hl : raw33184step2Labels = raw33184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33184step2 raw33184step2Labels = mixedMoment B raw33184step3 raw33184step3Labels := by
      have ha : raw33184step3 = raw33184step2 := by apply Matrix.ext; unfold raw33184step3 raw33184step2; decide +kernel
      have hl : raw33184step2Labels = labelEmbedding1 ∘ raw33184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33184step2 raw33184step2Labels raw33184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical33185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33185 raw33185Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw33185 raw33185Labels = mixedMoment B raw33185step0 raw33185step0Labels := by
      have hz : ∀ j, raw33185 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33185step0 = (fun i j => raw33185 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33185step0 raw33185; decide +kernel
      have hl : raw33185step0Labels = raw33185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33185 raw33185Labels permutation520 hz
    mixedMoment B raw33185step0 raw33185step0Labels = mixedMoment B raw33185step1 raw33185step1Labels := by
      have ha : raw33185step1 = (fun i j => raw33185step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33185step1 raw33185step0; decide +kernel
      have hl : raw33185step1Labels = raw33185step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33185step0 raw33185step0Labels permutation34 permutation7
    mixedMoment B raw33185step1 raw33185step1Labels = mixedMoment B raw33185step2 raw33185step2Labels := by
      have ha : raw33185step2 = -raw33185step1 := by apply Matrix.ext; change ∀ i j, raw33185step2 i j = -(raw33185step1 i j); unfold raw33185step2 raw33185step1; decide +kernel
      have hl : raw33185step2Labels = raw33185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33185step2 raw33185step2Labels = mixedMoment B raw33185step3 raw33185step3Labels := by
      have ha : raw33185step3 = raw33185step2 := by apply Matrix.ext; unfold raw33185step3 raw33185step2; decide +kernel
      have hl : raw33185step2Labels = labelEmbedding1 ∘ raw33185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33185step2 raw33185step2Labels raw33185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical33186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33186 raw33186Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw33186 raw33186Labels = mixedMoment B raw33186step0 raw33186step0Labels := by
      have ha : raw33186step0 = (fun i j => raw33186 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33186step0 raw33186; decide +kernel
      have hl : raw33186step0Labels = raw33186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33186 raw33186Labels permutation166 permutation7
    mixedMoment B raw33186step0 raw33186step0Labels = mixedMoment B raw33186step1 raw33186step1Labels := by
      have ha : raw33186step1 = -raw33186step0 := by apply Matrix.ext; change ∀ i j, raw33186step1 i j = -(raw33186step0 i j); unfold raw33186step1 raw33186step0; decide +kernel
      have hl : raw33186step1Labels = raw33186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33186step1 raw33186step1Labels = mixedMoment B raw33186step2 raw33186step2Labels := by
      have ha : raw33186step2 = raw33186step1 := by apply Matrix.ext; unfold raw33186step2 raw33186step1; decide +kernel
      have hl : raw33186step1Labels = labelEmbedding1 ∘ raw33186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33186step1 raw33186step1Labels raw33186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical33187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33187 raw33187Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw33187 raw33187Labels = mixedMoment B raw33187step0 raw33187step0Labels := by
      have ha : raw33187step0 = (fun i j => raw33187 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33187step0 raw33187; decide +kernel
      have hl : raw33187step0Labels = raw33187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33187 raw33187Labels permutation166 permutation7
    mixedMoment B raw33187step0 raw33187step0Labels = mixedMoment B raw33187step1 raw33187step1Labels := by
      have ha : raw33187step1 = -raw33187step0 := by apply Matrix.ext; change ∀ i j, raw33187step1 i j = -(raw33187step0 i j); unfold raw33187step1 raw33187step0; decide +kernel
      have hl : raw33187step1Labels = raw33187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33187step1 raw33187step1Labels = mixedMoment B raw33187step2 raw33187step2Labels := by
      have ha : raw33187step2 = raw33187step1 := by apply Matrix.ext; unfold raw33187step2 raw33187step1; decide +kernel
      have hl : raw33187step1Labels = labelEmbedding1 ∘ raw33187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33187step1 raw33187step1Labels raw33187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical33188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33188 raw33188Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw33188 raw33188Labels = mixedMoment B raw33188step0 raw33188step0Labels := by
      have ha : raw33188step0 = (fun i j => raw33188 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33188step0 raw33188; decide +kernel
      have hl : raw33188step0Labels = raw33188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33188 raw33188Labels permutation166 permutation7
    mixedMoment B raw33188step0 raw33188step0Labels = mixedMoment B raw33188step1 raw33188step1Labels := by
      have ha : raw33188step1 = -raw33188step0 := by apply Matrix.ext; change ∀ i j, raw33188step1 i j = -(raw33188step0 i j); unfold raw33188step1 raw33188step0; decide +kernel
      have hl : raw33188step1Labels = raw33188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33188step1 raw33188step1Labels = mixedMoment B raw33188step2 raw33188step2Labels := by
      have ha : raw33188step2 = raw33188step1 := by apply Matrix.ext; unfold raw33188step2 raw33188step1; decide +kernel
      have hl : raw33188step1Labels = labelEmbedding1 ∘ raw33188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33188step1 raw33188step1Labels raw33188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical33189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33189 raw33189Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw33189 raw33189Labels = mixedMoment B raw33189step0 raw33189step0Labels := by
      have hz : ∀ j, raw33189 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33189step0 = (fun i j => raw33189 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33189step0 raw33189; decide +kernel
      have hl : raw33189step0Labels = raw33189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33189 raw33189Labels permutation520 hz
    mixedMoment B raw33189step0 raw33189step0Labels = mixedMoment B raw33189step1 raw33189step1Labels := by
      have ha : raw33189step1 = (fun i j => raw33189step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33189step1 raw33189step0; decide +kernel
      have hl : raw33189step1Labels = raw33189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33189step0 raw33189step0Labels permutation34 permutation7
    mixedMoment B raw33189step1 raw33189step1Labels = mixedMoment B raw33189step2 raw33189step2Labels := by
      have ha : raw33189step2 = -raw33189step1 := by apply Matrix.ext; change ∀ i j, raw33189step2 i j = -(raw33189step1 i j); unfold raw33189step2 raw33189step1; decide +kernel
      have hl : raw33189step2Labels = raw33189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33189step2 raw33189step2Labels = mixedMoment B raw33189step3 raw33189step3Labels := by
      have ha : raw33189step3 = raw33189step2 := by apply Matrix.ext; unfold raw33189step3 raw33189step2; decide +kernel
      have hl : raw33189step2Labels = labelEmbedding1 ∘ raw33189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33189step2 raw33189step2Labels raw33189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical33190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33190 raw33190Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw33190 raw33190Labels = mixedMoment B raw33190step0 raw33190step0Labels := by
      have ha : raw33190step0 = (fun i j => raw33190 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33190step0 raw33190; decide +kernel
      have hl : raw33190step0Labels = raw33190Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33190 raw33190Labels permutation160 permutation7
    mixedMoment B raw33190step0 raw33190step0Labels = mixedMoment B raw33190step1 raw33190step1Labels := by
      have ha : raw33190step1 = -raw33190step0 := by apply Matrix.ext; change ∀ i j, raw33190step1 i j = -(raw33190step0 i j); unfold raw33190step1 raw33190step0; decide +kernel
      have hl : raw33190step1Labels = raw33190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33190step1 raw33190step1Labels = mixedMoment B raw33190step2 raw33190step2Labels := by
      have ha : raw33190step2 = raw33190step1 := by apply Matrix.ext; unfold raw33190step2 raw33190step1; decide +kernel
      have hl : raw33190step1Labels = labelEmbedding1 ∘ raw33190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33190step1 raw33190step1Labels raw33190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical33191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33191 raw33191Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw33191 raw33191Labels = mixedMoment B raw33191step0 raw33191step0Labels := by
      have ha : raw33191step0 = (fun i j => raw33191 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33191step0 raw33191; decide +kernel
      have hl : raw33191step0Labels = raw33191Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33191 raw33191Labels permutation160 permutation7
    mixedMoment B raw33191step0 raw33191step0Labels = mixedMoment B raw33191step1 raw33191step1Labels := by
      have ha : raw33191step1 = -raw33191step0 := by apply Matrix.ext; change ∀ i j, raw33191step1 i j = -(raw33191step0 i j); unfold raw33191step1 raw33191step0; decide +kernel
      have hl : raw33191step1Labels = raw33191step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33191step1 raw33191step1Labels = mixedMoment B raw33191step2 raw33191step2Labels := by
      have ha : raw33191step2 = raw33191step1 := by apply Matrix.ext; unfold raw33191step2 raw33191step1; decide +kernel
      have hl : raw33191step1Labels = labelEmbedding1 ∘ raw33191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33191step1 raw33191step1Labels raw33191step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical33192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33192 raw33192Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw33192 raw33192Labels = mixedMoment B raw33192step0 raw33192step0Labels := by
      have ha : raw33192step0 = (fun i j => raw33192 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33192step0 raw33192; decide +kernel
      have hl : raw33192step0Labels = raw33192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33192 raw33192Labels permutation160 permutation7
    mixedMoment B raw33192step0 raw33192step0Labels = mixedMoment B raw33192step1 raw33192step1Labels := by
      have ha : raw33192step1 = -raw33192step0 := by apply Matrix.ext; change ∀ i j, raw33192step1 i j = -(raw33192step0 i j); unfold raw33192step1 raw33192step0; decide +kernel
      have hl : raw33192step1Labels = raw33192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33192step1 raw33192step1Labels = mixedMoment B raw33192step2 raw33192step2Labels := by
      have ha : raw33192step2 = raw33192step1 := by apply Matrix.ext; unfold raw33192step2 raw33192step1; decide +kernel
      have hl : raw33192step1Labels = labelEmbedding1 ∘ raw33192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33192step1 raw33192step1Labels raw33192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical33193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33193 raw33193Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw33193 raw33193Labels = mixedMoment B raw33193step0 raw33193step0Labels := by
      have hz : ∀ j, raw33193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33193step0 = (fun i j => raw33193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33193step0 raw33193; decide +kernel
      have hl : raw33193step0Labels = raw33193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33193 raw33193Labels permutation434 hz
    mixedMoment B raw33193step0 raw33193step0Labels = mixedMoment B raw33193step1 raw33193step1Labels := by
      have ha : raw33193step1 = (fun i j => raw33193step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33193step1 raw33193step0; decide +kernel
      have hl : raw33193step1Labels = raw33193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33193step0 raw33193step0Labels permutation34 permutation7
    mixedMoment B raw33193step1 raw33193step1Labels = mixedMoment B raw33193step2 raw33193step2Labels := by
      have ha : raw33193step2 = -raw33193step1 := by apply Matrix.ext; change ∀ i j, raw33193step2 i j = -(raw33193step1 i j); unfold raw33193step2 raw33193step1; decide +kernel
      have hl : raw33193step2Labels = raw33193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33193step2 raw33193step2Labels = mixedMoment B raw33193step3 raw33193step3Labels := by
      have ha : raw33193step3 = raw33193step2 := by apply Matrix.ext; unfold raw33193step3 raw33193step2; decide +kernel
      have hl : raw33193step2Labels = labelEmbedding1 ∘ raw33193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33193step2 raw33193step2Labels raw33193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical33194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33194 raw33194Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw33194 raw33194Labels = mixedMoment B raw33194step0 raw33194step0Labels := by
      have ha : raw33194step0 = (fun i j => raw33194 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33194step0 raw33194; decide +kernel
      have hl : raw33194step0Labels = raw33194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33194 raw33194Labels permutation160 permutation7
    mixedMoment B raw33194step0 raw33194step0Labels = mixedMoment B raw33194step1 raw33194step1Labels := by
      have ha : raw33194step1 = -raw33194step0 := by apply Matrix.ext; change ∀ i j, raw33194step1 i j = -(raw33194step0 i j); unfold raw33194step1 raw33194step0; decide +kernel
      have hl : raw33194step1Labels = raw33194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33194step1 raw33194step1Labels = mixedMoment B raw33194step2 raw33194step2Labels := by
      have ha : raw33194step2 = raw33194step1 := by apply Matrix.ext; unfold raw33194step2 raw33194step1; decide +kernel
      have hl : raw33194step1Labels = labelEmbedding1 ∘ raw33194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33194step1 raw33194step1Labels raw33194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical33195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33195 raw33195Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw33195 raw33195Labels = mixedMoment B raw33195step0 raw33195step0Labels := by
      have ha : raw33195step0 = (fun i j => raw33195 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33195step0 raw33195; decide +kernel
      have hl : raw33195step0Labels = raw33195Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33195 raw33195Labels permutation160 permutation7
    mixedMoment B raw33195step0 raw33195step0Labels = mixedMoment B raw33195step1 raw33195step1Labels := by
      have ha : raw33195step1 = -raw33195step0 := by apply Matrix.ext; change ∀ i j, raw33195step1 i j = -(raw33195step0 i j); unfold raw33195step1 raw33195step0; decide +kernel
      have hl : raw33195step1Labels = raw33195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33195step1 raw33195step1Labels = mixedMoment B raw33195step2 raw33195step2Labels := by
      have ha : raw33195step2 = raw33195step1 := by apply Matrix.ext; unfold raw33195step2 raw33195step1; decide +kernel
      have hl : raw33195step1Labels = labelEmbedding1 ∘ raw33195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33195step1 raw33195step1Labels raw33195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

theorem canonical33196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33196 raw33196Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw33196 raw33196Labels = mixedMoment B raw33196step0 raw33196step0Labels := by
      have ha : raw33196step0 = (fun i j => raw33196 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33196step0 raw33196; decide +kernel
      have hl : raw33196step0Labels = raw33196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33196 raw33196Labels permutation160 permutation7
    mixedMoment B raw33196step0 raw33196step0Labels = mixedMoment B raw33196step1 raw33196step1Labels := by
      have ha : raw33196step1 = -raw33196step0 := by apply Matrix.ext; change ∀ i j, raw33196step1 i j = -(raw33196step0 i j); unfold raw33196step1 raw33196step0; decide +kernel
      have hl : raw33196step1Labels = raw33196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33196step1 raw33196step1Labels = mixedMoment B raw33196step2 raw33196step2Labels := by
      have ha : raw33196step2 = raw33196step1 := by apply Matrix.ext; unfold raw33196step2 raw33196step1; decide +kernel
      have hl : raw33196step1Labels = labelEmbedding1 ∘ raw33196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33196step1 raw33196step1Labels raw33196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

theorem canonical33197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33197 raw33197Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw33197 raw33197Labels = mixedMoment B raw33197step0 raw33197step0Labels := by
      have hz : ∀ j, raw33197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33197step0 = (fun i j => raw33197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33197step0 raw33197; decide +kernel
      have hl : raw33197step0Labels = raw33197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33197 raw33197Labels permutation434 hz
    mixedMoment B raw33197step0 raw33197step0Labels = mixedMoment B raw33197step1 raw33197step1Labels := by
      have ha : raw33197step1 = (fun i j => raw33197step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33197step1 raw33197step0; decide +kernel
      have hl : raw33197step1Labels = raw33197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33197step0 raw33197step0Labels permutation34 permutation7
    mixedMoment B raw33197step1 raw33197step1Labels = mixedMoment B raw33197step2 raw33197step2Labels := by
      have ha : raw33197step2 = -raw33197step1 := by apply Matrix.ext; change ∀ i j, raw33197step2 i j = -(raw33197step1 i j); unfold raw33197step2 raw33197step1; decide +kernel
      have hl : raw33197step2Labels = raw33197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33197step2 raw33197step2Labels = mixedMoment B raw33197step3 raw33197step3Labels := by
      have ha : raw33197step3 = raw33197step2 := by apply Matrix.ext; unfold raw33197step3 raw33197step2; decide +kernel
      have hl : raw33197step2Labels = labelEmbedding1 ∘ raw33197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33197step2 raw33197step2Labels raw33197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical33198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33198 raw33198Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw33198 raw33198Labels = mixedMoment B raw33198step0 raw33198step0Labels := by
      have hz : ∀ j, raw33198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33198step0 = (fun i j => raw33198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33198step0 raw33198; decide +kernel
      have hl : raw33198step0Labels = raw33198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33198 raw33198Labels permutation520 hz
    mixedMoment B raw33198step0 raw33198step0Labels = mixedMoment B raw33198step1 raw33198step1Labels := by
      have ha : raw33198step1 = (fun i j => raw33198step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33198step1 raw33198step0; decide +kernel
      have hl : raw33198step1Labels = raw33198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33198step0 raw33198step0Labels permutation34 permutation7
    mixedMoment B raw33198step1 raw33198step1Labels = mixedMoment B raw33198step2 raw33198step2Labels := by
      have ha : raw33198step2 = -raw33198step1 := by apply Matrix.ext; change ∀ i j, raw33198step2 i j = -(raw33198step1 i j); unfold raw33198step2 raw33198step1; decide +kernel
      have hl : raw33198step2Labels = raw33198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33198step2 raw33198step2Labels = mixedMoment B raw33198step3 raw33198step3Labels := by
      have ha : raw33198step3 = raw33198step2 := by apply Matrix.ext; unfold raw33198step3 raw33198step2; decide +kernel
      have hl : raw33198step2Labels = labelEmbedding1 ∘ raw33198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33198step2 raw33198step2Labels raw33198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical260
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33324 raw33324Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw33324 raw33324Labels = mixedMoment B raw33324step0 raw33324step0Labels := by
      have hz : ∀ j, raw33324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33324step0 = (fun i j => raw33324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33324step0 raw33324; decide +kernel
      have hl : raw33324step0Labels = raw33324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33324 raw33324Labels permutation346 hz
    mixedMoment B raw33324step0 raw33324step0Labels = mixedMoment B raw33324step1 raw33324step1Labels := by
      have ha : raw33324step1 = (fun i j => raw33324step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33324step1 raw33324step0; decide +kernel
      have hl : raw33324step1Labels = raw33324step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33324step0 raw33324step0Labels permutation145 permutation7
    mixedMoment B raw33324step1 raw33324step1Labels = mixedMoment B raw33324step2 raw33324step2Labels := by
      have ha : raw33324step2 = raw33324step1 := by apply Matrix.ext; unfold raw33324step2 raw33324step1; decide +kernel
      have hl : raw33324step1Labels = labelEmbedding1 ∘ raw33324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33324step1 raw33324step1Labels raw33324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical33325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33325 raw33325Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw33325 raw33325Labels = mixedMoment B raw33325step0 raw33325step0Labels := by
      have ha : raw33325step0 = (fun i j => raw33325 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33325step0 raw33325; decide +kernel
      have hl : raw33325step0Labels = raw33325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33325 raw33325Labels permutation664 permutation7
    mixedMoment B raw33325step0 raw33325step0Labels = mixedMoment B raw33325step1 raw33325step1Labels := by
      have ha : raw33325step1 = raw33325step0 := by apply Matrix.ext; unfold raw33325step1 raw33325step0; decide +kernel
      have hl : raw33325step0Labels = labelEmbedding1 ∘ raw33325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33325step0 raw33325step0Labels raw33325step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical33326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33326 raw33326Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw33326 raw33326Labels = mixedMoment B raw33326step0 raw33326step0Labels := by
      have hz : ∀ j, raw33326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33326step0 = (fun i j => raw33326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33326step0 raw33326; decide +kernel
      have hl : raw33326step0Labels = raw33326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33326 raw33326Labels permutation520 hz
    mixedMoment B raw33326step0 raw33326step0Labels = mixedMoment B raw33326step1 raw33326step1Labels := by
      have hz : ∀ j, raw33326step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33326step1 = (fun i j => raw33326step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33326step1 raw33326step0; decide +kernel
      have hl : raw33326step1Labels = raw33326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33326step0 raw33326step0Labels permutation80 hz
    mixedMoment B raw33326step1 raw33326step1Labels = mixedMoment B raw33326step2 raw33326step2Labels := by
      have ha : raw33326step2 = (fun i j => raw33326step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33326step2 raw33326step1; decide +kernel
      have hl : raw33326step2Labels = raw33326step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33326step1 raw33326step1Labels permutation31 permutation7
    mixedMoment B raw33326step2 raw33326step2Labels = mixedMoment B raw33326step3 raw33326step3Labels := by
      have ha : raw33326step3 = raw33326step2 := by apply Matrix.ext; unfold raw33326step3 raw33326step2; decide +kernel
      have hl : raw33326step2Labels = labelEmbedding1 ∘ raw33326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33326step2 raw33326step2Labels raw33326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical33327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33327 raw33327Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw33327 raw33327Labels = mixedMoment B raw33327step0 raw33327step0Labels := by
      have hz : ∀ j, raw33327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33327step0 = (fun i j => raw33327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33327step0 raw33327; decide +kernel
      have hl : raw33327step0Labels = raw33327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33327 raw33327Labels permutation346 hz
    mixedMoment B raw33327step0 raw33327step0Labels = mixedMoment B raw33327step1 raw33327step1Labels := by
      have ha : raw33327step1 = (fun i j => raw33327step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33327step1 raw33327step0; decide +kernel
      have hl : raw33327step1Labels = raw33327step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33327step0 raw33327step0Labels permutation145 permutation7
    mixedMoment B raw33327step1 raw33327step1Labels = mixedMoment B raw33327step2 raw33327step2Labels := by
      have ha : raw33327step2 = raw33327step1 := by apply Matrix.ext; unfold raw33327step2 raw33327step1; decide +kernel
      have hl : raw33327step1Labels = labelEmbedding1 ∘ raw33327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33327step1 raw33327step1Labels raw33327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical33328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33328 raw33328Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw33328 raw33328Labels = mixedMoment B raw33328step0 raw33328step0Labels := by
      have hz : ∀ j, raw33328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33328step0 = (fun i j => raw33328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33328step0 raw33328; decide +kernel
      have hl : raw33328step0Labels = raw33328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33328 raw33328Labels permutation346 hz
    mixedMoment B raw33328step0 raw33328step0Labels = mixedMoment B raw33328step1 raw33328step1Labels := by
      have ha : raw33328step1 = (fun i j => raw33328step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33328step1 raw33328step0; decide +kernel
      have hl : raw33328step1Labels = raw33328step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33328step0 raw33328step0Labels permutation145 permutation7
    mixedMoment B raw33328step1 raw33328step1Labels = mixedMoment B raw33328step2 raw33328step2Labels := by
      have ha : raw33328step2 = raw33328step1 := by apply Matrix.ext; unfold raw33328step2 raw33328step1; decide +kernel
      have hl : raw33328step1Labels = labelEmbedding1 ∘ raw33328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33328step1 raw33328step1Labels raw33328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical33329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33329 raw33329Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw33329 raw33329Labels = mixedMoment B raw33329step0 raw33329step0Labels := by
      have ha : raw33329step0 = (fun i j => raw33329 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33329step0 raw33329; decide +kernel
      have hl : raw33329step0Labels = raw33329Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33329 raw33329Labels permutation664 permutation7
    mixedMoment B raw33329step0 raw33329step0Labels = mixedMoment B raw33329step1 raw33329step1Labels := by
      have ha : raw33329step1 = raw33329step0 := by apply Matrix.ext; unfold raw33329step1 raw33329step0; decide +kernel
      have hl : raw33329step0Labels = labelEmbedding1 ∘ raw33329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33329step0 raw33329step0Labels raw33329step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical33330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33330 raw33330Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw33330 raw33330Labels = mixedMoment B raw33330step0 raw33330step0Labels := by
      have hz : ∀ j, raw33330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33330step0 = (fun i j => raw33330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33330step0 raw33330; decide +kernel
      have hl : raw33330step0Labels = raw33330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33330 raw33330Labels permutation520 hz
    mixedMoment B raw33330step0 raw33330step0Labels = mixedMoment B raw33330step1 raw33330step1Labels := by
      have hz : ∀ j, raw33330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33330step1 = (fun i j => raw33330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33330step1 raw33330step0; decide +kernel
      have hl : raw33330step1Labels = raw33330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33330step0 raw33330step0Labels permutation80 hz
    mixedMoment B raw33330step1 raw33330step1Labels = mixedMoment B raw33330step2 raw33330step2Labels := by
      have ha : raw33330step2 = (fun i j => raw33330step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33330step2 raw33330step1; decide +kernel
      have hl : raw33330step2Labels = raw33330step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33330step1 raw33330step1Labels permutation31 permutation7
    mixedMoment B raw33330step2 raw33330step2Labels = mixedMoment B raw33330step3 raw33330step3Labels := by
      have ha : raw33330step3 = raw33330step2 := by apply Matrix.ext; unfold raw33330step3 raw33330step2; decide +kernel
      have hl : raw33330step2Labels = labelEmbedding1 ∘ raw33330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33330step2 raw33330step2Labels raw33330step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical33331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33331 raw33331Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw33331 raw33331Labels = mixedMoment B raw33331step0 raw33331step0Labels := by
      have hz : ∀ j, raw33331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33331step0 = (fun i j => raw33331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33331step0 raw33331; decide +kernel
      have hl : raw33331step0Labels = raw33331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33331 raw33331Labels permutation346 hz
    mixedMoment B raw33331step0 raw33331step0Labels = mixedMoment B raw33331step1 raw33331step1Labels := by
      have ha : raw33331step1 = (fun i j => raw33331step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33331step1 raw33331step0; decide +kernel
      have hl : raw33331step1Labels = raw33331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33331step0 raw33331step0Labels permutation145 permutation7
    mixedMoment B raw33331step1 raw33331step1Labels = mixedMoment B raw33331step2 raw33331step2Labels := by
      have ha : raw33331step2 = raw33331step1 := by apply Matrix.ext; unfold raw33331step2 raw33331step1; decide +kernel
      have hl : raw33331step1Labels = labelEmbedding1 ∘ raw33331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33331step1 raw33331step1Labels raw33331step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical33332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33332 raw33332Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw33332 raw33332Labels = mixedMoment B raw33332step0 raw33332step0Labels := by
      have ha : raw33332step0 = (fun i j => raw33332 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33332step0 raw33332; decide +kernel
      have hl : raw33332step0Labels = raw33332Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33332 raw33332Labels permutation640 permutation7
    mixedMoment B raw33332step0 raw33332step0Labels = mixedMoment B raw33332step1 raw33332step1Labels := by
      have ha : raw33332step1 = raw33332step0 := by apply Matrix.ext; unfold raw33332step1 raw33332step0; decide +kernel
      have hl : raw33332step0Labels = labelEmbedding1 ∘ raw33332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33332step0 raw33332step0Labels raw33332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

theorem canonical33333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33333 raw33333Labels = mixedMoment B node2689 node2689Labels := by
  calc
    mixedMoment B raw33333 raw33333Labels = mixedMoment B raw33333step0 raw33333step0Labels := by
      have ha : raw33333step0 = (fun i j => raw33333 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33333step0 raw33333; decide +kernel
      have hl : raw33333step0Labels = raw33333Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33333 raw33333Labels permutation640 permutation7
    mixedMoment B raw33333step0 raw33333step0Labels = mixedMoment B raw33333step1 raw33333step1Labels := by
      have ha : raw33333step1 = raw33333step0 := by apply Matrix.ext; unfold raw33333step1 raw33333step0; decide +kernel
      have hl : raw33333step0Labels = labelEmbedding1 ∘ raw33333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33333step0 raw33333step0Labels raw33333step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2689 node2689Labels := by rfl

theorem canonical33334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33334 raw33334Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw33334 raw33334Labels = mixedMoment B raw33334step0 raw33334step0Labels := by
      have hz : ∀ j, raw33334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33334step0 = (fun i j => raw33334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33334step0 raw33334; decide +kernel
      have hl : raw33334step0Labels = raw33334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33334 raw33334Labels permutation520 hz
    mixedMoment B raw33334step0 raw33334step0Labels = mixedMoment B raw33334step1 raw33334step1Labels := by
      have ha : raw33334step1 = (fun i j => raw33334step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33334step1 raw33334step0; decide +kernel
      have hl : raw33334step1Labels = raw33334step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33334step0 raw33334step0Labels permutation145 permutation7
    mixedMoment B raw33334step1 raw33334step1Labels = mixedMoment B raw33334step2 raw33334step2Labels := by
      have ha : raw33334step2 = raw33334step1 := by apply Matrix.ext; unfold raw33334step2 raw33334step1; decide +kernel
      have hl : raw33334step1Labels = labelEmbedding1 ∘ raw33334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33334step1 raw33334step1Labels raw33334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical33335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33335 raw33335Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw33335 raw33335Labels = mixedMoment B raw33335step0 raw33335step0Labels := by
      have ha : raw33335step0 = (fun i j => raw33335 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33335step0 raw33335; decide +kernel
      have hl : raw33335step0Labels = raw33335Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33335 raw33335Labels permutation640 permutation7
    mixedMoment B raw33335step0 raw33335step0Labels = mixedMoment B raw33335step1 raw33335step1Labels := by
      have ha : raw33335step1 = raw33335step0 := by apply Matrix.ext; unfold raw33335step1 raw33335step0; decide +kernel
      have hl : raw33335step0Labels = labelEmbedding1 ∘ raw33335step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33335step0 raw33335step0Labels raw33335step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

theorem canonical33336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33336 raw33336Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw33336 raw33336Labels = mixedMoment B raw33336step0 raw33336step0Labels := by
      have hz : ∀ j, raw33336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33336step0 = (fun i j => raw33336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33336step0 raw33336; decide +kernel
      have hl : raw33336step0Labels = raw33336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33336 raw33336Labels permutation346 hz
    mixedMoment B raw33336step0 raw33336step0Labels = mixedMoment B raw33336step1 raw33336step1Labels := by
      have ha : raw33336step1 = (fun i j => raw33336step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33336step1 raw33336step0; decide +kernel
      have hl : raw33336step1Labels = raw33336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33336step0 raw33336step0Labels permutation145 permutation7
    mixedMoment B raw33336step1 raw33336step1Labels = mixedMoment B raw33336step2 raw33336step2Labels := by
      have ha : raw33336step2 = raw33336step1 := by apply Matrix.ext; unfold raw33336step2 raw33336step1; decide +kernel
      have hl : raw33336step1Labels = labelEmbedding1 ∘ raw33336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33336step1 raw33336step1Labels raw33336step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical33337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33337 raw33337Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw33337 raw33337Labels = mixedMoment B raw33337step0 raw33337step0Labels := by
      have hz : ∀ j, raw33337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33337step0 = (fun i j => raw33337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33337step0 raw33337; decide +kernel
      have hl : raw33337step0Labels = raw33337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33337 raw33337Labels permutation346 hz
    mixedMoment B raw33337step0 raw33337step0Labels = mixedMoment B raw33337step1 raw33337step1Labels := by
      have ha : raw33337step1 = (fun i j => raw33337step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33337step1 raw33337step0; decide +kernel
      have hl : raw33337step1Labels = raw33337step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33337step0 raw33337step0Labels permutation145 permutation7
    mixedMoment B raw33337step1 raw33337step1Labels = mixedMoment B raw33337step2 raw33337step2Labels := by
      have ha : raw33337step2 = raw33337step1 := by apply Matrix.ext; unfold raw33337step2 raw33337step1; decide +kernel
      have hl : raw33337step1Labels = labelEmbedding1 ∘ raw33337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33337step1 raw33337step1Labels raw33337step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical33338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33338 raw33338Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw33338 raw33338Labels = mixedMoment B raw33338step0 raw33338step0Labels := by
      have ha : raw33338step0 = (fun i j => raw33338 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33338step0 raw33338; decide +kernel
      have hl : raw33338step0Labels = raw33338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33338 raw33338Labels permutation664 permutation7
    mixedMoment B raw33338step0 raw33338step0Labels = mixedMoment B raw33338step1 raw33338step1Labels := by
      have ha : raw33338step1 = raw33338step0 := by apply Matrix.ext; unfold raw33338step1 raw33338step0; decide +kernel
      have hl : raw33338step0Labels = labelEmbedding1 ∘ raw33338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33338step0 raw33338step0Labels raw33338step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical33339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33339 raw33339Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw33339 raw33339Labels = mixedMoment B raw33339step0 raw33339step0Labels := by
      have hz : ∀ j, raw33339 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33339step0 = (fun i j => raw33339 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33339step0 raw33339; decide +kernel
      have hl : raw33339step0Labels = raw33339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33339 raw33339Labels permutation520 hz
    mixedMoment B raw33339step0 raw33339step0Labels = mixedMoment B raw33339step1 raw33339step1Labels := by
      have hz : ∀ j, raw33339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33339step1 = (fun i j => raw33339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33339step1 raw33339step0; decide +kernel
      have hl : raw33339step1Labels = raw33339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33339step0 raw33339step0Labels permutation80 hz
    mixedMoment B raw33339step1 raw33339step1Labels = mixedMoment B raw33339step2 raw33339step2Labels := by
      have ha : raw33339step2 = (fun i j => raw33339step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33339step2 raw33339step1; decide +kernel
      have hl : raw33339step2Labels = raw33339step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33339step1 raw33339step1Labels permutation31 permutation7
    mixedMoment B raw33339step2 raw33339step2Labels = mixedMoment B raw33339step3 raw33339step3Labels := by
      have ha : raw33339step3 = raw33339step2 := by apply Matrix.ext; unfold raw33339step3 raw33339step2; decide +kernel
      have hl : raw33339step2Labels = labelEmbedding1 ∘ raw33339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33339step2 raw33339step2Labels raw33339step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical33340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33340 raw33340Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw33340 raw33340Labels = mixedMoment B raw33340step0 raw33340step0Labels := by
      have hz : ∀ j, raw33340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33340step0 = (fun i j => raw33340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33340step0 raw33340; decide +kernel
      have hl : raw33340step0Labels = raw33340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33340 raw33340Labels permutation346 hz
    mixedMoment B raw33340step0 raw33340step0Labels = mixedMoment B raw33340step1 raw33340step1Labels := by
      have ha : raw33340step1 = (fun i j => raw33340step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33340step1 raw33340step0; decide +kernel
      have hl : raw33340step1Labels = raw33340step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33340step0 raw33340step0Labels permutation145 permutation7
    mixedMoment B raw33340step1 raw33340step1Labels = mixedMoment B raw33340step2 raw33340step2Labels := by
      have ha : raw33340step2 = raw33340step1 := by apply Matrix.ext; unfold raw33340step2 raw33340step1; decide +kernel
      have hl : raw33340step1Labels = labelEmbedding1 ∘ raw33340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33340step1 raw33340step1Labels raw33340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical33341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33341 raw33341Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw33341 raw33341Labels = mixedMoment B raw33341step0 raw33341step0Labels := by
      have hz : ∀ j, raw33341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33341step0 = (fun i j => raw33341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33341step0 raw33341; decide +kernel
      have hl : raw33341step0Labels = raw33341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33341 raw33341Labels permutation346 hz
    mixedMoment B raw33341step0 raw33341step0Labels = mixedMoment B raw33341step1 raw33341step1Labels := by
      have ha : raw33341step1 = (fun i j => raw33341step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33341step1 raw33341step0; decide +kernel
      have hl : raw33341step1Labels = raw33341step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33341step0 raw33341step0Labels permutation151 permutation7
    mixedMoment B raw33341step1 raw33341step1Labels = mixedMoment B raw33341step2 raw33341step2Labels := by
      have ha : raw33341step2 = raw33341step1 := by apply Matrix.ext; unfold raw33341step2 raw33341step1; decide +kernel
      have hl : raw33341step1Labels = labelEmbedding1 ∘ raw33341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33341step1 raw33341step1Labels raw33341step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical33342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33342 raw33342Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw33342 raw33342Labels = mixedMoment B raw33342step0 raw33342step0Labels := by
      have hz : ∀ j, raw33342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33342step0 = (fun i j => raw33342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33342step0 raw33342; decide +kernel
      have hl : raw33342step0Labels = raw33342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33342 raw33342Labels permutation346 hz
    mixedMoment B raw33342step0 raw33342step0Labels = mixedMoment B raw33342step1 raw33342step1Labels := by
      have ha : raw33342step1 = (fun i j => raw33342step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33342step1 raw33342step0; decide +kernel
      have hl : raw33342step1Labels = raw33342step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33342step0 raw33342step0Labels permutation151 permutation7
    mixedMoment B raw33342step1 raw33342step1Labels = mixedMoment B raw33342step2 raw33342step2Labels := by
      have ha : raw33342step2 = raw33342step1 := by apply Matrix.ext; unfold raw33342step2 raw33342step1; decide +kernel
      have hl : raw33342step1Labels = labelEmbedding1 ∘ raw33342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33342step1 raw33342step1Labels raw33342step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical33343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33343 raw33343Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw33343 raw33343Labels = mixedMoment B raw33343step0 raw33343step0Labels := by
      have ha : raw33343step0 = (fun i j => raw33343 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33343step0 raw33343; decide +kernel
      have hl : raw33343step0Labels = raw33343Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33343 raw33343Labels permutation688 permutation7
    mixedMoment B raw33343step0 raw33343step0Labels = mixedMoment B raw33343step1 raw33343step1Labels := by
      have ha : raw33343step1 = raw33343step0 := by apply Matrix.ext; unfold raw33343step1 raw33343step0; decide +kernel
      have hl : raw33343step0Labels = labelEmbedding1 ∘ raw33343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33343step0 raw33343step0Labels raw33343step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical33344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33344 raw33344Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw33344 raw33344Labels = mixedMoment B raw33344step0 raw33344step0Labels := by
      have hz : ∀ j, raw33344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33344step0 = (fun i j => raw33344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33344step0 raw33344; decide +kernel
      have hl : raw33344step0Labels = raw33344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33344 raw33344Labels permutation346 hz
    mixedMoment B raw33344step0 raw33344step0Labels = mixedMoment B raw33344step1 raw33344step1Labels := by
      have ha : raw33344step1 = (fun i j => raw33344step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33344step1 raw33344step0; decide +kernel
      have hl : raw33344step1Labels = raw33344step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33344step0 raw33344step0Labels permutation151 permutation7
    mixedMoment B raw33344step1 raw33344step1Labels = mixedMoment B raw33344step2 raw33344step2Labels := by
      have ha : raw33344step2 = raw33344step1 := by apply Matrix.ext; unfold raw33344step2 raw33344step1; decide +kernel
      have hl : raw33344step1Labels = labelEmbedding1 ∘ raw33344step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33344step1 raw33344step1Labels raw33344step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical33345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33345 raw33345Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw33345 raw33345Labels = mixedMoment B raw33345step0 raw33345step0Labels := by
      have hz : ∀ j, raw33345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33345step0 = (fun i j => raw33345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33345step0 raw33345; decide +kernel
      have hl : raw33345step0Labels = raw33345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33345 raw33345Labels permutation434 hz
    mixedMoment B raw33345step0 raw33345step0Labels = mixedMoment B raw33345step1 raw33345step1Labels := by
      have hz : ∀ j, raw33345step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33345step1 = (fun i j => raw33345step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33345step1 raw33345step0; decide +kernel
      have hl : raw33345step1Labels = raw33345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33345step0 raw33345step0Labels permutation80 hz
    mixedMoment B raw33345step1 raw33345step1Labels = mixedMoment B raw33345step2 raw33345step2Labels := by
      have ha : raw33345step2 = (fun i j => raw33345step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33345step2 raw33345step1; decide +kernel
      have hl : raw33345step2Labels = raw33345step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33345step1 raw33345step1Labels permutation31 permutation7
    mixedMoment B raw33345step2 raw33345step2Labels = mixedMoment B raw33345step3 raw33345step3Labels := by
      have ha : raw33345step3 = raw33345step2 := by apply Matrix.ext; unfold raw33345step3 raw33345step2; decide +kernel
      have hl : raw33345step2Labels = labelEmbedding1 ∘ raw33345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33345step2 raw33345step2Labels raw33345step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33489 raw33489Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw33489 raw33489Labels = mixedMoment B raw33489step0 raw33489step0Labels := by
      have hz : ∀ j, raw33489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33489step0 = (fun i j => raw33489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33489step0 raw33489; decide +kernel
      have hl : raw33489step0Labels = raw33489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33489 raw33489Labels permutation346 hz
    mixedMoment B raw33489step0 raw33489step0Labels = mixedMoment B raw33489step1 raw33489step1Labels := by
      have ha : raw33489step1 = (fun i j => raw33489step0 (permutation64 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33489step1 raw33489step0; decide +kernel
      have hl : raw33489step1Labels = raw33489step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33489step0 raw33489step0Labels permutation64 permutation5
    mixedMoment B raw33489step1 raw33489step1Labels = mixedMoment B raw33489step2 raw33489step2Labels := by
      have ha : raw33489step2 = -raw33489step1 := by apply Matrix.ext; change ∀ i j, raw33489step2 i j = -(raw33489step1 i j); unfold raw33489step2 raw33489step1; decide +kernel
      have hl : raw33489step2Labels = raw33489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33489step2 raw33489step2Labels = mixedMoment B raw33489step3 raw33489step3Labels := by
      have ha : raw33489step3 = raw33489step2 := by apply Matrix.ext; unfold raw33489step3 raw33489step2; decide +kernel
      have hl : raw33489step2Labels = labelEmbedding1 ∘ raw33489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33489step2 raw33489step2Labels raw33489step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

theorem canonical33490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33490 raw33490Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw33490 raw33490Labels = mixedMoment B raw33490step0 raw33490step0Labels := by
      have ha : raw33490step0 = (fun i j => raw33490 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33490step0 raw33490; decide +kernel
      have hl : raw33490step0Labels = raw33490Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33490 raw33490Labels permutation194 permutation7
    mixedMoment B raw33490step0 raw33490step0Labels = mixedMoment B raw33490step1 raw33490step1Labels := by
      have ha : raw33490step1 = -raw33490step0 := by apply Matrix.ext; change ∀ i j, raw33490step1 i j = -(raw33490step0 i j); unfold raw33490step1 raw33490step0; decide +kernel
      have hl : raw33490step1Labels = raw33490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33490step1 raw33490step1Labels = mixedMoment B raw33490step2 raw33490step2Labels := by
      have ha : raw33490step2 = raw33490step1 := by apply Matrix.ext; unfold raw33490step2 raw33490step1; decide +kernel
      have hl : raw33490step1Labels = labelEmbedding1 ∘ raw33490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33490step1 raw33490step1Labels raw33490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical33491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33491 raw33491Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw33491 raw33491Labels = mixedMoment B raw33491step0 raw33491step0Labels := by
      have hz : ∀ j, raw33491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33491step0 = (fun i j => raw33491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33491step0 raw33491; decide +kernel
      have hl : raw33491step0Labels = raw33491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33491 raw33491Labels permutation346 hz
    mixedMoment B raw33491step0 raw33491step0Labels = mixedMoment B raw33491step1 raw33491step1Labels := by
      have ha : raw33491step1 = (fun i j => raw33491step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33491step1 raw33491step0; decide +kernel
      have hl : raw33491step1Labels = raw33491step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33491step0 raw33491step0Labels permutation50 permutation7
    mixedMoment B raw33491step1 raw33491step1Labels = mixedMoment B raw33491step2 raw33491step2Labels := by
      have ha : raw33491step2 = -raw33491step1 := by apply Matrix.ext; change ∀ i j, raw33491step2 i j = -(raw33491step1 i j); unfold raw33491step2 raw33491step1; decide +kernel
      have hl : raw33491step2Labels = raw33491step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33491step2 raw33491step2Labels = mixedMoment B raw33491step3 raw33491step3Labels := by
      have ha : raw33491step3 = raw33491step2 := by apply Matrix.ext; unfold raw33491step3 raw33491step2; decide +kernel
      have hl : raw33491step2Labels = labelEmbedding1 ∘ raw33491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33491step2 raw33491step2Labels raw33491step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical33492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33492 raw33492Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw33492 raw33492Labels = mixedMoment B raw33492step0 raw33492step0Labels := by
      have hz : ∀ j, raw33492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33492step0 = (fun i j => raw33492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33492step0 raw33492; decide +kernel
      have hl : raw33492step0Labels = raw33492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33492 raw33492Labels permutation346 hz
    mixedMoment B raw33492step0 raw33492step0Labels = mixedMoment B raw33492step1 raw33492step1Labels := by
      have ha : raw33492step1 = (fun i j => raw33492step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33492step1 raw33492step0; decide +kernel
      have hl : raw33492step1Labels = raw33492step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33492step0 raw33492step0Labels permutation51 permutation7
    mixedMoment B raw33492step1 raw33492step1Labels = mixedMoment B raw33492step2 raw33492step2Labels := by
      have ha : raw33492step2 = -raw33492step1 := by apply Matrix.ext; change ∀ i j, raw33492step2 i j = -(raw33492step1 i j); unfold raw33492step2 raw33492step1; decide +kernel
      have hl : raw33492step2Labels = raw33492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33492step2 raw33492step2Labels = mixedMoment B raw33492step3 raw33492step3Labels := by
      have ha : raw33492step3 = raw33492step2 := by apply Matrix.ext; unfold raw33492step3 raw33492step2; decide +kernel
      have hl : raw33492step2Labels = labelEmbedding1 ∘ raw33492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33492step2 raw33492step2Labels raw33492step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical33493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33493 raw33493Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw33493 raw33493Labels = mixedMoment B raw33493step0 raw33493step0Labels := by
      have hz : ∀ j, raw33493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33493step0 = (fun i j => raw33493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33493step0 raw33493; decide +kernel
      have hl : raw33493step0Labels = raw33493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33493 raw33493Labels permutation346 hz
    mixedMoment B raw33493step0 raw33493step0Labels = mixedMoment B raw33493step1 raw33493step1Labels := by
      have ha : raw33493step1 = (fun i j => raw33493step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33493step1 raw33493step0; decide +kernel
      have hl : raw33493step1Labels = raw33493step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33493step0 raw33493step0Labels permutation50 permutation7
    mixedMoment B raw33493step1 raw33493step1Labels = mixedMoment B raw33493step2 raw33493step2Labels := by
      have ha : raw33493step2 = -raw33493step1 := by apply Matrix.ext; change ∀ i j, raw33493step2 i j = -(raw33493step1 i j); unfold raw33493step2 raw33493step1; decide +kernel
      have hl : raw33493step2Labels = raw33493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33493step2 raw33493step2Labels = mixedMoment B raw33493step3 raw33493step3Labels := by
      have ha : raw33493step3 = raw33493step2 := by apply Matrix.ext; unfold raw33493step3 raw33493step2; decide +kernel
      have hl : raw33493step2Labels = labelEmbedding1 ∘ raw33493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33493step2 raw33493step2Labels raw33493step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical33494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33494 raw33494Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw33494 raw33494Labels = mixedMoment B raw33494step0 raw33494step0Labels := by
      have hz : ∀ j, raw33494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33494step0 = (fun i j => raw33494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33494step0 raw33494; decide +kernel
      have hl : raw33494step0Labels = raw33494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33494 raw33494Labels permutation346 hz
    mixedMoment B raw33494step0 raw33494step0Labels = mixedMoment B raw33494step1 raw33494step1Labels := by
      have ha : raw33494step1 = (fun i j => raw33494step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33494step1 raw33494step0; decide +kernel
      have hl : raw33494step1Labels = raw33494step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33494step0 raw33494step0Labels permutation50 permutation7
    mixedMoment B raw33494step1 raw33494step1Labels = mixedMoment B raw33494step2 raw33494step2Labels := by
      have ha : raw33494step2 = -raw33494step1 := by apply Matrix.ext; change ∀ i j, raw33494step2 i j = -(raw33494step1 i j); unfold raw33494step2 raw33494step1; decide +kernel
      have hl : raw33494step2Labels = raw33494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33494step2 raw33494step2Labels = mixedMoment B raw33494step3 raw33494step3Labels := by
      have ha : raw33494step3 = raw33494step2 := by apply Matrix.ext; unfold raw33494step3 raw33494step2; decide +kernel
      have hl : raw33494step2Labels = labelEmbedding1 ∘ raw33494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33494step2 raw33494step2Labels raw33494step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical33495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33495 raw33495Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw33495 raw33495Labels = mixedMoment B raw33495step0 raw33495step0Labels := by
      have ha : raw33495step0 = (fun i j => raw33495 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33495step0 raw33495; decide +kernel
      have hl : raw33495step0Labels = raw33495Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33495 raw33495Labels permutation194 permutation7
    mixedMoment B raw33495step0 raw33495step0Labels = mixedMoment B raw33495step1 raw33495step1Labels := by
      have ha : raw33495step1 = -raw33495step0 := by apply Matrix.ext; change ∀ i j, raw33495step1 i j = -(raw33495step0 i j); unfold raw33495step1 raw33495step0; decide +kernel
      have hl : raw33495step1Labels = raw33495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33495step1 raw33495step1Labels = mixedMoment B raw33495step2 raw33495step2Labels := by
      have ha : raw33495step2 = raw33495step1 := by apply Matrix.ext; unfold raw33495step2 raw33495step1; decide +kernel
      have hl : raw33495step1Labels = labelEmbedding1 ∘ raw33495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33495step1 raw33495step1Labels raw33495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

theorem canonical33496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33496 raw33496Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw33496 raw33496Labels = mixedMoment B raw33496step0 raw33496step0Labels := by
      have ha : raw33496step0 = (fun i j => raw33496 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33496step0 raw33496; decide +kernel
      have hl : raw33496step0Labels = raw33496Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33496 raw33496Labels permutation194 permutation7
    mixedMoment B raw33496step0 raw33496step0Labels = mixedMoment B raw33496step1 raw33496step1Labels := by
      have ha : raw33496step1 = -raw33496step0 := by apply Matrix.ext; change ∀ i j, raw33496step1 i j = -(raw33496step0 i j); unfold raw33496step1 raw33496step0; decide +kernel
      have hl : raw33496step1Labels = raw33496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33496step1 raw33496step1Labels = mixedMoment B raw33496step2 raw33496step2Labels := by
      have ha : raw33496step2 = raw33496step1 := by apply Matrix.ext; unfold raw33496step2 raw33496step1; decide +kernel
      have hl : raw33496step1Labels = labelEmbedding1 ∘ raw33496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33496step1 raw33496step1Labels raw33496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical33497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33497 raw33497Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw33497 raw33497Labels = mixedMoment B raw33497step0 raw33497step0Labels := by
      have ha : raw33497step0 = (fun i j => raw33497 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33497step0 raw33497; decide +kernel
      have hl : raw33497step0Labels = raw33497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33497 raw33497Labels permutation195 permutation7
    mixedMoment B raw33497step0 raw33497step0Labels = mixedMoment B raw33497step1 raw33497step1Labels := by
      have ha : raw33497step1 = -raw33497step0 := by apply Matrix.ext; change ∀ i j, raw33497step1 i j = -(raw33497step0 i j); unfold raw33497step1 raw33497step0; decide +kernel
      have hl : raw33497step1Labels = raw33497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33497step1 raw33497step1Labels = mixedMoment B raw33497step2 raw33497step2Labels := by
      have ha : raw33497step2 = raw33497step1 := by apply Matrix.ext; unfold raw33497step2 raw33497step1; decide +kernel
      have hl : raw33497step1Labels = labelEmbedding1 ∘ raw33497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33497step1 raw33497step1Labels raw33497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical33498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33498 raw33498Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw33498 raw33498Labels = mixedMoment B raw33498step0 raw33498step0Labels := by
      have ha : raw33498step0 = (fun i j => raw33498 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33498step0 raw33498; decide +kernel
      have hl : raw33498step0Labels = raw33498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33498 raw33498Labels permutation194 permutation7
    mixedMoment B raw33498step0 raw33498step0Labels = mixedMoment B raw33498step1 raw33498step1Labels := by
      have ha : raw33498step1 = -raw33498step0 := by apply Matrix.ext; change ∀ i j, raw33498step1 i j = -(raw33498step0 i j); unfold raw33498step1 raw33498step0; decide +kernel
      have hl : raw33498step1Labels = raw33498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33498step1 raw33498step1Labels = mixedMoment B raw33498step2 raw33498step2Labels := by
      have ha : raw33498step2 = raw33498step1 := by apply Matrix.ext; unfold raw33498step2 raw33498step1; decide +kernel
      have hl : raw33498step1Labels = labelEmbedding1 ∘ raw33498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33498step1 raw33498step1Labels raw33498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical33499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33499 raw33499Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33499 raw33499Labels = mixedMoment B raw33499step0 raw33499step0Labels := by
      have hz : ∀ j, raw33499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33499step0 = (fun i j => raw33499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33499step0 raw33499; decide +kernel
      have hl : raw33499step0Labels = raw33499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33499 raw33499Labels permutation346 hz
    mixedMoment B raw33499step0 raw33499step0Labels = mixedMoment B raw33499step1 raw33499step1Labels := by
      have ha : raw33499step1 = (fun i j => raw33499step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33499step1 raw33499step0; decide +kernel
      have hl : raw33499step1Labels = raw33499step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33499step0 raw33499step0Labels permutation51 permutation7
    mixedMoment B raw33499step1 raw33499step1Labels = mixedMoment B raw33499step2 raw33499step2Labels := by
      have ha : raw33499step2 = -raw33499step1 := by apply Matrix.ext; change ∀ i j, raw33499step2 i j = -(raw33499step1 i j); unfold raw33499step2 raw33499step1; decide +kernel
      have hl : raw33499step2Labels = raw33499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33499step2 raw33499step2Labels = mixedMoment B raw33499step3 raw33499step3Labels := by
      have ha : raw33499step3 = raw33499step2 := by apply Matrix.ext; unfold raw33499step3 raw33499step2; decide +kernel
      have hl : raw33499step2Labels = labelEmbedding1 ∘ raw33499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33499step2 raw33499step2Labels raw33499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical33500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33500 raw33500Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33500 raw33500Labels = mixedMoment B raw33500step0 raw33500step0Labels := by
      have ha : raw33500step0 = (fun i j => raw33500 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33500step0 raw33500; decide +kernel
      have hl : raw33500step0Labels = raw33500Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33500 raw33500Labels permutation195 permutation7
    mixedMoment B raw33500step0 raw33500step0Labels = mixedMoment B raw33500step1 raw33500step1Labels := by
      have ha : raw33500step1 = -raw33500step0 := by apply Matrix.ext; change ∀ i j, raw33500step1 i j = -(raw33500step0 i j); unfold raw33500step1 raw33500step0; decide +kernel
      have hl : raw33500step1Labels = raw33500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33500step1 raw33500step1Labels = mixedMoment B raw33500step2 raw33500step2Labels := by
      have ha : raw33500step2 = raw33500step1 := by apply Matrix.ext; unfold raw33500step2 raw33500step1; decide +kernel
      have hl : raw33500step1Labels = labelEmbedding1 ∘ raw33500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33500step1 raw33500step1Labels raw33500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33501 raw33501Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33501 raw33501Labels = mixedMoment B raw33501step0 raw33501step0Labels := by
      have hz : ∀ j, raw33501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33501step0 = (fun i j => raw33501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33501step0 raw33501; decide +kernel
      have hl : raw33501step0Labels = raw33501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33501 raw33501Labels permutation346 hz
    mixedMoment B raw33501step0 raw33501step0Labels = mixedMoment B raw33501step1 raw33501step1Labels := by
      have ha : raw33501step1 = (fun i j => raw33501step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33501step1 raw33501step0; decide +kernel
      have hl : raw33501step1Labels = raw33501step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33501step0 raw33501step0Labels permutation51 permutation7
    mixedMoment B raw33501step1 raw33501step1Labels = mixedMoment B raw33501step2 raw33501step2Labels := by
      have ha : raw33501step2 = -raw33501step1 := by apply Matrix.ext; change ∀ i j, raw33501step2 i j = -(raw33501step1 i j); unfold raw33501step2 raw33501step1; decide +kernel
      have hl : raw33501step2Labels = raw33501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33501step2 raw33501step2Labels = mixedMoment B raw33501step3 raw33501step3Labels := by
      have ha : raw33501step3 = raw33501step2 := by apply Matrix.ext; unfold raw33501step3 raw33501step2; decide +kernel
      have hl : raw33501step2Labels = labelEmbedding1 ∘ raw33501step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33501step2 raw33501step2Labels raw33501step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical33502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33502 raw33502Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33502 raw33502Labels = mixedMoment B raw33502step0 raw33502step0Labels := by
      have hz : ∀ j, raw33502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33502step0 = (fun i j => raw33502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33502step0 raw33502; decide +kernel
      have hl : raw33502step0Labels = raw33502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33502 raw33502Labels permutation346 hz
    mixedMoment B raw33502step0 raw33502step0Labels = mixedMoment B raw33502step1 raw33502step1Labels := by
      have ha : raw33502step1 = (fun i j => raw33502step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33502step1 raw33502step0; decide +kernel
      have hl : raw33502step1Labels = raw33502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33502step0 raw33502step0Labels permutation51 permutation7
    mixedMoment B raw33502step1 raw33502step1Labels = mixedMoment B raw33502step2 raw33502step2Labels := by
      have ha : raw33502step2 = -raw33502step1 := by apply Matrix.ext; change ∀ i j, raw33502step2 i j = -(raw33502step1 i j); unfold raw33502step2 raw33502step1; decide +kernel
      have hl : raw33502step2Labels = raw33502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33502step2 raw33502step2Labels = mixedMoment B raw33502step3 raw33502step3Labels := by
      have ha : raw33502step3 = raw33502step2 := by apply Matrix.ext; unfold raw33502step3 raw33502step2; decide +kernel
      have hl : raw33502step2Labels = labelEmbedding1 ∘ raw33502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33502step2 raw33502step2Labels raw33502step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical33503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33503 raw33503Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33503 raw33503Labels = mixedMoment B raw33503step0 raw33503step0Labels := by
      have hz : ∀ j, raw33503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33503step0 = (fun i j => raw33503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33503step0 raw33503; decide +kernel
      have hl : raw33503step0Labels = raw33503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33503 raw33503Labels permutation346 hz
    mixedMoment B raw33503step0 raw33503step0Labels = mixedMoment B raw33503step1 raw33503step1Labels := by
      have ha : raw33503step1 = (fun i j => raw33503step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33503step1 raw33503step0; decide +kernel
      have hl : raw33503step1Labels = raw33503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33503step0 raw33503step0Labels permutation50 permutation7
    mixedMoment B raw33503step1 raw33503step1Labels = mixedMoment B raw33503step2 raw33503step2Labels := by
      have ha : raw33503step2 = -raw33503step1 := by apply Matrix.ext; change ∀ i j, raw33503step2 i j = -(raw33503step1 i j); unfold raw33503step2 raw33503step1; decide +kernel
      have hl : raw33503step2Labels = raw33503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33503step2 raw33503step2Labels = mixedMoment B raw33503step3 raw33503step3Labels := by
      have ha : raw33503step3 = raw33503step2 := by apply Matrix.ext; unfold raw33503step3 raw33503step2; decide +kernel
      have hl : raw33503step2Labels = labelEmbedding1 ∘ raw33503step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33503step2 raw33503step2Labels raw33503step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical33504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33504 raw33504Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33504 raw33504Labels = mixedMoment B raw33504step0 raw33504step0Labels := by
      have ha : raw33504step0 = (fun i j => raw33504 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33504step0 raw33504; decide +kernel
      have hl : raw33504step0Labels = raw33504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33504 raw33504Labels permutation194 permutation7
    mixedMoment B raw33504step0 raw33504step0Labels = mixedMoment B raw33504step1 raw33504step1Labels := by
      have ha : raw33504step1 = -raw33504step0 := by apply Matrix.ext; change ∀ i j, raw33504step1 i j = -(raw33504step0 i j); unfold raw33504step1 raw33504step0; decide +kernel
      have hl : raw33504step1Labels = raw33504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33504step1 raw33504step1Labels = mixedMoment B raw33504step2 raw33504step2Labels := by
      have ha : raw33504step2 = raw33504step1 := by apply Matrix.ext; unfold raw33504step2 raw33504step1; decide +kernel
      have hl : raw33504step1Labels = labelEmbedding1 ∘ raw33504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33504step1 raw33504step1Labels raw33504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33505 raw33505Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33505 raw33505Labels = mixedMoment B raw33505step0 raw33505step0Labels := by
      have hz : ∀ j, raw33505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33505step0 = (fun i j => raw33505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33505step0 raw33505; decide +kernel
      have hl : raw33505step0Labels = raw33505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33505 raw33505Labels permutation346 hz
    mixedMoment B raw33505step0 raw33505step0Labels = mixedMoment B raw33505step1 raw33505step1Labels := by
      have ha : raw33505step1 = (fun i j => raw33505step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33505step1 raw33505step0; decide +kernel
      have hl : raw33505step1Labels = raw33505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33505step0 raw33505step0Labels permutation50 permutation7
    mixedMoment B raw33505step1 raw33505step1Labels = mixedMoment B raw33505step2 raw33505step2Labels := by
      have ha : raw33505step2 = -raw33505step1 := by apply Matrix.ext; change ∀ i j, raw33505step2 i j = -(raw33505step1 i j); unfold raw33505step2 raw33505step1; decide +kernel
      have hl : raw33505step2Labels = raw33505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33505step2 raw33505step2Labels = mixedMoment B raw33505step3 raw33505step3Labels := by
      have ha : raw33505step3 = raw33505step2 := by apply Matrix.ext; unfold raw33505step3 raw33505step2; decide +kernel
      have hl : raw33505step2Labels = labelEmbedding1 ∘ raw33505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33505step2 raw33505step2Labels raw33505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical33506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33506 raw33506Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33506 raw33506Labels = mixedMoment B raw33506step0 raw33506step0Labels := by
      have hz : ∀ j, raw33506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33506step0 = (fun i j => raw33506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33506step0 raw33506; decide +kernel
      have hl : raw33506step0Labels = raw33506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33506 raw33506Labels permutation346 hz
    mixedMoment B raw33506step0 raw33506step0Labels = mixedMoment B raw33506step1 raw33506step1Labels := by
      have ha : raw33506step1 = (fun i j => raw33506step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33506step1 raw33506step0; decide +kernel
      have hl : raw33506step1Labels = raw33506step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33506step0 raw33506step0Labels permutation50 permutation7
    mixedMoment B raw33506step1 raw33506step1Labels = mixedMoment B raw33506step2 raw33506step2Labels := by
      have ha : raw33506step2 = -raw33506step1 := by apply Matrix.ext; change ∀ i j, raw33506step2 i j = -(raw33506step1 i j); unfold raw33506step2 raw33506step1; decide +kernel
      have hl : raw33506step2Labels = raw33506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33506step2 raw33506step2Labels = mixedMoment B raw33506step3 raw33506step3Labels := by
      have ha : raw33506step3 = raw33506step2 := by apply Matrix.ext; unfold raw33506step3 raw33506step2; decide +kernel
      have hl : raw33506step2Labels = labelEmbedding1 ∘ raw33506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33506step2 raw33506step2Labels raw33506step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical33507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33507 raw33507Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw33507 raw33507Labels = mixedMoment B raw33507step0 raw33507step0Labels := by
      have hz : ∀ j, raw33507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33507step0 = (fun i j => raw33507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33507step0 raw33507; decide +kernel
      have hl : raw33507step0Labels = raw33507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33507 raw33507Labels permutation346 hz
    mixedMoment B raw33507step0 raw33507step0Labels = mixedMoment B raw33507step1 raw33507step1Labels := by
      have ha : raw33507step1 = (fun i j => raw33507step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33507step1 raw33507step0; decide +kernel
      have hl : raw33507step1Labels = raw33507step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33507step0 raw33507step0Labels permutation144 permutation5
    mixedMoment B raw33507step1 raw33507step1Labels = mixedMoment B raw33507step2 raw33507step2Labels := by
      have ha : raw33507step2 = raw33507step1 := by apply Matrix.ext; unfold raw33507step2 raw33507step1; decide +kernel
      have hl : raw33507step1Labels = labelEmbedding1 ∘ raw33507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33507step1 raw33507step1Labels raw33507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

theorem canonical33508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33508 raw33508Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw33508 raw33508Labels = mixedMoment B raw33508step0 raw33508step0Labels := by
      have ha : raw33508step0 = (fun i j => raw33508 (permutation660 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33508step0 raw33508; decide +kernel
      have hl : raw33508step0Labels = raw33508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33508 raw33508Labels permutation660 permutation5
    mixedMoment B raw33508step0 raw33508step0Labels = mixedMoment B raw33508step1 raw33508step1Labels := by
      have ha : raw33508step1 = raw33508step0 := by apply Matrix.ext; unfold raw33508step1 raw33508step0; decide +kernel
      have hl : raw33508step0Labels = labelEmbedding1 ∘ raw33508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33508step0 raw33508step0Labels raw33508step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

theorem canonical33509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33509 raw33509Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw33509 raw33509Labels = mixedMoment B raw33509step0 raw33509step0Labels := by
      have hz : ∀ j, raw33509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33509step0 = (fun i j => raw33509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33509step0 raw33509; decide +kernel
      have hl : raw33509step0Labels = raw33509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33509 raw33509Labels permutation346 hz
    mixedMoment B raw33509step0 raw33509step0Labels = mixedMoment B raw33509step1 raw33509step1Labels := by
      have ha : raw33509step1 = (fun i j => raw33509step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33509step1 raw33509step0; decide +kernel
      have hl : raw33509step1Labels = raw33509step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33509step0 raw33509step0Labels permutation147 permutation5
    mixedMoment B raw33509step1 raw33509step1Labels = mixedMoment B raw33509step2 raw33509step2Labels := by
      have ha : raw33509step2 = raw33509step1 := by apply Matrix.ext; unfold raw33509step2 raw33509step1; decide +kernel
      have hl : raw33509step1Labels = labelEmbedding1 ∘ raw33509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33509step1 raw33509step1Labels raw33509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical33510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33510 raw33510Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw33510 raw33510Labels = mixedMoment B raw33510step0 raw33510step0Labels := by
      have hz : ∀ j, raw33510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33510step0 = (fun i j => raw33510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33510step0 raw33510; decide +kernel
      have hl : raw33510step0Labels = raw33510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33510 raw33510Labels permutation346 hz
    mixedMoment B raw33510step0 raw33510step0Labels = mixedMoment B raw33510step1 raw33510step1Labels := by
      have ha : raw33510step1 = (fun i j => raw33510step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33510step1 raw33510step0; decide +kernel
      have hl : raw33510step1Labels = raw33510step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33510step0 raw33510step0Labels permutation141 permutation5
    mixedMoment B raw33510step1 raw33510step1Labels = mixedMoment B raw33510step2 raw33510step2Labels := by
      have ha : raw33510step2 = raw33510step1 := by apply Matrix.ext; unfold raw33510step2 raw33510step1; decide +kernel
      have hl : raw33510step1Labels = labelEmbedding1 ∘ raw33510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33510step1 raw33510step1Labels raw33510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical33511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33511 raw33511Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw33511 raw33511Labels = mixedMoment B raw33511step0 raw33511step0Labels := by
      have hz : ∀ j, raw33511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33511step0 = (fun i j => raw33511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33511step0 raw33511; decide +kernel
      have hl : raw33511step0Labels = raw33511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33511 raw33511Labels permutation346 hz
    mixedMoment B raw33511step0 raw33511step0Labels = mixedMoment B raw33511step1 raw33511step1Labels := by
      have ha : raw33511step1 = (fun i j => raw33511step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33511step1 raw33511step0; decide +kernel
      have hl : raw33511step1Labels = raw33511step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33511step0 raw33511step0Labels permutation64 permutation4
    mixedMoment B raw33511step1 raw33511step1Labels = mixedMoment B raw33511step2 raw33511step2Labels := by
      have ha : raw33511step2 = -raw33511step1 := by apply Matrix.ext; change ∀ i j, raw33511step2 i j = -(raw33511step1 i j); unfold raw33511step2 raw33511step1; decide +kernel
      have hl : raw33511step2Labels = raw33511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3079 node3079Labels := by rfl

theorem canonical33512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33512 raw33512Labels = mixedMoment B node1824 node1824Labels := by
  calc
    _ = mixedMoment B node1824 node1824Labels := by rfl

theorem canonical33513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33513 raw33513Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw33513 raw33513Labels = mixedMoment B raw33513step0 raw33513step0Labels := by
      have hz : ∀ j, raw33513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33513step0 = (fun i j => raw33513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33513step0 raw33513; decide +kernel
      have hl : raw33513step0Labels = raw33513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33513 raw33513Labels permutation346 hz
    mixedMoment B raw33513step0 raw33513step0Labels = mixedMoment B raw33513step1 raw33513step1Labels := by
      have ha : raw33513step1 = (fun i j => raw33513step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33513step1 raw33513step0; decide +kernel
      have hl : raw33513step1Labels = raw33513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33513step0 raw33513step0Labels permutation35 permutation2
    _ = mixedMoment B node1829 node1829Labels := by rfl

theorem canonical33514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33514 raw33514Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw33514 raw33514Labels = mixedMoment B raw33514step0 raw33514step0Labels := by
      have hz : ∀ j, raw33514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33514step0 = (fun i j => raw33514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33514step0 raw33514; decide +kernel
      have hl : raw33514step0Labels = raw33514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33514 raw33514Labels permutation346 hz
    mixedMoment B raw33514step0 raw33514step0Labels = mixedMoment B raw33514step1 raw33514step1Labels := by
      have ha : raw33514step1 = (fun i j => raw33514step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33514step1 raw33514step0; decide +kernel
      have hl : raw33514step1Labels = raw33514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33514step0 raw33514step0Labels permutation33 permutation2
    _ = mixedMoment B node1829 node1829Labels := by rfl

theorem canonical33515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33515 raw33515Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw33515 raw33515Labels = mixedMoment B raw33515step0 raw33515step0Labels := by
      have hz : ∀ j, raw33515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33515step0 = (fun i j => raw33515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33515step0 raw33515; decide +kernel
      have hl : raw33515step0Labels = raw33515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33515 raw33515Labels permutation346 hz
    _ = mixedMoment B node1828 node1828Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33591 raw33591Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw33591 raw33591Labels = mixedMoment B raw33591step0 raw33591step0Labels := by
      have hz : ∀ j, raw33591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33591step0 = (fun i j => raw33591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33591step0 raw33591; decide +kernel
      have hl : raw33591step0Labels = raw33591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33591 raw33591Labels permutation346 hz
    mixedMoment B raw33591step0 raw33591step0Labels = mixedMoment B raw33591step1 raw33591step1Labels := by
      have ha : raw33591step1 = (fun i j => raw33591step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33591step1 raw33591step0; decide +kernel
      have hl : raw33591step1Labels = raw33591step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33591step0 raw33591step0Labels permutation62 permutation5
    mixedMoment B raw33591step1 raw33591step1Labels = mixedMoment B raw33591step2 raw33591step2Labels := by
      have ha : raw33591step2 = -raw33591step1 := by apply Matrix.ext; change ∀ i j, raw33591step2 i j = -(raw33591step1 i j); unfold raw33591step2 raw33591step1; decide +kernel
      have hl : raw33591step2Labels = raw33591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33591step2 raw33591step2Labels = mixedMoment B raw33591step3 raw33591step3Labels := by
      have ha : raw33591step3 = raw33591step2 := by apply Matrix.ext; unfold raw33591step3 raw33591step2; decide +kernel
      have hl : raw33591step2Labels = labelEmbedding1 ∘ raw33591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33591step2 raw33591step2Labels raw33591step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2760 node2760Labels := by rfl

theorem canonical33592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33592 raw33592Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw33592 raw33592Labels = mixedMoment B raw33592step0 raw33592step0Labels := by
      have ha : raw33592step0 = (fun i j => raw33592 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33592step0 raw33592; decide +kernel
      have hl : raw33592step0Labels = raw33592Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33592 raw33592Labels permutation188 permutation7
    mixedMoment B raw33592step0 raw33592step0Labels = mixedMoment B raw33592step1 raw33592step1Labels := by
      have ha : raw33592step1 = -raw33592step0 := by apply Matrix.ext; change ∀ i j, raw33592step1 i j = -(raw33592step0 i j); unfold raw33592step1 raw33592step0; decide +kernel
      have hl : raw33592step1Labels = raw33592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33592step1 raw33592step1Labels = mixedMoment B raw33592step2 raw33592step2Labels := by
      have ha : raw33592step2 = raw33592step1 := by apply Matrix.ext; unfold raw33592step2 raw33592step1; decide +kernel
      have hl : raw33592step1Labels = labelEmbedding1 ∘ raw33592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33592step1 raw33592step1Labels raw33592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical33593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33593 raw33593Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw33593 raw33593Labels = mixedMoment B raw33593step0 raw33593step0Labels := by
      have hz : ∀ j, raw33593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33593step0 = (fun i j => raw33593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33593step0 raw33593; decide +kernel
      have hl : raw33593step0Labels = raw33593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33593 raw33593Labels permutation346 hz
    mixedMoment B raw33593step0 raw33593step0Labels = mixedMoment B raw33593step1 raw33593step1Labels := by
      have ha : raw33593step1 = (fun i j => raw33593step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33593step1 raw33593step0; decide +kernel
      have hl : raw33593step1Labels = raw33593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33593step0 raw33593step0Labels permutation44 permutation7
    mixedMoment B raw33593step1 raw33593step1Labels = mixedMoment B raw33593step2 raw33593step2Labels := by
      have ha : raw33593step2 = -raw33593step1 := by apply Matrix.ext; change ∀ i j, raw33593step2 i j = -(raw33593step1 i j); unfold raw33593step2 raw33593step1; decide +kernel
      have hl : raw33593step2Labels = raw33593step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33593step2 raw33593step2Labels = mixedMoment B raw33593step3 raw33593step3Labels := by
      have ha : raw33593step3 = raw33593step2 := by apply Matrix.ext; unfold raw33593step3 raw33593step2; decide +kernel
      have hl : raw33593step2Labels = labelEmbedding1 ∘ raw33593step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33593step2 raw33593step2Labels raw33593step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical33594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33594 raw33594Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw33594 raw33594Labels = mixedMoment B raw33594step0 raw33594step0Labels := by
      have hz : ∀ j, raw33594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33594step0 = (fun i j => raw33594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33594step0 raw33594; decide +kernel
      have hl : raw33594step0Labels = raw33594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33594 raw33594Labels permutation520 hz
    mixedMoment B raw33594step0 raw33594step0Labels = mixedMoment B raw33594step1 raw33594step1Labels := by
      have hz : ∀ j, raw33594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33594step1 = (fun i j => raw33594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33594step1 raw33594step0; decide +kernel
      have hl : raw33594step1Labels = raw33594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33594step0 raw33594step0Labels permutation80 hz
    mixedMoment B raw33594step1 raw33594step1Labels = mixedMoment B raw33594step2 raw33594step2Labels := by
      have ha : raw33594step2 = (fun i j => raw33594step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33594step2 raw33594step1; decide +kernel
      have hl : raw33594step2Labels = raw33594step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33594step1 raw33594step1Labels permutation8 permutation7
    mixedMoment B raw33594step2 raw33594step2Labels = mixedMoment B raw33594step3 raw33594step3Labels := by
      have ha : raw33594step3 = -raw33594step2 := by apply Matrix.ext; change ∀ i j, raw33594step3 i j = -(raw33594step2 i j); unfold raw33594step3 raw33594step2; decide +kernel
      have hl : raw33594step3Labels = raw33594step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33594step3 raw33594step3Labels = mixedMoment B raw33594step4 raw33594step4Labels := by
      have ha : raw33594step4 = raw33594step3 := by apply Matrix.ext; unfold raw33594step4 raw33594step3; decide +kernel
      have hl : raw33594step3Labels = labelEmbedding1 ∘ raw33594step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33594step3 raw33594step3Labels raw33594step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical33595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33595 raw33595Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw33595 raw33595Labels = mixedMoment B raw33595step0 raw33595step0Labels := by
      have hz : ∀ j, raw33595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33595step0 = (fun i j => raw33595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33595step0 raw33595; decide +kernel
      have hl : raw33595step0Labels = raw33595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33595 raw33595Labels permutation346 hz
    mixedMoment B raw33595step0 raw33595step0Labels = mixedMoment B raw33595step1 raw33595step1Labels := by
      have ha : raw33595step1 = (fun i j => raw33595step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33595step1 raw33595step0; decide +kernel
      have hl : raw33595step1Labels = raw33595step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33595step0 raw33595step0Labels permutation44 permutation7
    mixedMoment B raw33595step1 raw33595step1Labels = mixedMoment B raw33595step2 raw33595step2Labels := by
      have ha : raw33595step2 = -raw33595step1 := by apply Matrix.ext; change ∀ i j, raw33595step2 i j = -(raw33595step1 i j); unfold raw33595step2 raw33595step1; decide +kernel
      have hl : raw33595step2Labels = raw33595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33595step2 raw33595step2Labels = mixedMoment B raw33595step3 raw33595step3Labels := by
      have ha : raw33595step3 = raw33595step2 := by apply Matrix.ext; unfold raw33595step3 raw33595step2; decide +kernel
      have hl : raw33595step2Labels = labelEmbedding1 ∘ raw33595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33595step2 raw33595step2Labels raw33595step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical33596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33596 raw33596Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw33596 raw33596Labels = mixedMoment B raw33596step0 raw33596step0Labels := by
      have hz : ∀ j, raw33596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33596step0 = (fun i j => raw33596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33596step0 raw33596; decide +kernel
      have hl : raw33596step0Labels = raw33596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33596 raw33596Labels permutation346 hz
    mixedMoment B raw33596step0 raw33596step0Labels = mixedMoment B raw33596step1 raw33596step1Labels := by
      have ha : raw33596step1 = (fun i j => raw33596step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33596step1 raw33596step0; decide +kernel
      have hl : raw33596step1Labels = raw33596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33596step0 raw33596step0Labels permutation44 permutation7
    mixedMoment B raw33596step1 raw33596step1Labels = mixedMoment B raw33596step2 raw33596step2Labels := by
      have ha : raw33596step2 = -raw33596step1 := by apply Matrix.ext; change ∀ i j, raw33596step2 i j = -(raw33596step1 i j); unfold raw33596step2 raw33596step1; decide +kernel
      have hl : raw33596step2Labels = raw33596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33596step2 raw33596step2Labels = mixedMoment B raw33596step3 raw33596step3Labels := by
      have ha : raw33596step3 = raw33596step2 := by apply Matrix.ext; unfold raw33596step3 raw33596step2; decide +kernel
      have hl : raw33596step2Labels = labelEmbedding1 ∘ raw33596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33596step2 raw33596step2Labels raw33596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical33597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33597 raw33597Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw33597 raw33597Labels = mixedMoment B raw33597step0 raw33597step0Labels := by
      have ha : raw33597step0 = (fun i j => raw33597 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33597step0 raw33597; decide +kernel
      have hl : raw33597step0Labels = raw33597Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33597 raw33597Labels permutation188 permutation7
    mixedMoment B raw33597step0 raw33597step0Labels = mixedMoment B raw33597step1 raw33597step1Labels := by
      have ha : raw33597step1 = -raw33597step0 := by apply Matrix.ext; change ∀ i j, raw33597step1 i j = -(raw33597step0 i j); unfold raw33597step1 raw33597step0; decide +kernel
      have hl : raw33597step1Labels = raw33597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33597step1 raw33597step1Labels = mixedMoment B raw33597step2 raw33597step2Labels := by
      have ha : raw33597step2 = raw33597step1 := by apply Matrix.ext; unfold raw33597step2 raw33597step1; decide +kernel
      have hl : raw33597step1Labels = labelEmbedding1 ∘ raw33597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33597step1 raw33597step1Labels raw33597step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical33598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33598 raw33598Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw33598 raw33598Labels = mixedMoment B raw33598step0 raw33598step0Labels := by
      have ha : raw33598step0 = (fun i j => raw33598 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33598step0 raw33598; decide +kernel
      have hl : raw33598step0Labels = raw33598Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33598 raw33598Labels permutation188 permutation7
    mixedMoment B raw33598step0 raw33598step0Labels = mixedMoment B raw33598step1 raw33598step1Labels := by
      have ha : raw33598step1 = -raw33598step0 := by apply Matrix.ext; change ∀ i j, raw33598step1 i j = -(raw33598step0 i j); unfold raw33598step1 raw33598step0; decide +kernel
      have hl : raw33598step1Labels = raw33598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33598step1 raw33598step1Labels = mixedMoment B raw33598step2 raw33598step2Labels := by
      have ha : raw33598step2 = raw33598step1 := by apply Matrix.ext; unfold raw33598step2 raw33598step1; decide +kernel
      have hl : raw33598step1Labels = labelEmbedding1 ∘ raw33598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33598step1 raw33598step1Labels raw33598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical33599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33599 raw33599Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33599 raw33599Labels = mixedMoment B raw33599step0 raw33599step0Labels := by
      have hz : ∀ j, raw33599 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33599step0 = (fun i j => raw33599 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33599step0 raw33599; decide +kernel
      have hl : raw33599step0Labels = raw33599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33599 raw33599Labels permutation520 hz
    mixedMoment B raw33599step0 raw33599step0Labels = mixedMoment B raw33599step1 raw33599step1Labels := by
      have ha : raw33599step1 = (fun i j => raw33599step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33599step1 raw33599step0; decide +kernel
      have hl : raw33599step1Labels = raw33599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33599step0 raw33599step0Labels permutation38 permutation7
    mixedMoment B raw33599step1 raw33599step1Labels = mixedMoment B raw33599step2 raw33599step2Labels := by
      have ha : raw33599step2 = -raw33599step1 := by apply Matrix.ext; change ∀ i j, raw33599step2 i j = -(raw33599step1 i j); unfold raw33599step2 raw33599step1; decide +kernel
      have hl : raw33599step2Labels = raw33599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33599step2 raw33599step2Labels = mixedMoment B raw33599step3 raw33599step3Labels := by
      have ha : raw33599step3 = raw33599step2 := by apply Matrix.ext; unfold raw33599step3 raw33599step2; decide +kernel
      have hl : raw33599step2Labels = labelEmbedding1 ∘ raw33599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33599step2 raw33599step2Labels raw33599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical33600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33600 raw33600Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw33600 raw33600Labels = mixedMoment B raw33600step0 raw33600step0Labels := by
      have ha : raw33600step0 = (fun i j => raw33600 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33600step0 raw33600; decide +kernel
      have hl : raw33600step0Labels = raw33600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33600 raw33600Labels permutation188 permutation7
    mixedMoment B raw33600step0 raw33600step0Labels = mixedMoment B raw33600step1 raw33600step1Labels := by
      have ha : raw33600step1 = -raw33600step0 := by apply Matrix.ext; change ∀ i j, raw33600step1 i j = -(raw33600step0 i j); unfold raw33600step1 raw33600step0; decide +kernel
      have hl : raw33600step1Labels = raw33600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33600step1 raw33600step1Labels = mixedMoment B raw33600step2 raw33600step2Labels := by
      have ha : raw33600step2 = raw33600step1 := by apply Matrix.ext; unfold raw33600step2 raw33600step1; decide +kernel
      have hl : raw33600step1Labels = labelEmbedding1 ∘ raw33600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33600step1 raw33600step1Labels raw33600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical33601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33601 raw33601Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw33601 raw33601Labels = mixedMoment B raw33601step0 raw33601step0Labels := by
      have hz : ∀ j, raw33601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33601step0 = (fun i j => raw33601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33601step0 raw33601; decide +kernel
      have hl : raw33601step0Labels = raw33601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33601 raw33601Labels permutation346 hz
    mixedMoment B raw33601step0 raw33601step0Labels = mixedMoment B raw33601step1 raw33601step1Labels := by
      have ha : raw33601step1 = (fun i j => raw33601step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33601step1 raw33601step0; decide +kernel
      have hl : raw33601step1Labels = raw33601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33601step0 raw33601step0Labels permutation44 permutation7
    mixedMoment B raw33601step1 raw33601step1Labels = mixedMoment B raw33601step2 raw33601step2Labels := by
      have ha : raw33601step2 = -raw33601step1 := by apply Matrix.ext; change ∀ i j, raw33601step2 i j = -(raw33601step1 i j); unfold raw33601step2 raw33601step1; decide +kernel
      have hl : raw33601step2Labels = raw33601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33601step2 raw33601step2Labels = mixedMoment B raw33601step3 raw33601step3Labels := by
      have ha : raw33601step3 = raw33601step2 := by apply Matrix.ext; unfold raw33601step3 raw33601step2; decide +kernel
      have hl : raw33601step2Labels = labelEmbedding1 ∘ raw33601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33601step2 raw33601step2Labels raw33601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical33602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33602 raw33602Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw33602 raw33602Labels = mixedMoment B raw33602step0 raw33602step0Labels := by
      have ha : raw33602step0 = (fun i j => raw33602 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33602step0 raw33602; decide +kernel
      have hl : raw33602step0Labels = raw33602Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33602 raw33602Labels permutation188 permutation7
    mixedMoment B raw33602step0 raw33602step0Labels = mixedMoment B raw33602step1 raw33602step1Labels := by
      have ha : raw33602step1 = -raw33602step0 := by apply Matrix.ext; change ∀ i j, raw33602step1 i j = -(raw33602step0 i j); unfold raw33602step1 raw33602step0; decide +kernel
      have hl : raw33602step1Labels = raw33602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33602step1 raw33602step1Labels = mixedMoment B raw33602step2 raw33602step2Labels := by
      have ha : raw33602step2 = raw33602step1 := by apply Matrix.ext; unfold raw33602step2 raw33602step1; decide +kernel
      have hl : raw33602step1Labels = labelEmbedding1 ∘ raw33602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33602step1 raw33602step1Labels raw33602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical33603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33603 raw33603Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw33603 raw33603Labels = mixedMoment B raw33603step0 raw33603step0Labels := by
      have hz : ∀ j, raw33603 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33603step0 = (fun i j => raw33603 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33603step0 raw33603; decide +kernel
      have hl : raw33603step0Labels = raw33603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33603 raw33603Labels permutation520 hz
    mixedMoment B raw33603step0 raw33603step0Labels = mixedMoment B raw33603step1 raw33603step1Labels := by
      have hz : ∀ j, raw33603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33603step1 = (fun i j => raw33603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33603step1 raw33603step0; decide +kernel
      have hl : raw33603step1Labels = raw33603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33603step0 raw33603step0Labels permutation80 hz
    mixedMoment B raw33603step1 raw33603step1Labels = mixedMoment B raw33603step2 raw33603step2Labels := by
      have ha : raw33603step2 = (fun i j => raw33603step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33603step2 raw33603step1; decide +kernel
      have hl : raw33603step2Labels = raw33603step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33603step1 raw33603step1Labels permutation8 permutation7
    mixedMoment B raw33603step2 raw33603step2Labels = mixedMoment B raw33603step3 raw33603step3Labels := by
      have ha : raw33603step3 = -raw33603step2 := by apply Matrix.ext; change ∀ i j, raw33603step3 i j = -(raw33603step2 i j); unfold raw33603step3 raw33603step2; decide +kernel
      have hl : raw33603step3Labels = raw33603step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33603step3 raw33603step3Labels = mixedMoment B raw33603step4 raw33603step4Labels := by
      have ha : raw33603step4 = raw33603step3 := by apply Matrix.ext; unfold raw33603step4 raw33603step3; decide +kernel
      have hl : raw33603step3Labels = labelEmbedding1 ∘ raw33603step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33603step3 raw33603step3Labels raw33603step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical33604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33604 raw33604Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33604 raw33604Labels = mixedMoment B raw33604step0 raw33604step0Labels := by
      have hz : ∀ j, raw33604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33604step0 = (fun i j => raw33604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33604step0 raw33604; decide +kernel
      have hl : raw33604step0Labels = raw33604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33604 raw33604Labels permutation346 hz
    mixedMoment B raw33604step0 raw33604step0Labels = mixedMoment B raw33604step1 raw33604step1Labels := by
      have ha : raw33604step1 = (fun i j => raw33604step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33604step1 raw33604step0; decide +kernel
      have hl : raw33604step1Labels = raw33604step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33604step0 raw33604step0Labels permutation45 permutation7
    mixedMoment B raw33604step1 raw33604step1Labels = mixedMoment B raw33604step2 raw33604step2Labels := by
      have ha : raw33604step2 = -raw33604step1 := by apply Matrix.ext; change ∀ i j, raw33604step2 i j = -(raw33604step1 i j); unfold raw33604step2 raw33604step1; decide +kernel
      have hl : raw33604step2Labels = raw33604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33604step2 raw33604step2Labels = mixedMoment B raw33604step3 raw33604step3Labels := by
      have ha : raw33604step3 = raw33604step2 := by apply Matrix.ext; unfold raw33604step3 raw33604step2; decide +kernel
      have hl : raw33604step2Labels = labelEmbedding1 ∘ raw33604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33604step2 raw33604step2Labels raw33604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical33605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33605 raw33605Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33605 raw33605Labels = mixedMoment B raw33605step0 raw33605step0Labels := by
      have hz : ∀ j, raw33605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33605step0 = (fun i j => raw33605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33605step0 raw33605; decide +kernel
      have hl : raw33605step0Labels = raw33605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33605 raw33605Labels permutation346 hz
    mixedMoment B raw33605step0 raw33605step0Labels = mixedMoment B raw33605step1 raw33605step1Labels := by
      have ha : raw33605step1 = (fun i j => raw33605step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33605step1 raw33605step0; decide +kernel
      have hl : raw33605step1Labels = raw33605step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33605step0 raw33605step0Labels permutation44 permutation7
    mixedMoment B raw33605step1 raw33605step1Labels = mixedMoment B raw33605step2 raw33605step2Labels := by
      have ha : raw33605step2 = -raw33605step1 := by apply Matrix.ext; change ∀ i j, raw33605step2 i j = -(raw33605step1 i j); unfold raw33605step2 raw33605step1; decide +kernel
      have hl : raw33605step2Labels = raw33605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33605step2 raw33605step2Labels = mixedMoment B raw33605step3 raw33605step3Labels := by
      have ha : raw33605step3 = raw33605step2 := by apply Matrix.ext; unfold raw33605step3 raw33605step2; decide +kernel
      have hl : raw33605step2Labels = labelEmbedding1 ∘ raw33605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33605step2 raw33605step2Labels raw33605step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical33606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33606 raw33606Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33606 raw33606Labels = mixedMoment B raw33606step0 raw33606step0Labels := by
      have ha : raw33606step0 = (fun i j => raw33606 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33606step0 raw33606; decide +kernel
      have hl : raw33606step0Labels = raw33606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33606 raw33606Labels permutation188 permutation7
    mixedMoment B raw33606step0 raw33606step0Labels = mixedMoment B raw33606step1 raw33606step1Labels := by
      have ha : raw33606step1 = -raw33606step0 := by apply Matrix.ext; change ∀ i j, raw33606step1 i j = -(raw33606step0 i j); unfold raw33606step1 raw33606step0; decide +kernel
      have hl : raw33606step1Labels = raw33606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33606step1 raw33606step1Labels = mixedMoment B raw33606step2 raw33606step2Labels := by
      have ha : raw33606step2 = raw33606step1 := by apply Matrix.ext; unfold raw33606step2 raw33606step1; decide +kernel
      have hl : raw33606step1Labels = labelEmbedding1 ∘ raw33606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33606step1 raw33606step1Labels raw33606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33607 raw33607Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33607 raw33607Labels = mixedMoment B raw33607step0 raw33607step0Labels := by
      have hz : ∀ j, raw33607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33607step0 = (fun i j => raw33607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33607step0 raw33607; decide +kernel
      have hl : raw33607step0Labels = raw33607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33607 raw33607Labels permutation346 hz
    mixedMoment B raw33607step0 raw33607step0Labels = mixedMoment B raw33607step1 raw33607step1Labels := by
      have ha : raw33607step1 = (fun i j => raw33607step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33607step1 raw33607step0; decide +kernel
      have hl : raw33607step1Labels = raw33607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33607step0 raw33607step0Labels permutation44 permutation7
    mixedMoment B raw33607step1 raw33607step1Labels = mixedMoment B raw33607step2 raw33607step2Labels := by
      have ha : raw33607step2 = -raw33607step1 := by apply Matrix.ext; change ∀ i j, raw33607step2 i j = -(raw33607step1 i j); unfold raw33607step2 raw33607step1; decide +kernel
      have hl : raw33607step2Labels = raw33607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33607step2 raw33607step2Labels = mixedMoment B raw33607step3 raw33607step3Labels := by
      have ha : raw33607step3 = raw33607step2 := by apply Matrix.ext; unfold raw33607step3 raw33607step2; decide +kernel
      have hl : raw33607step2Labels = labelEmbedding1 ∘ raw33607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33607step2 raw33607step2Labels raw33607step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical33608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33608 raw33608Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw33608 raw33608Labels = mixedMoment B raw33608step0 raw33608step0Labels := by
      have hz : ∀ j, raw33608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33608step0 = (fun i j => raw33608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33608step0 raw33608; decide +kernel
      have hl : raw33608step0Labels = raw33608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33608 raw33608Labels permutation346 hz
    mixedMoment B raw33608step0 raw33608step0Labels = mixedMoment B raw33608step1 raw33608step1Labels := by
      have ha : raw33608step1 = (fun i j => raw33608step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33608step1 raw33608step0; decide +kernel
      have hl : raw33608step1Labels = raw33608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33608step0 raw33608step0Labels permutation44 permutation7
    mixedMoment B raw33608step1 raw33608step1Labels = mixedMoment B raw33608step2 raw33608step2Labels := by
      have ha : raw33608step2 = -raw33608step1 := by apply Matrix.ext; change ∀ i j, raw33608step2 i j = -(raw33608step1 i j); unfold raw33608step2 raw33608step1; decide +kernel
      have hl : raw33608step2Labels = raw33608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33608step2 raw33608step2Labels = mixedMoment B raw33608step3 raw33608step3Labels := by
      have ha : raw33608step3 = raw33608step2 := by apply Matrix.ext; unfold raw33608step3 raw33608step2; decide +kernel
      have hl : raw33608step2Labels = labelEmbedding1 ∘ raw33608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33608step2 raw33608step2Labels raw33608step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical33609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33609 raw33609Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw33609 raw33609Labels = mixedMoment B raw33609step0 raw33609step0Labels := by
      have hz : ∀ j, raw33609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33609step0 = (fun i j => raw33609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33609step0 raw33609; decide +kernel
      have hl : raw33609step0Labels = raw33609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33609 raw33609Labels permutation346 hz
    mixedMoment B raw33609step0 raw33609step0Labels = mixedMoment B raw33609step1 raw33609step1Labels := by
      have ha : raw33609step1 = (fun i j => raw33609step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33609step1 raw33609step0; decide +kernel
      have hl : raw33609step1Labels = raw33609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33609step0 raw33609step0Labels permutation44 permutation7
    mixedMoment B raw33609step1 raw33609step1Labels = mixedMoment B raw33609step2 raw33609step2Labels := by
      have ha : raw33609step2 = -raw33609step1 := by apply Matrix.ext; change ∀ i j, raw33609step2 i j = -(raw33609step1 i j); unfold raw33609step2 raw33609step1; decide +kernel
      have hl : raw33609step2Labels = raw33609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33609step2 raw33609step2Labels = mixedMoment B raw33609step3 raw33609step3Labels := by
      have ha : raw33609step3 = raw33609step2 := by apply Matrix.ext; unfold raw33609step3 raw33609step2; decide +kernel
      have hl : raw33609step2Labels = labelEmbedding1 ∘ raw33609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33609step2 raw33609step2Labels raw33609step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical33610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33610 raw33610Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw33610 raw33610Labels = mixedMoment B raw33610step0 raw33610step0Labels := by
      have ha : raw33610step0 = (fun i j => raw33610 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33610step0 raw33610; decide +kernel
      have hl : raw33610step0Labels = raw33610Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33610 raw33610Labels permutation188 permutation7
    mixedMoment B raw33610step0 raw33610step0Labels = mixedMoment B raw33610step1 raw33610step1Labels := by
      have ha : raw33610step1 = -raw33610step0 := by apply Matrix.ext; change ∀ i j, raw33610step1 i j = -(raw33610step0 i j); unfold raw33610step1 raw33610step0; decide +kernel
      have hl : raw33610step1Labels = raw33610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33610step1 raw33610step1Labels = mixedMoment B raw33610step2 raw33610step2Labels := by
      have ha : raw33610step2 = raw33610step1 := by apply Matrix.ext; unfold raw33610step2 raw33610step1; decide +kernel
      have hl : raw33610step1Labels = labelEmbedding1 ∘ raw33610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33610step1 raw33610step1Labels raw33610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical33611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33611 raw33611Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw33611 raw33611Labels = mixedMoment B raw33611step0 raw33611step0Labels := by
      have hz : ∀ j, raw33611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33611step0 = (fun i j => raw33611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33611step0 raw33611; decide +kernel
      have hl : raw33611step0Labels = raw33611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33611 raw33611Labels permutation346 hz
    mixedMoment B raw33611step0 raw33611step0Labels = mixedMoment B raw33611step1 raw33611step1Labels := by
      have ha : raw33611step1 = (fun i j => raw33611step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33611step1 raw33611step0; decide +kernel
      have hl : raw33611step1Labels = raw33611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33611step0 raw33611step0Labels permutation44 permutation7
    mixedMoment B raw33611step1 raw33611step1Labels = mixedMoment B raw33611step2 raw33611step2Labels := by
      have ha : raw33611step2 = -raw33611step1 := by apply Matrix.ext; change ∀ i j, raw33611step2 i j = -(raw33611step1 i j); unfold raw33611step2 raw33611step1; decide +kernel
      have hl : raw33611step2Labels = raw33611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33611step2 raw33611step2Labels = mixedMoment B raw33611step3 raw33611step3Labels := by
      have ha : raw33611step3 = raw33611step2 := by apply Matrix.ext; unfold raw33611step3 raw33611step2; decide +kernel
      have hl : raw33611step2Labels = labelEmbedding1 ∘ raw33611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33611step2 raw33611step2Labels raw33611step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical33612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33612 raw33612Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw33612 raw33612Labels = mixedMoment B raw33612step0 raw33612step0Labels := by
      have hz : ∀ j, raw33612 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33612step0 = (fun i j => raw33612 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33612step0 raw33612; decide +kernel
      have hl : raw33612step0Labels = raw33612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33612 raw33612Labels permutation520 hz
    mixedMoment B raw33612step0 raw33612step0Labels = mixedMoment B raw33612step1 raw33612step1Labels := by
      have hz : ∀ j, raw33612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33612step1 = (fun i j => raw33612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33612step1 raw33612step0; decide +kernel
      have hl : raw33612step1Labels = raw33612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33612step0 raw33612step0Labels permutation80 hz
    mixedMoment B raw33612step1 raw33612step1Labels = mixedMoment B raw33612step2 raw33612step2Labels := by
      have ha : raw33612step2 = (fun i j => raw33612step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33612step2 raw33612step1; decide +kernel
      have hl : raw33612step2Labels = raw33612step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33612step1 raw33612step1Labels permutation8 permutation7
    mixedMoment B raw33612step2 raw33612step2Labels = mixedMoment B raw33612step3 raw33612step3Labels := by
      have ha : raw33612step3 = -raw33612step2 := by apply Matrix.ext; change ∀ i j, raw33612step3 i j = -(raw33612step2 i j); unfold raw33612step3 raw33612step2; decide +kernel
      have hl : raw33612step3Labels = raw33612step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33612step3 raw33612step3Labels = mixedMoment B raw33612step4 raw33612step4Labels := by
      have ha : raw33612step4 = raw33612step3 := by apply Matrix.ext; unfold raw33612step4 raw33612step3; decide +kernel
      have hl : raw33612step3Labels = labelEmbedding1 ∘ raw33612step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33612step3 raw33612step3Labels raw33612step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical33613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33613 raw33613Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw33613 raw33613Labels = mixedMoment B raw33613step0 raw33613step0Labels := by
      have hz : ∀ j, raw33613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33613step0 = (fun i j => raw33613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33613step0 raw33613; decide +kernel
      have hl : raw33613step0Labels = raw33613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33613 raw33613Labels permutation346 hz
    mixedMoment B raw33613step0 raw33613step0Labels = mixedMoment B raw33613step1 raw33613step1Labels := by
      have ha : raw33613step1 = (fun i j => raw33613step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33613step1 raw33613step0; decide +kernel
      have hl : raw33613step1Labels = raw33613step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33613step0 raw33613step0Labels permutation67 permutation4
    mixedMoment B raw33613step1 raw33613step1Labels = mixedMoment B raw33613step2 raw33613step2Labels := by
      have ha : raw33613step2 = -raw33613step1 := by apply Matrix.ext; change ∀ i j, raw33613step2 i j = -(raw33613step1 i j); unfold raw33613step2 raw33613step1; decide +kernel
      have hl : raw33613step2Labels = raw33613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3096 node3096Labels := by rfl

theorem canonical33614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33614 raw33614Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw33614 raw33614Labels = mixedMoment B raw33614step0 raw33614step0Labels := by
      have ha : raw33614step0 = (fun i j => raw33614 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33614step0 raw33614; decide +kernel
      have hl : raw33614step0Labels = raw33614Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33614 raw33614Labels permutation154 permutation2
    _ = mixedMoment B node1822 node1822Labels := by rfl

theorem canonical33615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33615 raw33615Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw33615 raw33615Labels = mixedMoment B raw33615step0 raw33615step0Labels := by
      have hz : ∀ j, raw33615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33615step0 = (fun i j => raw33615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33615step0 raw33615; decide +kernel
      have hl : raw33615step0Labels = raw33615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33615 raw33615Labels permutation346 hz
    mixedMoment B raw33615step0 raw33615step0Labels = mixedMoment B raw33615step1 raw33615step1Labels := by
      have ha : raw33615step1 = (fun i j => raw33615step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33615step1 raw33615step0; decide +kernel
      have hl : raw33615step1Labels = raw33615step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33615step0 raw33615step0Labels permutation34 permutation2
    _ = mixedMoment B node1827 node1827Labels := by rfl

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

theorem canonical11604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11604 raw11604Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw11604 raw11604Labels = mixedMoment B raw11604step0 raw11604step0Labels := by
      have ha : raw11604step0 = (fun i j => raw11604 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11604step0 raw11604; decide +kernel
      have hl : raw11604step0Labels = raw11604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11604 raw11604Labels permutation160 permutation7
    mixedMoment B raw11604step0 raw11604step0Labels = mixedMoment B raw11604step1 raw11604step1Labels := by
      have ha : raw11604step1 = -raw11604step0 := by apply Matrix.ext; change ∀ i j, raw11604step1 i j = -(raw11604step0 i j); unfold raw11604step1 raw11604step0; decide +kernel
      have hl : raw11604step1Labels = raw11604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11604step1 raw11604step1Labels = mixedMoment B raw11604step2 raw11604step2Labels := by
      have ha : raw11604step2 = raw11604step1 := by apply Matrix.ext; unfold raw11604step2 raw11604step1; decide +kernel
      have hl : raw11604step1Labels = labelEmbedding1 ∘ raw11604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11604step1 raw11604step1Labels raw11604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical11615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11615 raw11615Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw11615 raw11615Labels = mixedMoment B raw11615step0 raw11615step0Labels := by
      have ha : raw11615step0 = (fun i j => raw11615 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11615step0 raw11615; decide +kernel
      have hl : raw11615step0Labels = raw11615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11615 raw11615Labels permutation160 permutation7
    mixedMoment B raw11615step0 raw11615step0Labels = mixedMoment B raw11615step1 raw11615step1Labels := by
      have ha : raw11615step1 = -raw11615step0 := by apply Matrix.ext; change ∀ i j, raw11615step1 i j = -(raw11615step0 i j); unfold raw11615step1 raw11615step0; decide +kernel
      have hl : raw11615step1Labels = raw11615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11615step1 raw11615step1Labels = mixedMoment B raw11615step2 raw11615step2Labels := by
      have ha : raw11615step2 = raw11615step1 := by apply Matrix.ext; unfold raw11615step2 raw11615step1; decide +kernel
      have hl : raw11615step1Labels = labelEmbedding1 ∘ raw11615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11615step1 raw11615step1Labels raw11615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical11620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11620 raw11620Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11620 raw11620Labels = mixedMoment B raw11620step0 raw11620step0Labels := by
      have ha : raw11620step0 = (fun i j => raw11620 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11620step0 raw11620; decide +kernel
      have hl : raw11620step0Labels = raw11620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11620 raw11620Labels permutation166 permutation7
    mixedMoment B raw11620step0 raw11620step0Labels = mixedMoment B raw11620step1 raw11620step1Labels := by
      have ha : raw11620step1 = -raw11620step0 := by apply Matrix.ext; change ∀ i j, raw11620step1 i j = -(raw11620step0 i j); unfold raw11620step1 raw11620step0; decide +kernel
      have hl : raw11620step1Labels = raw11620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11620step1 raw11620step1Labels = mixedMoment B raw11620step2 raw11620step2Labels := by
      have ha : raw11620step2 = raw11620step1 := by apply Matrix.ext; unfold raw11620step2 raw11620step1; decide +kernel
      have hl : raw11620step1Labels = labelEmbedding1 ∘ raw11620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11620step1 raw11620step1Labels raw11620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical11625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11625 raw11625Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11625 raw11625Labels = mixedMoment B raw11625step0 raw11625step0Labels := by
      have ha : raw11625step0 = (fun i j => raw11625 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11625step0 raw11625; decide +kernel
      have hl : raw11625step0Labels = raw11625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11625 raw11625Labels permutation160 permutation7
    mixedMoment B raw11625step0 raw11625step0Labels = mixedMoment B raw11625step1 raw11625step1Labels := by
      have ha : raw11625step1 = -raw11625step0 := by apply Matrix.ext; change ∀ i j, raw11625step1 i j = -(raw11625step0 i j); unfold raw11625step1 raw11625step0; decide +kernel
      have hl : raw11625step1Labels = raw11625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11625step1 raw11625step1Labels = mixedMoment B raw11625step2 raw11625step2Labels := by
      have ha : raw11625step2 = raw11625step1 := by apply Matrix.ext; unfold raw11625step2 raw11625step1; decide +kernel
      have hl : raw11625step1Labels = labelEmbedding1 ∘ raw11625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11625step1 raw11625step1Labels raw11625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical11629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11629 raw11629Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw11629 raw11629Labels = mixedMoment B raw11629step0 raw11629step0Labels := by
      have ha : raw11629step0 = (fun i j => raw11629 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11629step0 raw11629; decide +kernel
      have hl : raw11629step0Labels = raw11629Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11629 raw11629Labels permutation160 permutation7
    mixedMoment B raw11629step0 raw11629step0Labels = mixedMoment B raw11629step1 raw11629step1Labels := by
      have ha : raw11629step1 = -raw11629step0 := by apply Matrix.ext; change ∀ i j, raw11629step1 i j = -(raw11629step0 i j); unfold raw11629step1 raw11629step0; decide +kernel
      have hl : raw11629step1Labels = raw11629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11629step1 raw11629step1Labels = mixedMoment B raw11629step2 raw11629step2Labels := by
      have ha : raw11629step2 = raw11629step1 := by apply Matrix.ext; unfold raw11629step2 raw11629step1; decide +kernel
      have hl : raw11629step1Labels = labelEmbedding1 ∘ raw11629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11629step1 raw11629step1Labels raw11629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical11631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11631 raw11631Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw11631 raw11631Labels = mixedMoment B raw11631step0 raw11631step0Labels := by
      have ha : raw11631step0 = (fun i j => raw11631 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11631step0 raw11631; decide +kernel
      have hl : raw11631step0Labels = raw11631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11631 raw11631Labels permutation160 permutation7
    mixedMoment B raw11631step0 raw11631step0Labels = mixedMoment B raw11631step1 raw11631step1Labels := by
      have ha : raw11631step1 = -raw11631step0 := by apply Matrix.ext; change ∀ i j, raw11631step1 i j = -(raw11631step0 i j); unfold raw11631step1 raw11631step0; decide +kernel
      have hl : raw11631step1Labels = raw11631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11631step1 raw11631step1Labels = mixedMoment B raw11631step2 raw11631step2Labels := by
      have ha : raw11631step2 = raw11631step1 := by apply Matrix.ext; unfold raw11631step2 raw11631step1; decide +kernel
      have hl : raw11631step1Labels = labelEmbedding1 ∘ raw11631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11631step1 raw11631step1Labels raw11631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical11632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11632 raw11632Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11632 raw11632Labels = mixedMoment B raw11632step0 raw11632step0Labels := by
      have hz : ∀ j, raw11632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11632step0 = (fun i j => raw11632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11632step0 raw11632; decide +kernel
      have hl : raw11632step0Labels = raw11632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11632 raw11632Labels permutation434 hz
    mixedMoment B raw11632step0 raw11632step0Labels = mixedMoment B raw11632step1 raw11632step1Labels := by
      have ha : raw11632step1 = (fun i j => raw11632step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11632step1 raw11632step0; decide +kernel
      have hl : raw11632step1Labels = raw11632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11632step0 raw11632step0Labels permutation34 permutation7
    mixedMoment B raw11632step1 raw11632step1Labels = mixedMoment B raw11632step2 raw11632step2Labels := by
      have ha : raw11632step2 = -raw11632step1 := by apply Matrix.ext; change ∀ i j, raw11632step2 i j = -(raw11632step1 i j); unfold raw11632step2 raw11632step1; decide +kernel
      have hl : raw11632step2Labels = raw11632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11632step2 raw11632step2Labels = mixedMoment B raw11632step3 raw11632step3Labels := by
      have ha : raw11632step3 = raw11632step2 := by apply Matrix.ext; unfold raw11632step3 raw11632step2; decide +kernel
      have hl : raw11632step2Labels = labelEmbedding1 ∘ raw11632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11632step2 raw11632step2Labels raw11632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical11633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11633 raw11633Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11633 raw11633Labels = mixedMoment B raw11633step0 raw11633step0Labels := by
      have hz : ∀ j, raw11633 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11633step0 = (fun i j => raw11633 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11633step0 raw11633; decide +kernel
      have hl : raw11633step0Labels = raw11633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11633 raw11633Labels permutation520 hz
    mixedMoment B raw11633step0 raw11633step0Labels = mixedMoment B raw11633step1 raw11633step1Labels := by
      have ha : raw11633step1 = (fun i j => raw11633step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11633step1 raw11633step0; decide +kernel
      have hl : raw11633step1Labels = raw11633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11633step0 raw11633step0Labels permutation34 permutation7
    mixedMoment B raw11633step1 raw11633step1Labels = mixedMoment B raw11633step2 raw11633step2Labels := by
      have ha : raw11633step2 = -raw11633step1 := by apply Matrix.ext; change ∀ i j, raw11633step2 i j = -(raw11633step1 i j); unfold raw11633step2 raw11633step1; decide +kernel
      have hl : raw11633step2Labels = raw11633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11633step2 raw11633step2Labels = mixedMoment B raw11633step3 raw11633step3Labels := by
      have ha : raw11633step3 = raw11633step2 := by apply Matrix.ext; unfold raw11633step3 raw11633step2; decide +kernel
      have hl : raw11633step2Labels = labelEmbedding1 ∘ raw11633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11633step2 raw11633step2Labels raw11633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

theorem sound1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1721 node1721Labels = Sparse.eval nodeValue1721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1721) = mixedMoment B node1721 node1721Labels := rfl
  simpa [nodeValue1721, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1734 node1734Labels = Sparse.eval nodeValue1734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1734) = mixedMoment B node1734 node1734Labels := rfl
  simpa [nodeValue1734, Sparse.eval] using hc.symm

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1742 node1742Labels = Sparse.eval nodeValue1742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1742) = mixedMoment B node1742 node1742Labels := rfl
  simpa [nodeValue1742, Sparse.eval] using hc.symm

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

theorem sound1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1822 node1822Labels = Sparse.eval nodeValue1822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1822) = mixedMoment B node1822 node1822Labels := rfl
  simpa [nodeValue1822, Sparse.eval] using hc.symm

theorem sound1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1824 node1824Labels = Sparse.eval nodeValue1824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1824) = mixedMoment B node1824 node1824Labels := rfl
  simpa [nodeValue1824, Sparse.eval] using hc.symm

theorem sound1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1825 node1825Labels = Sparse.eval nodeValue1825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1825) = mixedMoment B node1825 node1825Labels := rfl
  simpa [nodeValue1825, Sparse.eval] using hc.symm

theorem sound1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1827 node1827Labels = Sparse.eval nodeValue1827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1827) = mixedMoment B node1827 node1827Labels := rfl
  simpa [nodeValue1827, Sparse.eval] using hc.symm

theorem sound1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1828 node1828Labels = Sparse.eval nodeValue1828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1828) = mixedMoment B node1828 node1828Labels := rfl
  simpa [nodeValue1828, Sparse.eval] using hc.symm

theorem sound1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1829 node1829Labels = Sparse.eval nodeValue1829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1829) = mixedMoment B node1829 node1829Labels := rfl
  simpa [nodeValue1829, Sparse.eval] using hc.symm

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

theorem zero1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1908 node1908Labels = 0 := by
  exact mixedMoment_order_one B hB node1908 node1908Labels 1
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

theorem sound1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1875 node1875Labels = Sparse.eval nodeValue1875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1875) = mixedMoment B node1875 node1875Labels := rfl
  simpa [nodeValue1875, Sparse.eval] using hc.symm

theorem sound1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1876 node1876Labels = Sparse.eval nodeValue1876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1876) = mixedMoment B node1876 node1876Labels := rfl
  simpa [nodeValue1876, Sparse.eval] using hc.symm

theorem sound1878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1878 node1878Labels = Sparse.eval nodeValue1878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1878) = mixedMoment B node1878 node1878Labels := rfl
  simpa [nodeValue1878, Sparse.eval] using hc.symm

theorem sound1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1908 node1908Labels = Sparse.eval nodeValue1908 (mixedVector B) := by
  simpa only [nodeValue1908, Sparse.eval_nil] using zero1908 B _hB _hF

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

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2179 node2179Labels = Sparse.eval nodeValue2179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2179) = mixedMoment B node2179 node2179Labels := rfl
  simpa [nodeValue2179, Sparse.eval] using hc.symm

theorem sound2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2180 node2180Labels = Sparse.eval nodeValue2180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2180) = mixedMoment B node2180 node2180Labels := rfl
  simpa [nodeValue2180, Sparse.eval] using hc.symm

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2198 node2198Labels = Sparse.eval nodeValue2198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2198) = mixedMoment B node2198 node2198Labels := rfl
  simpa [nodeValue2198, Sparse.eval] using hc.symm

theorem sound2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2199 node2199Labels = Sparse.eval nodeValue2199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2199) = mixedMoment B node2199 node2199Labels := rfl
  simpa [nodeValue2199, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2211 node2211Labels = Sparse.eval nodeValue2211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2211) = mixedMoment B node2211 node2211Labels := rfl
  simpa [nodeValue2211, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

theorem sound2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2238 node2238Labels = Sparse.eval nodeValue2238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2238) = mixedMoment B node2238 node2238Labels := rfl
  simpa [nodeValue2238, Sparse.eval] using hc.symm

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

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

theorem sound2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2248 node2248Labels = Sparse.eval nodeValue2248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2248) = mixedMoment B node2248 node2248Labels := rfl
  simpa [nodeValue2248, Sparse.eval] using hc.symm

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2256 node2256Labels = Sparse.eval nodeValue2256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2256) = mixedMoment B node2256 node2256Labels := rfl
  simpa [nodeValue2256, Sparse.eval] using hc.symm

theorem sound2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2257 node2257Labels = Sparse.eval nodeValue2257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2257) = mixedMoment B node2257 node2257Labels := rfl
  simpa [nodeValue2257, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2272 node2272Labels = Sparse.eval nodeValue2272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2272) = mixedMoment B node2272 node2272Labels := rfl
  simpa [nodeValue2272, Sparse.eval] using hc.symm

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2652 node2652Labels = Sparse.eval nodeValue2652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2652) = mixedMoment B node2652 node2652Labels := rfl
  simpa [nodeValue2652, Sparse.eval] using hc.symm

theorem sound2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2657 node2657Labels = Sparse.eval nodeValue2657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2657) = mixedMoment B node2657 node2657Labels := rfl
  simpa [nodeValue2657, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem zero2689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2689 node2689Labels = 0 := by
  exact mixedMoment_alpha B hF node2689 node2689Labels 1 permutation216
    (by decide +kernel)

theorem zero2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = 0 := by
  exact mixedMoment_alpha B hF node2693 node2693Labels 1 permutation213
    (by decide +kernel)

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2688 node2688Labels = Sparse.eval nodeValue2688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2688) = mixedMoment B node2688 node2688Labels := rfl
  simpa [nodeValue2688, Sparse.eval] using hc.symm

theorem sound2689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2689 node2689Labels = Sparse.eval nodeValue2689 (mixedVector B) := by
  simpa only [nodeValue2689, Sparse.eval_nil] using zero2689 B _hB _hF

theorem sound2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = Sparse.eval nodeValue2693 (mixedVector B) := by
  simpa only [nodeValue2693, Sparse.eval_nil] using zero2693 B _hB _hF

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2728 node2728Labels = Sparse.eval nodeValue2728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2728) = mixedMoment B node2728 node2728Labels := rfl
  simpa [nodeValue2728, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

theorem sound2748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2748 node2748Labels = Sparse.eval nodeValue2748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2748) = mixedMoment B node2748 node2748Labels := rfl
  simpa [nodeValue2748, Sparse.eval] using hc.symm

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

theorem sound2760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2760 node2760Labels = Sparse.eval nodeValue2760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2760) = mixedMoment B node2760 node2760Labels := rfl
  simpa [nodeValue2760, Sparse.eval] using hc.symm

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3024 node3024Labels = Sparse.eval nodeValue3024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3024) = mixedMoment B node3024 node3024Labels := rfl
  simpa [nodeValue3024, Sparse.eval] using hc.symm

theorem sound3058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3058 node3058Labels = Sparse.eval nodeValue3058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3058) = mixedMoment B node3058 node3058Labels := rfl
  simpa [nodeValue3058, Sparse.eval] using hc.symm

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

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3079 node3079Labels = Sparse.eval nodeValue3079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3079) = mixedMoment B node3079 node3079Labels := rfl
  simpa [nodeValue3079, Sparse.eval] using hc.symm

theorem sound3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3096 node3096Labels = Sparse.eval nodeValue3096 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3096) = mixedMoment B node3096 node3096Labels := rfl
  simpa [nodeValue3096, Sparse.eval] using hc.symm

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

theorem sound3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3255 node3255Labels = Sparse.eval nodeValue3255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3255) = mixedMoment B node3255 node3255Labels := rfl
  simpa [nodeValue3255, Sparse.eval] using hc.symm

theorem sound3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3256 node3256Labels = Sparse.eval nodeValue3256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3256) = mixedMoment B node3256 node3256Labels := rfl
  simpa [nodeValue3256, Sparse.eval] using hc.symm

theorem sound3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3258 node3258Labels = Sparse.eval nodeValue3258 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3258) = mixedMoment B node3258 node3258Labels := rfl
  simpa [nodeValue3258, Sparse.eval] using hc.symm

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

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

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

theorem zero3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = 0 := by
  exact mixedMoment_alpha B hF node3403 node3403Labels 1 permutation485
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

theorem sound3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3403 node3403Labels = Sparse.eval nodeValue3403 (mixedVector B) := by
  simpa only [nodeValue3403, Sparse.eval_nil] using zero3403 B _hB _hF

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3444 node3444Labels = Sparse.eval nodeValue3444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3444) = mixedMoment B node3444 node3444Labels := rfl
  simpa [nodeValue3444, Sparse.eval] using hc.symm

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

theorem sound3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3458 node3458Labels = Sparse.eval nodeValue3458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3458) = mixedMoment B node3458 node3458Labels := rfl
  simpa [nodeValue3458, Sparse.eval] using hc.symm

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3462 node3462Labels = Sparse.eval nodeValue3462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3462) = mixedMoment B node3462 node3462Labels := rfl
  simpa [nodeValue3462, Sparse.eval] using hc.symm

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

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

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

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

theorem sourceEq2415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2415 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2415 + difference 0 0) (sourceB2415 + difference 0 0) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3444) := by
    have ha : (tripleCharges (sourceA2415 + difference 0 0) (sourceB2415 + difference 0 0) sourceC2415) = raw33149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33149; decide +kernel
    rw [ha]
    exact (canonical33149 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2415 + difference 1 0) (sourceB2415 + difference 0 1) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2415 + difference 1 0) (sourceB2415 + difference 0 1) sourceC2415) = raw33150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33150; decide +kernel
    rw [ha]
    exact (canonical33150 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2415 + difference 2 0) (sourceB2415 + difference 0 2) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2415 + difference 2 0) (sourceB2415 + difference 0 2) sourceC2415) = raw33151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33151; decide +kernel
    rw [ha]
    exact (canonical33151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2415 + difference 3 0) (sourceB2415 + difference 0 3) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2415 + difference 3 0) (sourceB2415 + difference 0 3) sourceC2415) = raw33152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33152; decide +kernel
    rw [ha]
    exact (canonical33152 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2415 + difference 4 0) (sourceB2415 + difference 0 4) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA2415 + difference 4 0) (sourceB2415 + difference 0 4) sourceC2415) = raw33153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33153; decide +kernel
    rw [ha]
    exact (canonical33153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2415 + difference 5 0) (sourceB2415 + difference 0 5) sourceC2415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2415 + difference 5 0) (sourceB2415 + difference 0 5) sourceC2415) = raw33154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2415 sourceB2415 sourceC2415 difference raw33154; decide +kernel
    rw [ha]
    exact (canonical33154 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2415 + sourceB2415) sourceC2415) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2415 + sourceB2415) sourceC2415) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2415 sourceB2415 sourceC2415 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2415 sourceB2415 sourceC2415
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2415, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 1) (sourceB2417 + difference 1 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 1) (sourceB2417 + difference 1 0) sourceC2417) = raw33177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33177; decide +kernel
    rw [ha]
    exact (canonical33177 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 2) (sourceB2417 + difference 2 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 2) (sourceB2417 + difference 2 0) sourceC2417) = raw33178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33178; decide +kernel
    rw [ha]
    exact (canonical33178 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 3) (sourceB2417 + difference 3 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 3) (sourceB2417 + difference 3 0) sourceC2417) = raw33179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33179; decide +kernel
    rw [ha]
    exact (canonical33179 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 4) (sourceB2417 + difference 4 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 4) (sourceB2417 + difference 4 0) sourceC2417) = raw33180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33180; decide +kernel
    rw [ha]
    exact (canonical33180 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2417 + difference 0 5) (sourceB2417 + difference 5 0) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA2417 + difference 0 5) (sourceB2417 + difference 5 0) sourceC2417) = raw11604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11604; decide +kernel
    rw [ha]
    exact (canonical11604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 0) (sourceB2417 + difference 0 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 0) (sourceB2417 + difference 0 1) sourceC2417) = raw11629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11629; decide +kernel
    rw [ha]
    exact (canonical11629 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 2) (sourceB2417 + difference 2 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 2) (sourceB2417 + difference 2 1) sourceC2417) = raw11631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11631; decide +kernel
    rw [ha]
    exact (canonical11631 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 3) (sourceB2417 + difference 3 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 3) (sourceB2417 + difference 3 1) sourceC2417) = raw11632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11632; decide +kernel
    rw [ha]
    exact (canonical11632 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 4) (sourceB2417 + difference 4 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 4) (sourceB2417 + difference 4 1) sourceC2417) = raw11633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11633; decide +kernel
    rw [ha]
    exact (canonical11633 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2417 + difference 1 5) (sourceB2417 + difference 5 1) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA2417 + difference 1 5) (sourceB2417 + difference 5 1) sourceC2417) = raw33181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33181; decide +kernel
    rw [ha]
    exact (canonical33181 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 0) (sourceB2417 + difference 0 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3256) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 0) (sourceB2417 + difference 0 2) sourceC2417) = raw33182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33182; decide +kernel
    rw [ha]
    exact (canonical33182 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 1) (sourceB2417 + difference 1 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3404) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 1) (sourceB2417 + difference 1 2) sourceC2417) = raw33183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33183; decide +kernel
    rw [ha]
    exact (canonical33183 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 3) (sourceB2417 + difference 3 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 3) (sourceB2417 + difference 3 2) sourceC2417) = raw33184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33184; decide +kernel
    rw [ha]
    exact (canonical33184 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 4) (sourceB2417 + difference 4 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 4) (sourceB2417 + difference 4 2) sourceC2417) = raw33185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33185; decide +kernel
    rw [ha]
    exact (canonical33185 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2417 + difference 2 5) (sourceB2417 + difference 5 2) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA2417 + difference 2 5) (sourceB2417 + difference 5 2) sourceC2417) = raw11615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11615; decide +kernel
    rw [ha]
    exact (canonical11615 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 0) (sourceB2417 + difference 0 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 0) (sourceB2417 + difference 0 3) sourceC2417) = raw33186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33186; decide +kernel
    rw [ha]
    exact (canonical33186 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 1) (sourceB2417 + difference 1 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 1) (sourceB2417 + difference 1 3) sourceC2417) = raw33187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33187; decide +kernel
    rw [ha]
    exact (canonical33187 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 2) (sourceB2417 + difference 2 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 2) (sourceB2417 + difference 2 3) sourceC2417) = raw33188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33188; decide +kernel
    rw [ha]
    exact (canonical33188 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 4) (sourceB2417 + difference 4 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 4) (sourceB2417 + difference 4 3) sourceC2417) = raw33189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33189; decide +kernel
    rw [ha]
    exact (canonical33189 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2417 + difference 3 5) (sourceB2417 + difference 5 3) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2417 + difference 3 5) (sourceB2417 + difference 5 3) sourceC2417) = raw11620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11620; decide +kernel
    rw [ha]
    exact (canonical11620 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 0) (sourceB2417 + difference 0 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 0) (sourceB2417 + difference 0 4) sourceC2417) = raw33190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33190; decide +kernel
    rw [ha]
    exact (canonical33190 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 1) (sourceB2417 + difference 1 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 1) (sourceB2417 + difference 1 4) sourceC2417) = raw33191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33191; decide +kernel
    rw [ha]
    exact (canonical33191 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 2) (sourceB2417 + difference 2 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 2) (sourceB2417 + difference 2 4) sourceC2417) = raw33192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33192; decide +kernel
    rw [ha]
    exact (canonical33192 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 3) (sourceB2417 + difference 3 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 3) (sourceB2417 + difference 3 4) sourceC2417) = raw33193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33193; decide +kernel
    rw [ha]
    exact (canonical33193 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2417 + difference 4 5) (sourceB2417 + difference 5 4) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2417 + difference 4 5) (sourceB2417 + difference 5 4) sourceC2417) = raw11625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw11625; decide +kernel
    rw [ha]
    exact (canonical11625 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 0) (sourceB2417 + difference 0 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 0) (sourceB2417 + difference 0 5) sourceC2417) = raw33194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33194; decide +kernel
    rw [ha]
    exact (canonical33194 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 1) (sourceB2417 + difference 1 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 1) (sourceB2417 + difference 1 5) sourceC2417) = raw33195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33195; decide +kernel
    rw [ha]
    exact (canonical33195 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 2) (sourceB2417 + difference 2 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 2) (sourceB2417 + difference 2 5) sourceC2417) = raw33196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33196; decide +kernel
    rw [ha]
    exact (canonical33196 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 3) (sourceB2417 + difference 3 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 3) (sourceB2417 + difference 3 5) sourceC2417) = raw33197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33197; decide +kernel
    rw [ha]
    exact (canonical33197 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2417 + difference 5 4) (sourceB2417 + difference 4 5) sourceC2417) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2417 + difference 5 4) (sourceB2417 + difference 4 5) sourceC2417) = raw33198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2417 sourceB2417 sourceC2417 difference raw33198; decide +kernel
    rw [ha]
    exact (canonical33198 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2417 sourceB2417 sourceC2417
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2417, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2426 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 1) (sourceB2426 + difference 1 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 1) (sourceB2426 + difference 1 0) sourceC2426) = raw33324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33324; decide +kernel
    rw [ha]
    exact (canonical33324 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 2) (sourceB2426 + difference 2 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 2) (sourceB2426 + difference 2 0) sourceC2426) = raw33325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33325; decide +kernel
    rw [ha]
    exact (canonical33325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 3) (sourceB2426 + difference 3 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 3) (sourceB2426 + difference 3 0) sourceC2426) = raw29097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29097; decide +kernel
    rw [ha]
    exact (canonical29097 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 4) (sourceB2426 + difference 4 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 4) (sourceB2426 + difference 4 0) sourceC2426) = raw33326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33326; decide +kernel
    rw [ha]
    exact (canonical33326 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2426 + difference 0 5) (sourceB2426 + difference 5 0) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2426 + difference 0 5) (sourceB2426 + difference 5 0) sourceC2426) = raw33327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33327; decide +kernel
    rw [ha]
    exact (canonical33327 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 0) (sourceB2426 + difference 0 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 0) (sourceB2426 + difference 0 1) sourceC2426) = raw33328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33328; decide +kernel
    rw [ha]
    exact (canonical33328 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 2) (sourceB2426 + difference 2 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 2) (sourceB2426 + difference 2 1) sourceC2426) = raw33329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33329; decide +kernel
    rw [ha]
    exact (canonical33329 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 3) (sourceB2426 + difference 3 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 3) (sourceB2426 + difference 3 1) sourceC2426) = raw29102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29102; decide +kernel
    rw [ha]
    exact (canonical29102 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 4) (sourceB2426 + difference 4 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 4) (sourceB2426 + difference 4 1) sourceC2426) = raw33330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33330; decide +kernel
    rw [ha]
    exact (canonical33330 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2426 + difference 1 5) (sourceB2426 + difference 5 1) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA2426 + difference 1 5) (sourceB2426 + difference 5 1) sourceC2426) = raw33331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33331; decide +kernel
    rw [ha]
    exact (canonical33331 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 0) (sourceB2426 + difference 0 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2688) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 0) (sourceB2426 + difference 0 2) sourceC2426) = raw33332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33332; decide +kernel
    rw [ha]
    exact (canonical33332 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 1) (sourceB2426 + difference 1 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2689) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 1) (sourceB2426 + difference 1 2) sourceC2426) = raw33333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33333; decide +kernel
    rw [ha]
    exact (canonical33333 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 3) (sourceB2426 + difference 3 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 3) (sourceB2426 + difference 3 2) sourceC2426) = raw29107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29107; decide +kernel
    rw [ha]
    exact (canonical29107 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 4) (sourceB2426 + difference 4 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 4) (sourceB2426 + difference 4 2) sourceC2426) = raw33334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33334; decide +kernel
    rw [ha]
    exact (canonical33334 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2426 + difference 2 5) (sourceB2426 + difference 5 2) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA2426 + difference 2 5) (sourceB2426 + difference 5 2) sourceC2426) = raw33335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33335; decide +kernel
    rw [ha]
    exact (canonical33335 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 0) (sourceB2426 + difference 0 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 0) (sourceB2426 + difference 0 3) sourceC2426) = raw33336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33336; decide +kernel
    rw [ha]
    exact (canonical33336 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 1) (sourceB2426 + difference 1 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 1) (sourceB2426 + difference 1 3) sourceC2426) = raw33337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33337; decide +kernel
    rw [ha]
    exact (canonical33337 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 2) (sourceB2426 + difference 2 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 2) (sourceB2426 + difference 2 3) sourceC2426) = raw33338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33338; decide +kernel
    rw [ha]
    exact (canonical33338 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 4) (sourceB2426 + difference 4 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 4) (sourceB2426 + difference 4 3) sourceC2426) = raw33339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33339; decide +kernel
    rw [ha]
    exact (canonical33339 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2426 + difference 3 5) (sourceB2426 + difference 5 3) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2426 + difference 3 5) (sourceB2426 + difference 5 3) sourceC2426) = raw33340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33340; decide +kernel
    rw [ha]
    exact (canonical33340 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 0) (sourceB2426 + difference 0 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 0) (sourceB2426 + difference 0 4) sourceC2426) = raw33341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33341; decide +kernel
    rw [ha]
    exact (canonical33341 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 1) (sourceB2426 + difference 1 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 1) (sourceB2426 + difference 1 4) sourceC2426) = raw33342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33342; decide +kernel
    rw [ha]
    exact (canonical33342 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 2) (sourceB2426 + difference 2 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 2) (sourceB2426 + difference 2 4) sourceC2426) = raw33343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33343; decide +kernel
    rw [ha]
    exact (canonical33343 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 3) (sourceB2426 + difference 3 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 3) (sourceB2426 + difference 3 4) sourceC2426) = raw29117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29117; decide +kernel
    rw [ha]
    exact (canonical29117 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2426 + difference 4 5) (sourceB2426 + difference 5 4) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2426 + difference 4 5) (sourceB2426 + difference 5 4) sourceC2426) = raw33344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33344; decide +kernel
    rw [ha]
    exact (canonical33344 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 0) (sourceB2426 + difference 0 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 0) (sourceB2426 + difference 0 5) sourceC2426) = raw29108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29108; decide +kernel
    rw [ha]
    exact (canonical29108 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 1) (sourceB2426 + difference 1 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 1) (sourceB2426 + difference 1 5) sourceC2426) = raw29109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29109; decide +kernel
    rw [ha]
    exact (canonical29109 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 2) (sourceB2426 + difference 2 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 2) (sourceB2426 + difference 2 5) sourceC2426) = raw29110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29110; decide +kernel
    rw [ha]
    exact (canonical29110 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 3) (sourceB2426 + difference 3 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 3) (sourceB2426 + difference 3 5) sourceC2426) = raw33345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw33345; decide +kernel
    rw [ha]
    exact (canonical33345 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2426 + difference 5 4) (sourceB2426 + difference 4 5) sourceC2426) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2426 + difference 5 4) (sourceB2426 + difference 4 5) sourceC2426) = raw29111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2426 sourceB2426 sourceC2426 difference raw29111; decide +kernel
    rw [ha]
    exact (canonical29111 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2426 sourceB2426 sourceC2426
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2426, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2440 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 1) (sourceB2440 + difference 1 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 1) (sourceB2440 + difference 1 0) sourceC2440) = raw33489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33489; decide +kernel
    rw [ha]
    exact (canonical33489 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 2) (sourceB2440 + difference 2 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 2) (sourceB2440 + difference 2 0) sourceC2440) = raw33490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33490; decide +kernel
    rw [ha]
    exact (canonical33490 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 3) (sourceB2440 + difference 3 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 3) (sourceB2440 + difference 3 0) sourceC2440) = raw33491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33491; decide +kernel
    rw [ha]
    exact (canonical33491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 4) (sourceB2440 + difference 4 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 4) (sourceB2440 + difference 4 0) sourceC2440) = raw33492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33492; decide +kernel
    rw [ha]
    exact (canonical33492 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2440 + difference 0 5) (sourceB2440 + difference 5 0) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2440 + difference 0 5) (sourceB2440 + difference 5 0) sourceC2440) = raw33493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33493; decide +kernel
    rw [ha]
    exact (canonical33493 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 0) (sourceB2440 + difference 0 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 0) (sourceB2440 + difference 0 1) sourceC2440) = raw33494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33494; decide +kernel
    rw [ha]
    exact (canonical33494 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 2) (sourceB2440 + difference 2 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 2) (sourceB2440 + difference 2 1) sourceC2440) = raw25026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25026; decide +kernel
    rw [ha]
    exact (canonical25026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 3) (sourceB2440 + difference 3 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 3) (sourceB2440 + difference 3 1) sourceC2440) = raw25027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25027; decide +kernel
    rw [ha]
    exact (canonical25027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 4) (sourceB2440 + difference 4 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 4) (sourceB2440 + difference 4 1) sourceC2440) = raw25028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25028; decide +kernel
    rw [ha]
    exact (canonical25028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2440 + difference 1 5) (sourceB2440 + difference 5 1) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2440 + difference 1 5) (sourceB2440 + difference 5 1) sourceC2440) = raw25029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25029; decide +kernel
    rw [ha]
    exact (canonical25029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 0) (sourceB2440 + difference 0 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 0) (sourceB2440 + difference 0 2) sourceC2440) = raw25036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25036; decide +kernel
    rw [ha]
    exact (canonical25036 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 1) (sourceB2440 + difference 1 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 1) (sourceB2440 + difference 1 2) sourceC2440) = raw33495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33495; decide +kernel
    rw [ha]
    exact (canonical33495 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 3) (sourceB2440 + difference 3 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 3) (sourceB2440 + difference 3 2) sourceC2440) = raw33496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33496; decide +kernel
    rw [ha]
    exact (canonical33496 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 4) (sourceB2440 + difference 4 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 4) (sourceB2440 + difference 4 2) sourceC2440) = raw33497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33497; decide +kernel
    rw [ha]
    exact (canonical33497 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2440 + difference 2 5) (sourceB2440 + difference 5 2) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA2440 + difference 2 5) (sourceB2440 + difference 5 2) sourceC2440) = raw33498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33498; decide +kernel
    rw [ha]
    exact (canonical33498 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 0) (sourceB2440 + difference 0 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 0) (sourceB2440 + difference 0 3) sourceC2440) = raw25041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25041; decide +kernel
    rw [ha]
    exact (canonical25041 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 1) (sourceB2440 + difference 1 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 1) (sourceB2440 + difference 1 3) sourceC2440) = raw33499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33499; decide +kernel
    rw [ha]
    exact (canonical33499 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 2) (sourceB2440 + difference 2 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 2) (sourceB2440 + difference 2 3) sourceC2440) = raw33500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33500; decide +kernel
    rw [ha]
    exact (canonical33500 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 4) (sourceB2440 + difference 4 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 4) (sourceB2440 + difference 4 3) sourceC2440) = raw33501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33501; decide +kernel
    rw [ha]
    exact (canonical33501 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2440 + difference 3 5) (sourceB2440 + difference 5 3) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2440 + difference 3 5) (sourceB2440 + difference 5 3) sourceC2440) = raw33502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33502; decide +kernel
    rw [ha]
    exact (canonical33502 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 0) (sourceB2440 + difference 0 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 0) (sourceB2440 + difference 0 4) sourceC2440) = raw25046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25046; decide +kernel
    rw [ha]
    exact (canonical25046 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 1) (sourceB2440 + difference 1 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 1) (sourceB2440 + difference 1 4) sourceC2440) = raw33503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33503; decide +kernel
    rw [ha]
    exact (canonical33503 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 2) (sourceB2440 + difference 2 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 2) (sourceB2440 + difference 2 4) sourceC2440) = raw33504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33504; decide +kernel
    rw [ha]
    exact (canonical33504 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 3) (sourceB2440 + difference 3 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 3) (sourceB2440 + difference 3 4) sourceC2440) = raw33505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33505; decide +kernel
    rw [ha]
    exact (canonical33505 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2440 + difference 4 5) (sourceB2440 + difference 5 4) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2440 + difference 4 5) (sourceB2440 + difference 5 4) sourceC2440) = raw33506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33506; decide +kernel
    rw [ha]
    exact (canonical33506 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 0) (sourceB2440 + difference 0 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 0) (sourceB2440 + difference 0 5) sourceC2440) = raw25051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw25051; decide +kernel
    rw [ha]
    exact (canonical25051 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 1) (sourceB2440 + difference 1 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 1) (sourceB2440 + difference 1 5) sourceC2440) = raw33507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33507; decide +kernel
    rw [ha]
    exact (canonical33507 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 2) (sourceB2440 + difference 2 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 2) (sourceB2440 + difference 2 5) sourceC2440) = raw33508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33508; decide +kernel
    rw [ha]
    exact (canonical33508 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 3) (sourceB2440 + difference 3 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 3) (sourceB2440 + difference 3 5) sourceC2440) = raw33509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33509; decide +kernel
    rw [ha]
    exact (canonical33509 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2440 + difference 5 4) (sourceB2440 + difference 4 5) sourceC2440) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2440 + difference 5 4) (sourceB2440 + difference 4 5) sourceC2440) = raw33510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2440 sourceB2440 sourceC2440 difference raw33510; decide +kernel
    rw [ha]
    exact (canonical33510 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2440 sourceB2440 sourceC2440
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2440, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2441 + difference 0 1) (sourceB2441 + difference 1 0) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA2441 + difference 0 1) (sourceB2441 + difference 1 0) sourceC2441) = raw33511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33511; decide +kernel
    rw [ha]
    exact (canonical33511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2441 + difference 1 1) (sourceB2441 + difference 1 1) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2441 + difference 1 1) (sourceB2441 + difference 1 1) sourceC2441) = raw25062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw25062; decide +kernel
    rw [ha]
    exact (canonical25062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2441 + difference 2 1) (sourceB2441 + difference 1 2) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1824) := by
    have ha : (tripleCharges (sourceA2441 + difference 2 1) (sourceB2441 + difference 1 2) sourceC2441) = raw33512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33512; decide +kernel
    rw [ha]
    exact (canonical33512 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2441 + difference 3 1) (sourceB2441 + difference 1 3) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2441 + difference 3 1) (sourceB2441 + difference 1 3) sourceC2441) = raw33513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33513; decide +kernel
    rw [ha]
    exact (canonical33513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2441 + difference 4 1) (sourceB2441 + difference 1 4) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2441 + difference 4 1) (sourceB2441 + difference 1 4) sourceC2441) = raw33514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33514; decide +kernel
    rw [ha]
    exact (canonical33514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2441 + difference 5 1) (sourceB2441 + difference 1 5) sourceC2441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA2441 + difference 5 1) (sourceB2441 + difference 1 5) sourceC2441) = raw33515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2441 sourceB2441 sourceC2441 difference raw33515; decide +kernel
    rw [ha]
    exact (canonical33515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2441 + sourceB2441) sourceC2441) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2441 + sourceB2441) sourceC2441) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA2441 sourceB2441 sourceC2441 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2441 sourceB2441 sourceC2441
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2441, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2446 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 1) (sourceB2446 + difference 1 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 1) (sourceB2446 + difference 1 0) sourceC2446) = raw33591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33591; decide +kernel
    rw [ha]
    exact (canonical33591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 2) (sourceB2446 + difference 2 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 2) (sourceB2446 + difference 2 0) sourceC2446) = raw33592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33592; decide +kernel
    rw [ha]
    exact (canonical33592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 3) (sourceB2446 + difference 3 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 3) (sourceB2446 + difference 3 0) sourceC2446) = raw33593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33593; decide +kernel
    rw [ha]
    exact (canonical33593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 4) (sourceB2446 + difference 4 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 4) (sourceB2446 + difference 4 0) sourceC2446) = raw33594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33594; decide +kernel
    rw [ha]
    exact (canonical33594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2446 + difference 0 5) (sourceB2446 + difference 5 0) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2446 + difference 0 5) (sourceB2446 + difference 5 0) sourceC2446) = raw33595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33595; decide +kernel
    rw [ha]
    exact (canonical33595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 0) (sourceB2446 + difference 0 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 0) (sourceB2446 + difference 0 1) sourceC2446) = raw33596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33596; decide +kernel
    rw [ha]
    exact (canonical33596 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 2) (sourceB2446 + difference 2 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 2) (sourceB2446 + difference 2 1) sourceC2446) = raw25196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25196; decide +kernel
    rw [ha]
    exact (canonical25196 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 3) (sourceB2446 + difference 3 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 3) (sourceB2446 + difference 3 1) sourceC2446) = raw25197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25197; decide +kernel
    rw [ha]
    exact (canonical25197 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 4) (sourceB2446 + difference 4 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 4) (sourceB2446 + difference 4 1) sourceC2446) = raw25198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25198; decide +kernel
    rw [ha]
    exact (canonical25198 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2446 + difference 1 5) (sourceB2446 + difference 5 1) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2446 + difference 1 5) (sourceB2446 + difference 5 1) sourceC2446) = raw25199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25199; decide +kernel
    rw [ha]
    exact (canonical25199 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 0) (sourceB2446 + difference 0 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 0) (sourceB2446 + difference 0 2) sourceC2446) = raw25206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25206; decide +kernel
    rw [ha]
    exact (canonical25206 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 1) (sourceB2446 + difference 1 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 1) (sourceB2446 + difference 1 2) sourceC2446) = raw33597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33597; decide +kernel
    rw [ha]
    exact (canonical33597 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 3) (sourceB2446 + difference 3 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 3) (sourceB2446 + difference 3 2) sourceC2446) = raw33598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33598; decide +kernel
    rw [ha]
    exact (canonical33598 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 4) (sourceB2446 + difference 4 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 4) (sourceB2446 + difference 4 2) sourceC2446) = raw33599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33599; decide +kernel
    rw [ha]
    exact (canonical33599 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2446 + difference 2 5) (sourceB2446 + difference 5 2) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA2446 + difference 2 5) (sourceB2446 + difference 5 2) sourceC2446) = raw33600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33600; decide +kernel
    rw [ha]
    exact (canonical33600 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 0) (sourceB2446 + difference 0 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 0) (sourceB2446 + difference 0 3) sourceC2446) = raw25211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25211; decide +kernel
    rw [ha]
    exact (canonical25211 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 1) (sourceB2446 + difference 1 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 1) (sourceB2446 + difference 1 3) sourceC2446) = raw33601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33601; decide +kernel
    rw [ha]
    exact (canonical33601 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 2) (sourceB2446 + difference 2 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 2) (sourceB2446 + difference 2 3) sourceC2446) = raw33602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33602; decide +kernel
    rw [ha]
    exact (canonical33602 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 4) (sourceB2446 + difference 4 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 4) (sourceB2446 + difference 4 3) sourceC2446) = raw33603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33603; decide +kernel
    rw [ha]
    exact (canonical33603 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2446 + difference 3 5) (sourceB2446 + difference 5 3) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2446 + difference 3 5) (sourceB2446 + difference 5 3) sourceC2446) = raw33604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33604; decide +kernel
    rw [ha]
    exact (canonical33604 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 0) (sourceB2446 + difference 0 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 0) (sourceB2446 + difference 0 4) sourceC2446) = raw25216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25216; decide +kernel
    rw [ha]
    exact (canonical25216 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 1) (sourceB2446 + difference 1 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 1) (sourceB2446 + difference 1 4) sourceC2446) = raw33605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33605; decide +kernel
    rw [ha]
    exact (canonical33605 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 2) (sourceB2446 + difference 2 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 2) (sourceB2446 + difference 2 4) sourceC2446) = raw33606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33606; decide +kernel
    rw [ha]
    exact (canonical33606 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 3) (sourceB2446 + difference 3 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 3) (sourceB2446 + difference 3 4) sourceC2446) = raw33607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33607; decide +kernel
    rw [ha]
    exact (canonical33607 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2446 + difference 4 5) (sourceB2446 + difference 5 4) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2446 + difference 4 5) (sourceB2446 + difference 5 4) sourceC2446) = raw33608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33608; decide +kernel
    rw [ha]
    exact (canonical33608 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 0) (sourceB2446 + difference 0 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 0) (sourceB2446 + difference 0 5) sourceC2446) = raw25221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw25221; decide +kernel
    rw [ha]
    exact (canonical25221 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 1) (sourceB2446 + difference 1 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 1) (sourceB2446 + difference 1 5) sourceC2446) = raw33609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33609; decide +kernel
    rw [ha]
    exact (canonical33609 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 2) (sourceB2446 + difference 2 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 2) (sourceB2446 + difference 2 5) sourceC2446) = raw33610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33610; decide +kernel
    rw [ha]
    exact (canonical33610 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 3) (sourceB2446 + difference 3 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 3) (sourceB2446 + difference 3 5) sourceC2446) = raw33611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33611; decide +kernel
    rw [ha]
    exact (canonical33611 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2446 + difference 5 4) (sourceB2446 + difference 4 5) sourceC2446) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2446 + difference 5 4) (sourceB2446 + difference 4 5) sourceC2446) = raw33612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2446 sourceB2446 sourceC2446 difference raw33612; decide +kernel
    rw [ha]
    exact (canonical33612 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2446 sourceB2446 sourceC2446
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2446, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2447 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2447 + difference 0 1) (sourceB2447 + difference 1 0) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA2447 + difference 0 1) (sourceB2447 + difference 1 0) sourceC2447) = raw33613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33613; decide +kernel
    rw [ha]
    exact (canonical33613 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2447 + difference 1 1) (sourceB2447 + difference 1 1) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2447 + difference 1 1) (sourceB2447 + difference 1 1) sourceC2447) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2447 + difference 2 1) (sourceB2447 + difference 1 2) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1822) := by
    have ha : (tripleCharges (sourceA2447 + difference 2 1) (sourceB2447 + difference 1 2) sourceC2447) = raw33614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33614; decide +kernel
    rw [ha]
    exact (canonical33614 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2447 + difference 3 1) (sourceB2447 + difference 1 3) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2447 + difference 3 1) (sourceB2447 + difference 1 3) sourceC2447) = raw33615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw33615; decide +kernel
    rw [ha]
    exact (canonical33615 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2447 + difference 4 1) (sourceB2447 + difference 1 4) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2447 + difference 4 1) (sourceB2447 + difference 1 4) sourceC2447) = raw29343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw29343; decide +kernel
    rw [ha]
    exact (canonical29343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2447 + difference 5 1) (sourceB2447 + difference 1 5) sourceC2447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1825) := by
    have ha : (tripleCharges (sourceA2447 + difference 5 1) (sourceB2447 + difference 1 5) sourceC2447) = raw27399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2447 sourceB2447 sourceC2447 difference raw27399; decide +kernel
    rw [ha]
    exact (canonical27399 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2447 + sourceB2447) sourceC2447) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2447 + sourceB2447) sourceC2447) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA2447 sourceB2447 sourceC2447 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2447 sourceB2447 sourceC2447
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2447, Integer.Sparse.eval]
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

theorem reindexCheck1955 : Integer.Sparse.reindex keyMap MixedData.row1955 = numericRow1955 := by decide +kernel

theorem numericCheck1955 (x : Master → ℝ) : Integer.Sparse.eval numericRow1955 x =
    (1 : ℝ) * reducedSource1955 x := by
  norm_num [numericRow1955, reducedSource1955, Integer.Sparse.eval, Sparse.eval, nodeValue1875, nodeValue1876, nodeValue1878, nodeValue1908, nodeValue2075, nodeValue3444, nodeValue4080]

theorem reindexCheck1957 : Integer.Sparse.reindex keyMap MixedData.row1957 = numericRow1957 := by decide +kernel

theorem numericCheck1957 (x : Master → ℝ) : Integer.Sparse.eval numericRow1957 x =
    (1 : ℝ) * reducedSource1957 x := by
  norm_num [numericRow1957, reducedSource1957, Integer.Sparse.eval, Sparse.eval, nodeValue3255, nodeValue3256, nodeValue3258, nodeValue3288, nodeValue3403, nodeValue3404, nodeValue3406, nodeValue3458, nodeValue3460, nodeValue3462, nodeValue3463, nodeValue3468, nodeValue3470, nodeValue3478, nodeValue3524, nodeValue3525, nodeValue3533, nodeValue3757, nodeValue3799, nodeValue3800, nodeValue3807]

theorem reindexCheck1959 : Integer.Sparse.reindex keyMap MixedData.row1959 = numericRow1959 := by decide +kernel

theorem numericCheck1959 (x : Master → ℝ) : Integer.Sparse.eval numericRow1959 x =
    (1 : ℝ) * reducedSource1959 x := by
  norm_num [numericRow1959, reducedSource1959, Integer.Sparse.eval, Sparse.eval, nodeValue2173, nodeValue2184, nodeValue2185, nodeValue2228, nodeValue2652, nodeValue2657, nodeValue2658, nodeValue2685, nodeValue2688, nodeValue2689, nodeValue2693, nodeValue2694, nodeValue2702, nodeValue2704, nodeValue2705, nodeValue2740, nodeValue2742, nodeValue3024, nodeValue3058, nodeValue3075, nodeValue3077]

theorem reindexCheck1961 : Integer.Sparse.reindex keyMap MixedData.row1961 = numericRow1961 := by decide +kernel

theorem numericCheck1961 (x : Master → ℝ) : Integer.Sparse.eval numericRow1961 x =
    (1 : ℝ) * reducedSource1961 x := by
  norm_num [numericRow1961, reducedSource1961, Integer.Sparse.eval, Sparse.eval, nodeValue1711, nodeValue1734, nodeValue1737, nodeValue1742, nodeValue2179, nodeValue2180, nodeValue2211, nodeValue2214, nodeValue2220, nodeValue2241, nodeValue2248, nodeValue2250, nodeValue2260, nodeValue2263, nodeValue2272, nodeValue2274, nodeValue2277, nodeValue2728, nodeValue2748, nodeValue2764, nodeValue2773]

theorem reindexCheck1962 : Integer.Sparse.reindex keyMap MixedData.row1962 = numericRow1962 := by decide +kernel

theorem numericCheck1962 (x : Master → ℝ) : Integer.Sparse.eval numericRow1962 x =
    (1 : ℝ) * reducedSource1962 x := by
  norm_num [numericRow1962, reducedSource1962, Integer.Sparse.eval, Sparse.eval, nodeValue1824, nodeValue1828, nodeValue1829, nodeValue2110, nodeValue3079, nodeValue4083]

theorem reindexCheck1966 : Integer.Sparse.reindex keyMap MixedData.row1966 = numericRow1966 := by decide +kernel

theorem numericCheck1966 (x : Master → ℝ) : Integer.Sparse.eval numericRow1966 x =
    (1 : ℝ) * reducedSource1966 x := by
  norm_num [numericRow1966, reducedSource1966, Integer.Sparse.eval, Sparse.eval, nodeValue1703, nodeValue1720, nodeValue1721, nodeValue1724, nodeValue1734, nodeValue2198, nodeValue2199, nodeValue2202, nodeValue2211, nodeValue2238, nodeValue2240, nodeValue2241, nodeValue2256, nodeValue2257, nodeValue2259, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2272, nodeValue2274, nodeValue2275, nodeValue2287, nodeValue2288, nodeValue2291, nodeValue2718, nodeValue2760, nodeValue2763, nodeValue2764, nodeValue2782]

theorem reindexCheck1967 : Integer.Sparse.reindex keyMap MixedData.row1967 = numericRow1967 := by decide +kernel

theorem numericCheck1967 (x : Master → ℝ) : Integer.Sparse.eval numericRow1967 x =
    (1 : ℝ) * reducedSource1967 x := by
  norm_num [numericRow1967, reducedSource1967, Integer.Sparse.eval, Sparse.eval, nodeValue1822, nodeValue1825, nodeValue1827, nodeValue1829, nodeValue2107, nodeValue3096, nodeValue4083]

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

theorem reducedZero1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1955 (mixedVector B) = 0 := by
  have h1875 : mixedVector B (Sum.inr 1875) = Sparse.eval nodeValue1875 (mixedVector B) := by
    change mixedMoment B node1875 node1875Labels = _
    exact sound1875 B hB hF
  have h1876 : mixedVector B (Sum.inr 1876) = Sparse.eval nodeValue1876 (mixedVector B) := by
    change mixedMoment B node1876 node1876Labels = _
    exact sound1876 B hB hF
  have h1878 : mixedVector B (Sum.inr 1878) = Sparse.eval nodeValue1878 (mixedVector B) := by
    change mixedMoment B node1878 node1878Labels = _
    exact sound1878 B hB hF
  have h1908 : mixedVector B (Sum.inr 1908) = Sparse.eval nodeValue1908 (mixedVector B) := by
    change mixedMoment B node1908 node1908Labels = _
    exact sound1908 B hB hF
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h3444 : mixedVector B (Sum.inr 3444) = Sparse.eval nodeValue3444 (mixedVector B) := by
    change mixedMoment B node3444 node3444Labels = _
    exact sound3444 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2415, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1875, h1876, h1878, h1908, h2075, h3444, h4080, reducedSource1955] using sourceEq2415 B hB

theorem rowSound1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1955 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1955, numericCheck1955, reducedZero1955 B hB hF, mul_zero]

theorem reducedZero1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1957 (mixedVector B) = 0 := by
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3256 : mixedVector B (Sum.inr 3256) = Sparse.eval nodeValue3256 (mixedVector B) := by
    change mixedMoment B node3256 node3256Labels = _
    exact sound3256 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3404 : mixedVector B (Sum.inr 3404) = Sparse.eval nodeValue3404 (mixedVector B) := by
    change mixedMoment B node3404 node3404Labels = _
    exact sound3404 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3458 : mixedVector B (Sum.inr 3458) = Sparse.eval nodeValue3458 (mixedVector B) := by
    change mixedMoment B node3458 node3458Labels = _
    exact sound3458 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3462 : mixedVector B (Sum.inr 3462) = Sparse.eval nodeValue3462 (mixedVector B) := by
    change mixedMoment B node3462 node3462Labels = _
    exact sound3462 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  simpa only [sourceForm2417, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3255, h3256, h3258, h3288, h3403, h3404, h3406, h3458, h3460, h3462, h3463, h3468, h3470, h3478, h3524, h3525, h3533, h3757, h3799, h3800, h3807, reducedSource1957] using sourceEq2417 B hB

theorem rowSound1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1957 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1957, numericCheck1957, reducedZero1957 B hB hF, mul_zero]

theorem reducedZero1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1959 (mixedVector B) = 0 := by
  have h2173 : mixedVector B (Sum.inr 2173) = Sparse.eval nodeValue2173 (mixedVector B) := by
    change mixedMoment B node2173 node2173Labels = _
    exact sound2173 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2688 : mixedVector B (Sum.inr 2688) = Sparse.eval nodeValue2688 (mixedVector B) := by
    change mixedMoment B node2688 node2688Labels = _
    exact sound2688 B hB hF
  have h2689 : mixedVector B (Sum.inr 2689) = Sparse.eval nodeValue2689 (mixedVector B) := by
    change mixedMoment B node2689 node2689Labels = _
    exact sound2689 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  simpa only [sourceForm2426, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2173, h2184, h2185, h2228, h2652, h2657, h2658, h2685, h2688, h2689, h2693, h2694, h2702, h2704, h2705, h2740, h2742, h3024, h3058, h3075, h3077, reducedSource1959] using sourceEq2426 B hB

theorem rowSound1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1959 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1959, numericCheck1959, reducedZero1959 B hB hF, mul_zero]

theorem reducedZero1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1961 (mixedVector B) = 0 := by
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1742 : mixedVector B (Sum.inr 1742) = Sparse.eval nodeValue1742 (mixedVector B) := by
    change mixedMoment B node1742 node1742Labels = _
    exact sound1742 B hB hF
  have h2179 : mixedVector B (Sum.inr 2179) = Sparse.eval nodeValue2179 (mixedVector B) := by
    change mixedMoment B node2179 node2179Labels = _
    exact sound2179 B hB hF
  have h2180 : mixedVector B (Sum.inr 2180) = Sparse.eval nodeValue2180 (mixedVector B) := by
    change mixedMoment B node2180 node2180Labels = _
    exact sound2180 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2248 : mixedVector B (Sum.inr 2248) = Sparse.eval nodeValue2248 (mixedVector B) := by
    change mixedMoment B node2248 node2248Labels = _
    exact sound2248 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  simpa only [sourceForm2440, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1711, h1734, h1737, h1742, h2179, h2180, h2211, h2214, h2220, h2241, h2248, h2250, h2260, h2263, h2272, h2274, h2277, h2728, h2748, h2764, h2773, reducedSource1961] using sourceEq2440 B hB

theorem rowSound1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1961 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1961, numericCheck1961, reducedZero1961 B hB hF, mul_zero]

theorem reducedZero1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1962 (mixedVector B) = 0 := by
  have h1824 : mixedVector B (Sum.inr 1824) = Sparse.eval nodeValue1824 (mixedVector B) := by
    change mixedMoment B node1824 node1824Labels = _
    exact sound1824 B hB hF
  have h1828 : mixedVector B (Sum.inr 1828) = Sparse.eval nodeValue1828 (mixedVector B) := by
    change mixedMoment B node1828 node1828Labels = _
    exact sound1828 B hB hF
  have h1829 : mixedVector B (Sum.inr 1829) = Sparse.eval nodeValue1829 (mixedVector B) := by
    change mixedMoment B node1829 node1829Labels = _
    exact sound1829 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2441, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1824, h1828, h1829, h2110, h3079, h4083, reducedSource1962] using sourceEq2441 B hB

theorem rowSound1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1962 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1962, numericCheck1962, reducedZero1962 B hB hF, mul_zero]

theorem reducedZero1966 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1966 (mixedVector B) = 0 := by
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h2198 : mixedVector B (Sum.inr 2198) = Sparse.eval nodeValue2198 (mixedVector B) := by
    change mixedMoment B node2198 node2198Labels = _
    exact sound2198 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2256 : mixedVector B (Sum.inr 2256) = Sparse.eval nodeValue2256 (mixedVector B) := by
    change mixedMoment B node2256 node2256Labels = _
    exact sound2256 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2760 : mixedVector B (Sum.inr 2760) = Sparse.eval nodeValue2760 (mixedVector B) := by
    change mixedMoment B node2760 node2760Labels = _
    exact sound2760 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  simpa only [sourceForm2446, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1703, h1720, h1721, h1724, h1734, h2198, h2199, h2202, h2211, h2238, h2240, h2241, h2256, h2257, h2259, h2260, h2262, h2263, h2272, h2274, h2275, h2287, h2288, h2291, h2718, h2760, h2763, h2764, h2782, reducedSource1966] using sourceEq2446 B hB

theorem rowSound1966 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1966 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1966, numericCheck1966, reducedZero1966 B hB hF, mul_zero]

theorem reducedZero1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1967 (mixedVector B) = 0 := by
  have h1822 : mixedVector B (Sum.inr 1822) = Sparse.eval nodeValue1822 (mixedVector B) := by
    change mixedMoment B node1822 node1822Labels = _
    exact sound1822 B hB hF
  have h1825 : mixedVector B (Sum.inr 1825) = Sparse.eval nodeValue1825 (mixedVector B) := by
    change mixedMoment B node1825 node1825Labels = _
    exact sound1825 B hB hF
  have h1827 : mixedVector B (Sum.inr 1827) = Sparse.eval nodeValue1827 (mixedVector B) := by
    change mixedMoment B node1827 node1827Labels = _
    exact sound1827 B hB hF
  have h1829 : mixedVector B (Sum.inr 1829) = Sparse.eval nodeValue1829 (mixedVector B) := by
    change mixedMoment B node1829 node1829Labels = _
    exact sound1829 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2447, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1822, h1825, h1827, h1829, h2107, h3096, h4083, reducedSource1967] using sourceEq2447 B hB

theorem rowSound1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1967 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1967, numericCheck1967, reducedZero1967 B hB hF, mul_zero]

theorem sourceRowsAt1952 : MixedData.sourceRows (1952 : Fin 2425) =
    MixedData.row1952 := by decide +kernel

theorem sourceRowsAt1953 : MixedData.sourceRows (1953 : Fin 2425) =
    MixedData.row1953 := by decide +kernel

theorem sourceRowsAt1954 : MixedData.sourceRows (1954 : Fin 2425) =
    MixedData.row1954 := by decide +kernel

theorem sourceRowsAt1955 : MixedData.sourceRows (1955 : Fin 2425) =
    MixedData.row1955 := by decide +kernel

theorem sourceRowsAt1956 : MixedData.sourceRows (1956 : Fin 2425) =
    MixedData.row1956 := by decide +kernel

theorem sourceRowsAt1957 : MixedData.sourceRows (1957 : Fin 2425) =
    MixedData.row1957 := by decide +kernel

theorem sourceRowsAt1958 : MixedData.sourceRows (1958 : Fin 2425) =
    MixedData.row1958 := by decide +kernel

theorem sourceRowsAt1959 : MixedData.sourceRows (1959 : Fin 2425) =
    MixedData.row1959 := by decide +kernel

theorem sourceRowsAt1960 : MixedData.sourceRows (1960 : Fin 2425) =
    MixedData.row1960 := by decide +kernel

theorem sourceRowsAt1961 : MixedData.sourceRows (1961 : Fin 2425) =
    MixedData.row1961 := by decide +kernel

theorem sourceRowsAt1962 : MixedData.sourceRows (1962 : Fin 2425) =
    MixedData.row1962 := by decide +kernel

theorem sourceRowsAt1963 : MixedData.sourceRows (1963 : Fin 2425) =
    MixedData.row1963 := by decide +kernel

theorem sourceRowsAt1964 : MixedData.sourceRows (1964 : Fin 2425) =
    MixedData.row1964 := by decide +kernel

theorem sourceRowsAt1965 : MixedData.sourceRows (1965 : Fin 2425) =
    MixedData.row1965 := by decide +kernel

theorem sourceRowsAt1966 : MixedData.sourceRows (1966 : Fin 2425) =
    MixedData.row1966 := by decide +kernel

theorem sourceRowsAt1967 : MixedData.sourceRows (1967 : Fin 2425) =
    MixedData.row1967 := by decide +kernel

theorem chunkSound122_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 122) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1952 ∨ k.val = 1953 ∨ k.val = 1954 ∨ k.val = 1955 ∨ k.val = 1956 ∨ k.val = 1957 ∨ k.val = 1958 ∨ k.val = 1959 ∨ k.val = 1960 ∨ k.val = 1961 ∨ k.val = 1962 ∨ k.val = 1963 ∨ k.val = 1964 ∨ k.val = 1965 ∨ k.val = 1966 ∨ k.val = 1967 := by omega
  rcases heq with h1952 | h1953 | h1954 | h1955 | h1956 | h1957 | h1958 | h1959 | h1960 | h1961 | h1962 | h1963 | h1964 | h1965 | h1966 | h1967
  · have he : k = (1952 : Fin 2425) := Fin.ext h1952
    subst k
    rw [sourceRowsAt1952]
    exact rowSound1952_e B hB hF
  · have he : k = (1953 : Fin 2425) := Fin.ext h1953
    subst k
    rw [sourceRowsAt1953]
    exact rowSound1953_e B hB hF
  · have he : k = (1954 : Fin 2425) := Fin.ext h1954
    subst k
    rw [sourceRowsAt1954]
    exact rowSound1954_e B hB hF
  · have he : k = (1955 : Fin 2425) := Fin.ext h1955
    subst k
    rw [sourceRowsAt1955]
    exact rowSound1955 B hB hF
  · have he : k = (1956 : Fin 2425) := Fin.ext h1956
    subst k
    rw [sourceRowsAt1956]
    exact rowSound1956_e B hB hF
  · have he : k = (1957 : Fin 2425) := Fin.ext h1957
    subst k
    rw [sourceRowsAt1957]
    exact rowSound1957 B hB hF
  · have he : k = (1958 : Fin 2425) := Fin.ext h1958
    subst k
    rw [sourceRowsAt1958]
    exact rowSound1958_e B hB hF
  · have he : k = (1959 : Fin 2425) := Fin.ext h1959
    subst k
    rw [sourceRowsAt1959]
    exact rowSound1959 B hB hF
  · have he : k = (1960 : Fin 2425) := Fin.ext h1960
    subst k
    rw [sourceRowsAt1960]
    exact rowSound1960_e B hB hF
  · have he : k = (1961 : Fin 2425) := Fin.ext h1961
    subst k
    rw [sourceRowsAt1961]
    exact rowSound1961 B hB hF
  · have he : k = (1962 : Fin 2425) := Fin.ext h1962
    subst k
    rw [sourceRowsAt1962]
    exact rowSound1962 B hB hF
  · have he : k = (1963 : Fin 2425) := Fin.ext h1963
    subst k
    rw [sourceRowsAt1963]
    exact rowSound1963_e B hB hF
  · have he : k = (1964 : Fin 2425) := Fin.ext h1964
    subst k
    rw [sourceRowsAt1964]
    exact rowSound1964_e B hB hF
  · have he : k = (1965 : Fin 2425) := Fin.ext h1965
    subst k
    rw [sourceRowsAt1965]
    exact rowSound1965_e B hB hF
  · have he : k = (1966 : Fin 2425) := Fin.ext h1966
    subst k
    rw [sourceRowsAt1966]
    exact rowSound1966 B hB hF
  · have he : k = (1967 : Fin 2425) := Fin.ext h1967
    subst k
    rw [sourceRowsAt1967]
    exact rowSound1967 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e_oai
