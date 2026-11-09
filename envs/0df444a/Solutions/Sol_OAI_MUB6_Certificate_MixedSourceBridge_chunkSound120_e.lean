-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:42:25.96407+00:00
-- url     : https://prove2.me/submissions/4337501f-6db5-441f-b9dc-d299cd27644f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1924_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1925_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1935_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13305 raw13305Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13305 raw13305Labels = mixedMoment B raw13305step0 raw13305step0Labels := by
      have hz : ∀ j, raw13305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13305step0 = (fun i j => raw13305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13305step0 raw13305; decide +kernel
      have hl : raw13305step0Labels = raw13305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13305 raw13305Labels permutation590 hz
    mixedMoment B raw13305step0 raw13305step0Labels = mixedMoment B raw13305step1 raw13305step1Labels := by
      have ha : raw13305step1 = (fun i j => raw13305step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13305step1 raw13305step0; decide +kernel
      have hl : raw13305step1Labels = raw13305step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13305step0 raw13305step0Labels permutation122 permutation0
    mixedMoment B raw13305step1 raw13305step1Labels = mixedMoment B raw13305step2 raw13305step2Labels := by
      have ha : raw13305step2 = -raw13305step1 := by apply Matrix.ext; change ∀ i j, raw13305step2 i j = -(raw13305step1 i j); unfold raw13305step2 raw13305step1; decide +kernel
      have hl : raw13305step2Labels = raw13305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13314 raw13314Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw13314 raw13314Labels = mixedMoment B raw13314step0 raw13314step0Labels := by
      have ha : raw13314step0 = (fun i j => raw13314 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13314step0 raw13314; decide +kernel
      have hl : raw13314step0Labels = raw13314Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13314 raw13314Labels permutation154 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16829 raw16829Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw16829 raw16829Labels = mixedMoment B raw16829step0 raw16829step0Labels := by
      have ha : raw16829step0 = (fun i j => raw16829 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16829step0 raw16829; decide +kernel
      have hl : raw16829step0Labels = raw16829Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16829 raw16829Labels permutation154 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

theorem canonical16832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16832 raw16832Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16832 raw16832Labels = mixedMoment B raw16832step0 raw16832step0Labels := by
      have hz : ∀ j, raw16832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16832step0 = (fun i j => raw16832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16832step0 raw16832; decide +kernel
      have hl : raw16832step0Labels = raw16832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16832 raw16832Labels permutation520 hz
    mixedMoment B raw16832step0 raw16832step0Labels = mixedMoment B raw16832step1 raw16832step1Labels := by
      have ha : raw16832step1 = (fun i j => raw16832step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16832step1 raw16832step0; decide +kernel
      have hl : raw16832step1Labels = raw16832step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16832step0 raw16832step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical16835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16835 raw16835Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw16835 raw16835Labels = mixedMoment B raw16835step0 raw16835step0Labels := by
      have ha : raw16835step0 = (fun i j => raw16835 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16835step0 raw16835; decide +kernel
      have hl : raw16835step0Labels = raw16835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16835 raw16835Labels permutation267 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17020 raw17020Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw17020 raw17020Labels = mixedMoment B raw17020step0 raw17020step0Labels := by
      have ha : raw17020step0 = (fun i j => raw17020 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17020step0 raw17020; decide +kernel
      have hl : raw17020step0Labels = raw17020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17020 raw17020Labels permutation154 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical17023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17023 raw17023Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17023 raw17023Labels = mixedMoment B raw17023step0 raw17023step0Labels := by
      have hz : ∀ j, raw17023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17023step0 = (fun i j => raw17023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17023step0 raw17023; decide +kernel
      have hl : raw17023step0Labels = raw17023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17023 raw17023Labels permutation520 hz
    mixedMoment B raw17023step0 raw17023step0Labels = mixedMoment B raw17023step1 raw17023step1Labels := by
      have ha : raw17023step1 = (fun i j => raw17023step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17023step1 raw17023step0; decide +kernel
      have hl : raw17023step1Labels = raw17023step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17023step0 raw17023step0Labels permutation122 permutation0
    mixedMoment B raw17023step1 raw17023step1Labels = mixedMoment B raw17023step2 raw17023step2Labels := by
      have ha : raw17023step2 = -raw17023step1 := by apply Matrix.ext; change ∀ i j, raw17023step2 i j = -(raw17023step1 i j); unfold raw17023step2 raw17023step1; decide +kernel
      have hl : raw17023step2Labels = raw17023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17026 raw17026Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw17026 raw17026Labels = mixedMoment B raw17026step0 raw17026step0Labels := by
      have ha : raw17026step0 = (fun i j => raw17026 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17026step0 raw17026; decide +kernel
      have hl : raw17026step0Labels = raw17026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17026 raw17026Labels permutation662 permutation2
    mixedMoment B raw17026step0 raw17026step0Labels = mixedMoment B raw17026step1 raw17026step1Labels := by
      have ha : raw17026step1 = -raw17026step0 := by apply Matrix.ext; change ∀ i j, raw17026step1 i j = -(raw17026step0 i j); unfold raw17026step1 raw17026step0; decide +kernel
      have hl : raw17026step1Labels = raw17026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23905 raw23905Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw23905 raw23905Labels = mixedMoment B raw23905step0 raw23905step0Labels := by
      have ha : raw23905step0 = (fun i j => raw23905 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23905step0 raw23905; decide +kernel
      have hl : raw23905step0Labels = raw23905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23905 raw23905Labels permutation154 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical23911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23911 raw23911Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23911 raw23911Labels = mixedMoment B raw23911step0 raw23911step0Labels := by
      have hz : ∀ j, raw23911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23911step0 = (fun i j => raw23911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23911step0 raw23911; decide +kernel
      have hl : raw23911step0Labels = raw23911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23911 raw23911Labels permutation520 hz
    mixedMoment B raw23911step0 raw23911step0Labels = mixedMoment B raw23911step1 raw23911step1Labels := by
      have ha : raw23911step1 = (fun i j => raw23911step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23911step1 raw23911step0; decide +kernel
      have hl : raw23911step1Labels = raw23911step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23911step0 raw23911step0Labels permutation146 permutation0
    mixedMoment B raw23911step1 raw23911step1Labels = mixedMoment B raw23911step2 raw23911step2Labels := by
      have ha : raw23911step2 = -raw23911step1 := by apply Matrix.ext; change ∀ i j, raw23911step2 i j = -(raw23911step1 i j); unfold raw23911step2 raw23911step1; decide +kernel
      have hl : raw23911step2Labels = raw23911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32259 raw32259Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw32259 raw32259Labels = mixedMoment B raw32259step0 raw32259step0Labels := by
      have ha : raw32259step0 = (fun i j => raw32259 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32259step0 raw32259; decide +kernel
      have hl : raw32259step0Labels = raw32259Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32259 raw32259Labels permutation154 permutation2
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical32260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32260 raw32260Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw32260 raw32260Labels = mixedMoment B raw32260step0 raw32260step0Labels := by
      have ha : raw32260step0 = (fun i j => raw32260 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32260step0 raw32260; decide +kernel
      have hl : raw32260step0Labels = raw32260Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32260 raw32260Labels permutation178 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

theorem canonical32261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32261 raw32261Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw32261 raw32261Labels = mixedMoment B raw32261step0 raw32261step0Labels := by
      have ha : raw32261step0 = (fun i j => raw32261 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32261step0 raw32261; decide +kernel
      have hl : raw32261step0Labels = raw32261Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32261 raw32261Labels permutation155 permutation2
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical32262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32262 raw32262Labels = mixedMoment B node2898 node2898Labels := by
  calc
    mixedMoment B raw32262 raw32262Labels = mixedMoment B raw32262step0 raw32262step0Labels := by
      have ha : raw32262step0 = (fun i j => raw32262 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32262step0 raw32262; decide +kernel
      have hl : raw32262step0Labels = raw32262Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32262 raw32262Labels permutation153 permutation2
    _ = mixedMoment B node2898 node2898Labels := by rfl

theorem canonical32263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32263 raw32263Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw32263 raw32263Labels = mixedMoment B raw32263step0 raw32263step0Labels := by
      have ha : raw32263step0 = (fun i j => raw32263 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32263step0 raw32263; decide +kernel
      have hl : raw32263step0Labels = raw32263Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32263 raw32263Labels permutation154 permutation2
    _ = mixedMoment B node2895 node2895Labels := by rfl

theorem canonical32264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32264 raw32264Labels = mixedMoment B node1158 node1158Labels := by
  calc
    mixedMoment B raw32264 raw32264Labels = mixedMoment B raw32264step0 raw32264step0Labels := by
      have ha : raw32264step0 = (fun i j => raw32264 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32264step0 raw32264; decide +kernel
      have hl : raw32264step0Labels = raw32264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32264 raw32264Labels permutation158 permutation2
    _ = mixedMoment B node1158 node1158Labels := by rfl

theorem canonical32265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32265 raw32265Labels = mixedMoment B node2354 node2354Labels := by
  calc
    mixedMoment B raw32265 raw32265Labels = mixedMoment B raw32265step0 raw32265step0Labels := by
      have ha : raw32265step0 = (fun i j => raw32265 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32265step0 raw32265; decide +kernel
      have hl : raw32265step0Labels = raw32265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32265 raw32265Labels permutation158 permutation2
    _ = mixedMoment B node2354 node2354Labels := by rfl

theorem canonical32266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32266 raw32266Labels = mixedMoment B node2567 node2567Labels := by
  calc
    _ = mixedMoment B node2567 node2567Labels := by rfl

theorem canonical32267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32267 raw32267Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw32267 raw32267Labels = mixedMoment B raw32267step0 raw32267step0Labels := by
      have ha : raw32267step0 = (fun i j => raw32267 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32267step0 raw32267; decide +kernel
      have hl : raw32267step0Labels = raw32267Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32267 raw32267Labels permutation158 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical32268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32268 raw32268Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw32268 raw32268Labels = mixedMoment B raw32268step0 raw32268step0Labels := by
      have ha : raw32268step0 = (fun i j => raw32268 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32268step0 raw32268; decide +kernel
      have hl : raw32268step0Labels = raw32268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32268 raw32268Labels permutation166 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

theorem canonical32269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32269 raw32269Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw32269 raw32269Labels = mixedMoment B raw32269step0 raw32269step0Labels := by
      have ha : raw32269step0 = (fun i j => raw32269 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32269step0 raw32269; decide +kernel
      have hl : raw32269step0Labels = raw32269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32269 raw32269Labels permutation158 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical32270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32270 raw32270Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw32270 raw32270Labels = mixedMoment B raw32270step0 raw32270step0Labels := by
      have hz : ∀ j, raw32270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32270step0 = (fun i j => raw32270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32270step0 raw32270; decide +kernel
      have hl : raw32270step0Labels = raw32270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32270 raw32270Labels permutation265 hz
    mixedMoment B raw32270step0 raw32270step0Labels = mixedMoment B raw32270step1 raw32270step1Labels := by
      have ha : raw32270step1 = (fun i j => raw32270step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32270step1 raw32270step0; decide +kernel
      have hl : raw32270step1Labels = raw32270step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32270step0 raw32270step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical32271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32271 raw32271Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw32271 raw32271Labels = mixedMoment B raw32271step0 raw32271step0Labels := by
      have ha : raw32271step0 = (fun i j => raw32271 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32271step0 raw32271; decide +kernel
      have hl : raw32271step0Labels = raw32271Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32271 raw32271Labels permutation178 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical32272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32272 raw32272Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw32272 raw32272Labels = mixedMoment B raw32272step0 raw32272step0Labels := by
      have ha : raw32272step0 = (fun i j => raw32272 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32272step0 raw32272; decide +kernel
      have hl : raw32272step0Labels = raw32272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32272 raw32272Labels permutation155 permutation2
    _ = mixedMoment B node2893 node2893Labels := by rfl

theorem canonical32273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32273 raw32273Labels = mixedMoment B node2898 node2898Labels := by
  calc
    _ = mixedMoment B node2898 node2898Labels := by rfl

theorem canonical32274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32274 raw32274Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw32274 raw32274Labels = mixedMoment B raw32274step0 raw32274step0Labels := by
      have ha : raw32274step0 = (fun i j => raw32274 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32274step0 raw32274; decide +kernel
      have hl : raw32274step0Labels = raw32274Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32274 raw32274Labels permutation662 permutation2
    mixedMoment B raw32274step0 raw32274step0Labels = mixedMoment B raw32274step1 raw32274step1Labels := by
      have ha : raw32274step1 = -raw32274step0 := by apply Matrix.ext; change ∀ i j, raw32274step1 i j = -(raw32274step0 i j); unfold raw32274step1 raw32274step0; decide +kernel
      have hl : raw32274step1Labels = raw32274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

theorem canonical32275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32275 raw32275Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw32275 raw32275Labels = mixedMoment B raw32275step0 raw32275step0Labels := by
      have ha : raw32275step0 = (fun i j => raw32275 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32275step0 raw32275; decide +kernel
      have hl : raw32275step0Labels = raw32275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32275 raw32275Labels permutation154 permutation2
    _ = mixedMoment B node2922 node2922Labels := by rfl

theorem canonical32276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32276 raw32276Labels = mixedMoment B node3748 node3748Labels := by
  calc
    mixedMoment B raw32276 raw32276Labels = mixedMoment B raw32276step0 raw32276step0Labels := by
      have ha : raw32276step0 = (fun i j => raw32276 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32276step0 raw32276; decide +kernel
      have hl : raw32276step0Labels = raw32276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32276 raw32276Labels permutation663 permutation2
    mixedMoment B raw32276step0 raw32276step0Labels = mixedMoment B raw32276step1 raw32276step1Labels := by
      have ha : raw32276step1 = -raw32276step0 := by apply Matrix.ext; change ∀ i j, raw32276step1 i j = -(raw32276step0 i j); unfold raw32276step1 raw32276step0; decide +kernel
      have hl : raw32276step1Labels = raw32276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3748 node3748Labels := by rfl

theorem canonical32277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32277 raw32277Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw32277 raw32277Labels = mixedMoment B raw32277step0 raw32277step0Labels := by
      have ha : raw32277step0 = (fun i j => raw32277 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32277step0 raw32277; decide +kernel
      have hl : raw32277step0Labels = raw32277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32277 raw32277Labels permutation662 permutation2
    mixedMoment B raw32277step0 raw32277step0Labels = mixedMoment B raw32277step1 raw32277step1Labels := by
      have ha : raw32277step1 = -raw32277step0 := by apply Matrix.ext; change ∀ i j, raw32277step1 i j = -(raw32277step0 i j); unfold raw32277step1 raw32277step0; decide +kernel
      have hl : raw32277step1Labels = raw32277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3751 node3751Labels := by rfl

theorem canonical32278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32278 raw32278Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw32278 raw32278Labels = mixedMoment B raw32278step0 raw32278step0Labels := by
      have ha : raw32278step0 = (fun i j => raw32278 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32278step0 raw32278; decide +kernel
      have hl : raw32278step0Labels = raw32278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32278 raw32278Labels permutation688 permutation2
    mixedMoment B raw32278step0 raw32278step0Labels = mixedMoment B raw32278step1 raw32278step1Labels := by
      have ha : raw32278step1 = -raw32278step0 := by apply Matrix.ext; change ∀ i j, raw32278step1 i j = -(raw32278step0 i j); unfold raw32278step1 raw32278step0; decide +kernel
      have hl : raw32278step1Labels = raw32278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical32279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32279 raw32279Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw32279 raw32279Labels = mixedMoment B raw32279step0 raw32279step0Labels := by
      have ha : raw32279step0 = (fun i j => raw32279 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32279step0 raw32279; decide +kernel
      have hl : raw32279step0Labels = raw32279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32279 raw32279Labels permutation658 permutation2
    mixedMoment B raw32279step0 raw32279step0Labels = mixedMoment B raw32279step1 raw32279step1Labels := by
      have ha : raw32279step1 = -raw32279step0 := by apply Matrix.ext; change ∀ i j, raw32279step1 i j = -(raw32279step0 i j); unfold raw32279step1 raw32279step0; decide +kernel
      have hl : raw32279step1Labels = raw32279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical32280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32280 raw32280Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw32280 raw32280Labels = mixedMoment B raw32280step0 raw32280step0Labels := by
      have ha : raw32280step0 = (fun i j => raw32280 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32280step0 raw32280; decide +kernel
      have hl : raw32280step0Labels = raw32280Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32280 raw32280Labels permutation154 permutation2
    _ = mixedMoment B node3973 node3973Labels := by rfl

theorem canonical32281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32281 raw32281Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw32281 raw32281Labels = mixedMoment B raw32281step0 raw32281step0Labels := by
      have ha : raw32281step0 = (fun i j => raw32281 (permutation505 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32281step0 raw32281; decide +kernel
      have hl : raw32281step0Labels = raw32281Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32281 raw32281Labels permutation505 permutation0
    mixedMoment B raw32281step0 raw32281step0Labels = mixedMoment B raw32281step1 raw32281step1Labels := by
      have ha : raw32281step1 = -raw32281step0 := by apply Matrix.ext; change ∀ i j, raw32281step1 i j = -(raw32281step0 i j); unfold raw32281step1 raw32281step0; decide +kernel
      have hl : raw32281step1Labels = raw32281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4087 node4087Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32442 raw32442Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw32442 raw32442Labels = mixedMoment B raw32442step0 raw32442step0Labels := by
      have ha : raw32442step0 = (fun i j => raw32442 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32442step0 raw32442; decide +kernel
      have hl : raw32442step0Labels = raw32442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32442 raw32442Labels permutation663 permutation7
    mixedMoment B raw32442step0 raw32442step0Labels = mixedMoment B raw32442step1 raw32442step1Labels := by
      have ha : raw32442step1 = raw32442step0 := by apply Matrix.ext; unfold raw32442step1 raw32442step0; decide +kernel
      have hl : raw32442step0Labels = labelEmbedding1 ∘ raw32442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32442step0 raw32442step0Labels raw32442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical32443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32443 raw32443Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw32443 raw32443Labels = mixedMoment B raw32443step0 raw32443step0Labels := by
      have ha : raw32443step0 = (fun i j => raw32443 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32443step0 raw32443; decide +kernel
      have hl : raw32443step0Labels = raw32443Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32443 raw32443Labels permutation662 permutation7
    mixedMoment B raw32443step0 raw32443step0Labels = mixedMoment B raw32443step1 raw32443step1Labels := by
      have ha : raw32443step1 = raw32443step0 := by apply Matrix.ext; unfold raw32443step1 raw32443step0; decide +kernel
      have hl : raw32443step0Labels = labelEmbedding1 ∘ raw32443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32443step0 raw32443step0Labels raw32443step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

theorem canonical32444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32444 raw32444Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32444 raw32444Labels = mixedMoment B raw32444step0 raw32444step0Labels := by
      have ha : raw32444step0 = (fun i j => raw32444 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32444step0 raw32444; decide +kernel
      have hl : raw32444step0Labels = raw32444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32444 raw32444Labels permutation664 permutation7
    mixedMoment B raw32444step0 raw32444step0Labels = mixedMoment B raw32444step1 raw32444step1Labels := by
      have ha : raw32444step1 = raw32444step0 := by apply Matrix.ext; unfold raw32444step1 raw32444step0; decide +kernel
      have hl : raw32444step0Labels = labelEmbedding1 ∘ raw32444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32444step0 raw32444step0Labels raw32444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical32445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32445 raw32445Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32445 raw32445Labels = mixedMoment B raw32445step0 raw32445step0Labels := by
      have hz : ∀ j, raw32445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32445step0 = (fun i j => raw32445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32445step0 raw32445; decide +kernel
      have hl : raw32445step0Labels = raw32445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32445 raw32445Labels permutation520 hz
    mixedMoment B raw32445step0 raw32445step0Labels = mixedMoment B raw32445step1 raw32445step1Labels := by
      have ha : raw32445step1 = (fun i j => raw32445step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32445step1 raw32445step0; decide +kernel
      have hl : raw32445step1Labels = raw32445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32445step0 raw32445step0Labels permutation151 permutation7
    mixedMoment B raw32445step1 raw32445step1Labels = mixedMoment B raw32445step2 raw32445step2Labels := by
      have ha : raw32445step2 = raw32445step1 := by apply Matrix.ext; unfold raw32445step2 raw32445step1; decide +kernel
      have hl : raw32445step1Labels = labelEmbedding1 ∘ raw32445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32445step1 raw32445step1Labels raw32445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical32446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32446 raw32446Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw32446 raw32446Labels = mixedMoment B raw32446step0 raw32446step0Labels := by
      have ha : raw32446step0 = (fun i j => raw32446 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32446step0 raw32446; decide +kernel
      have hl : raw32446step0Labels = raw32446Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32446 raw32446Labels permutation664 permutation7
    mixedMoment B raw32446step0 raw32446step0Labels = mixedMoment B raw32446step1 raw32446step1Labels := by
      have ha : raw32446step1 = raw32446step0 := by apply Matrix.ext; unfold raw32446step1 raw32446step0; decide +kernel
      have hl : raw32446step0Labels = labelEmbedding1 ∘ raw32446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32446step0 raw32446step0Labels raw32446step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical32447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32447 raw32447Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw32447 raw32447Labels = mixedMoment B raw32447step0 raw32447step0Labels := by
      have ha : raw32447step0 = (fun i j => raw32447 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32447step0 raw32447; decide +kernel
      have hl : raw32447step0Labels = raw32447Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32447 raw32447Labels permutation218 permutation5
    mixedMoment B raw32447step0 raw32447step0Labels = mixedMoment B raw32447step1 raw32447step1Labels := by
      have ha : raw32447step1 = -raw32447step0 := by apply Matrix.ext; change ∀ i j, raw32447step1 i j = -(raw32447step0 i j); unfold raw32447step1 raw32447step0; decide +kernel
      have hl : raw32447step1Labels = raw32447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32447step1 raw32447step1Labels = mixedMoment B raw32447step2 raw32447step2Labels := by
      have ha : raw32447step2 = raw32447step1 := by apply Matrix.ext; unfold raw32447step2 raw32447step1; decide +kernel
      have hl : raw32447step1Labels = labelEmbedding1 ∘ raw32447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32447step1 raw32447step1Labels raw32447step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical32448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32448 raw32448Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw32448 raw32448Labels = mixedMoment B raw32448step0 raw32448step0Labels := by
      have ha : raw32448step0 = (fun i j => raw32448 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32448step0 raw32448; decide +kernel
      have hl : raw32448step0Labels = raw32448Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32448 raw32448Labels permutation186 permutation5
    mixedMoment B raw32448step0 raw32448step0Labels = mixedMoment B raw32448step1 raw32448step1Labels := by
      have ha : raw32448step1 = -raw32448step0 := by apply Matrix.ext; change ∀ i j, raw32448step1 i j = -(raw32448step0 i j); unfold raw32448step1 raw32448step0; decide +kernel
      have hl : raw32448step1Labels = raw32448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32448step1 raw32448step1Labels = mixedMoment B raw32448step2 raw32448step2Labels := by
      have ha : raw32448step2 = raw32448step1 := by apply Matrix.ext; unfold raw32448step2 raw32448step1; decide +kernel
      have hl : raw32448step1Labels = labelEmbedding1 ∘ raw32448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32448step1 raw32448step1Labels raw32448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical32449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32449 raw32449Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw32449 raw32449Labels = mixedMoment B raw32449step0 raw32449step0Labels := by
      have ha : raw32449step0 = (fun i j => raw32449 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32449step0 raw32449; decide +kernel
      have hl : raw32449step0Labels = raw32449Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32449 raw32449Labels permutation218 permutation5
    mixedMoment B raw32449step0 raw32449step0Labels = mixedMoment B raw32449step1 raw32449step1Labels := by
      have ha : raw32449step1 = -raw32449step0 := by apply Matrix.ext; change ∀ i j, raw32449step1 i j = -(raw32449step0 i j); unfold raw32449step1 raw32449step0; decide +kernel
      have hl : raw32449step1Labels = raw32449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32449step1 raw32449step1Labels = mixedMoment B raw32449step2 raw32449step2Labels := by
      have ha : raw32449step2 = raw32449step1 := by apply Matrix.ext; unfold raw32449step2 raw32449step1; decide +kernel
      have hl : raw32449step1Labels = labelEmbedding1 ∘ raw32449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32449step1 raw32449step1Labels raw32449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical32450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32450 raw32450Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw32450 raw32450Labels = mixedMoment B raw32450step0 raw32450step0Labels := by
      have hz : ∀ j, raw32450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32450step0 = (fun i j => raw32450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32450step0 raw32450; decide +kernel
      have hl : raw32450step0Labels = raw32450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32450 raw32450Labels permutation520 hz
    mixedMoment B raw32450step0 raw32450step0Labels = mixedMoment B raw32450step1 raw32450step1Labels := by
      have ha : raw32450step1 = (fun i j => raw32450step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32450step1 raw32450step0; decide +kernel
      have hl : raw32450step1Labels = raw32450step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32450step0 raw32450step0Labels permutation48 permutation5
    mixedMoment B raw32450step1 raw32450step1Labels = mixedMoment B raw32450step2 raw32450step2Labels := by
      have ha : raw32450step2 = -raw32450step1 := by apply Matrix.ext; change ∀ i j, raw32450step2 i j = -(raw32450step1 i j); unfold raw32450step2 raw32450step1; decide +kernel
      have hl : raw32450step2Labels = raw32450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32450step2 raw32450step2Labels = mixedMoment B raw32450step3 raw32450step3Labels := by
      have ha : raw32450step3 = raw32450step2 := by apply Matrix.ext; unfold raw32450step3 raw32450step2; decide +kernel
      have hl : raw32450step2Labels = labelEmbedding1 ∘ raw32450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32450step2 raw32450step2Labels raw32450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical32451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32451 raw32451Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw32451 raw32451Labels = mixedMoment B raw32451step0 raw32451step0Labels := by
      have ha : raw32451step0 = (fun i j => raw32451 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32451step0 raw32451; decide +kernel
      have hl : raw32451step0Labels = raw32451Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32451 raw32451Labels permutation257 permutation5
    mixedMoment B raw32451step0 raw32451step0Labels = mixedMoment B raw32451step1 raw32451step1Labels := by
      have ha : raw32451step1 = -raw32451step0 := by apply Matrix.ext; change ∀ i j, raw32451step1 i j = -(raw32451step0 i j); unfold raw32451step1 raw32451step0; decide +kernel
      have hl : raw32451step1Labels = raw32451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32451step1 raw32451step1Labels = mixedMoment B raw32451step2 raw32451step2Labels := by
      have ha : raw32451step2 = raw32451step1 := by apply Matrix.ext; unfold raw32451step2 raw32451step1; decide +kernel
      have hl : raw32451step1Labels = labelEmbedding1 ∘ raw32451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32451step1 raw32451step1Labels raw32451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical32452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32452 raw32452Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw32452 raw32452Labels = mixedMoment B raw32452step0 raw32452step0Labels := by
      have ha : raw32452step0 = (fun i j => raw32452 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32452step0 raw32452; decide +kernel
      have hl : raw32452step0Labels = raw32452Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32452 raw32452Labels permutation163 permutation5
    mixedMoment B raw32452step0 raw32452step0Labels = mixedMoment B raw32452step1 raw32452step1Labels := by
      have ha : raw32452step1 = -raw32452step0 := by apply Matrix.ext; change ∀ i j, raw32452step1 i j = -(raw32452step0 i j); unfold raw32452step1 raw32452step0; decide +kernel
      have hl : raw32452step1Labels = raw32452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32452step1 raw32452step1Labels = mixedMoment B raw32452step2 raw32452step2Labels := by
      have ha : raw32452step2 = raw32452step1 := by apply Matrix.ext; unfold raw32452step2 raw32452step1; decide +kernel
      have hl : raw32452step1Labels = labelEmbedding1 ∘ raw32452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32452step1 raw32452step1Labels raw32452step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical32453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32453 raw32453Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32453 raw32453Labels = mixedMoment B raw32453step0 raw32453step0Labels := by
      have ha : raw32453step0 = (fun i j => raw32453 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32453step0 raw32453; decide +kernel
      have hl : raw32453step0Labels = raw32453Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32453 raw32453Labels permutation163 permutation5
    mixedMoment B raw32453step0 raw32453step0Labels = mixedMoment B raw32453step1 raw32453step1Labels := by
      have ha : raw32453step1 = -raw32453step0 := by apply Matrix.ext; change ∀ i j, raw32453step1 i j = -(raw32453step0 i j); unfold raw32453step1 raw32453step0; decide +kernel
      have hl : raw32453step1Labels = raw32453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32453step1 raw32453step1Labels = mixedMoment B raw32453step2 raw32453step2Labels := by
      have ha : raw32453step2 = raw32453step1 := by apply Matrix.ext; unfold raw32453step2 raw32453step1; decide +kernel
      have hl : raw32453step1Labels = labelEmbedding1 ∘ raw32453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32453step1 raw32453step1Labels raw32453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical32454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32454 raw32454Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32454 raw32454Labels = mixedMoment B raw32454step0 raw32454step0Labels := by
      have ha : raw32454step0 = (fun i j => raw32454 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32454step0 raw32454; decide +kernel
      have hl : raw32454step0Labels = raw32454Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32454 raw32454Labels permutation205 permutation5
    mixedMoment B raw32454step0 raw32454step0Labels = mixedMoment B raw32454step1 raw32454step1Labels := by
      have ha : raw32454step1 = -raw32454step0 := by apply Matrix.ext; change ∀ i j, raw32454step1 i j = -(raw32454step0 i j); unfold raw32454step1 raw32454step0; decide +kernel
      have hl : raw32454step1Labels = raw32454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32454step1 raw32454step1Labels = mixedMoment B raw32454step2 raw32454step2Labels := by
      have ha : raw32454step2 = raw32454step1 := by apply Matrix.ext; unfold raw32454step2 raw32454step1; decide +kernel
      have hl : raw32454step1Labels = labelEmbedding1 ∘ raw32454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32454step1 raw32454step1Labels raw32454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical32455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32455 raw32455Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw32455 raw32455Labels = mixedMoment B raw32455step0 raw32455step0Labels := by
      have hz : ∀ j, raw32455 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32455step0 = (fun i j => raw32455 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32455step0 raw32455; decide +kernel
      have hl : raw32455step0Labels = raw32455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32455 raw32455Labels permutation520 hz
    mixedMoment B raw32455step0 raw32455step0Labels = mixedMoment B raw32455step1 raw32455step1Labels := by
      have ha : raw32455step1 = (fun i j => raw32455step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32455step1 raw32455step0; decide +kernel
      have hl : raw32455step1Labels = raw32455step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32455step0 raw32455step0Labels permutation35 permutation5
    mixedMoment B raw32455step1 raw32455step1Labels = mixedMoment B raw32455step2 raw32455step2Labels := by
      have ha : raw32455step2 = -raw32455step1 := by apply Matrix.ext; change ∀ i j, raw32455step2 i j = -(raw32455step1 i j); unfold raw32455step2 raw32455step1; decide +kernel
      have hl : raw32455step2Labels = raw32455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32455step2 raw32455step2Labels = mixedMoment B raw32455step3 raw32455step3Labels := by
      have ha : raw32455step3 = raw32455step2 := by apply Matrix.ext; unfold raw32455step3 raw32455step2; decide +kernel
      have hl : raw32455step2Labels = labelEmbedding1 ∘ raw32455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32455step2 raw32455step2Labels raw32455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical32456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32456 raw32456Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32456 raw32456Labels = mixedMoment B raw32456step0 raw32456step0Labels := by
      have ha : raw32456step0 = (fun i j => raw32456 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32456step0 raw32456; decide +kernel
      have hl : raw32456step0Labels = raw32456Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32456 raw32456Labels permutation249 permutation5
    mixedMoment B raw32456step0 raw32456step0Labels = mixedMoment B raw32456step1 raw32456step1Labels := by
      have ha : raw32456step1 = -raw32456step0 := by apply Matrix.ext; change ∀ i j, raw32456step1 i j = -(raw32456step0 i j); unfold raw32456step1 raw32456step0; decide +kernel
      have hl : raw32456step1Labels = raw32456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32456step1 raw32456step1Labels = mixedMoment B raw32456step2 raw32456step2Labels := by
      have ha : raw32456step2 = raw32456step1 := by apply Matrix.ext; unfold raw32456step2 raw32456step1; decide +kernel
      have hl : raw32456step1Labels = labelEmbedding1 ∘ raw32456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32456step1 raw32456step1Labels raw32456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical32457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32457 raw32457Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw32457 raw32457Labels = mixedMoment B raw32457step0 raw32457step0Labels := by
      have ha : raw32457step0 = (fun i j => raw32457 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32457step0 raw32457; decide +kernel
      have hl : raw32457step0Labels = raw32457Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32457 raw32457Labels permutation171 permutation5
    mixedMoment B raw32457step0 raw32457step0Labels = mixedMoment B raw32457step1 raw32457step1Labels := by
      have ha : raw32457step1 = -raw32457step0 := by apply Matrix.ext; change ∀ i j, raw32457step1 i j = -(raw32457step0 i j); unfold raw32457step1 raw32457step0; decide +kernel
      have hl : raw32457step1Labels = raw32457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32457step1 raw32457step1Labels = mixedMoment B raw32457step2 raw32457step2Labels := by
      have ha : raw32457step2 = raw32457step1 := by apply Matrix.ext; unfold raw32457step2 raw32457step1; decide +kernel
      have hl : raw32457step1Labels = labelEmbedding1 ∘ raw32457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32457step1 raw32457step1Labels raw32457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical32458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32458 raw32458Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw32458 raw32458Labels = mixedMoment B raw32458step0 raw32458step0Labels := by
      have ha : raw32458step0 = (fun i j => raw32458 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32458step0 raw32458; decide +kernel
      have hl : raw32458step0Labels = raw32458Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32458 raw32458Labels permutation171 permutation5
    mixedMoment B raw32458step0 raw32458step0Labels = mixedMoment B raw32458step1 raw32458step1Labels := by
      have ha : raw32458step1 = -raw32458step0 := by apply Matrix.ext; change ∀ i j, raw32458step1 i j = -(raw32458step0 i j); unfold raw32458step1 raw32458step0; decide +kernel
      have hl : raw32458step1Labels = raw32458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32458step1 raw32458step1Labels = mixedMoment B raw32458step2 raw32458step2Labels := by
      have ha : raw32458step2 = raw32458step1 := by apply Matrix.ext; unfold raw32458step2 raw32458step1; decide +kernel
      have hl : raw32458step1Labels = labelEmbedding1 ∘ raw32458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32458step1 raw32458step1Labels raw32458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical32459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32459 raw32459Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw32459 raw32459Labels = mixedMoment B raw32459step0 raw32459step0Labels := by
      have ha : raw32459step0 = (fun i j => raw32459 (permutation157 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32459step0 raw32459; decide +kernel
      have hl : raw32459step0Labels = raw32459Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32459 raw32459Labels permutation157 permutation5
    mixedMoment B raw32459step0 raw32459step0Labels = mixedMoment B raw32459step1 raw32459step1Labels := by
      have ha : raw32459step1 = -raw32459step0 := by apply Matrix.ext; change ∀ i j, raw32459step1 i j = -(raw32459step0 i j); unfold raw32459step1 raw32459step0; decide +kernel
      have hl : raw32459step1Labels = raw32459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32459step1 raw32459step1Labels = mixedMoment B raw32459step2 raw32459step2Labels := by
      have ha : raw32459step2 = raw32459step1 := by apply Matrix.ext; unfold raw32459step2 raw32459step1; decide +kernel
      have hl : raw32459step1Labels = labelEmbedding1 ∘ raw32459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32459step1 raw32459step1Labels raw32459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

theorem canonical32460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32460 raw32460Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw32460 raw32460Labels = mixedMoment B raw32460step0 raw32460step0Labels := by
      have hz : ∀ j, raw32460 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32460step0 = (fun i j => raw32460 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32460step0 raw32460; decide +kernel
      have hl : raw32460step0Labels = raw32460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32460 raw32460Labels permutation520 hz
    mixedMoment B raw32460step0 raw32460step0Labels = mixedMoment B raw32460step1 raw32460step1Labels := by
      have ha : raw32460step1 = (fun i j => raw32460step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32460step1 raw32460step0; decide +kernel
      have hl : raw32460step1Labels = raw32460step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32460step0 raw32460step0Labels permutation36 permutation5
    mixedMoment B raw32460step1 raw32460step1Labels = mixedMoment B raw32460step2 raw32460step2Labels := by
      have ha : raw32460step2 = -raw32460step1 := by apply Matrix.ext; change ∀ i j, raw32460step2 i j = -(raw32460step1 i j); unfold raw32460step2 raw32460step1; decide +kernel
      have hl : raw32460step2Labels = raw32460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32460step2 raw32460step2Labels = mixedMoment B raw32460step3 raw32460step3Labels := by
      have ha : raw32460step3 = raw32460step2 := by apply Matrix.ext; unfold raw32460step3 raw32460step2; decide +kernel
      have hl : raw32460step2Labels = labelEmbedding1 ∘ raw32460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32460step2 raw32460step2Labels raw32460step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical32461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32461 raw32461Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32461 raw32461Labels = mixedMoment B raw32461step0 raw32461step0Labels := by
      have ha : raw32461step0 = (fun i j => raw32461 (permutation247 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32461step0 raw32461; decide +kernel
      have hl : raw32461step0Labels = raw32461Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32461 raw32461Labels permutation247 permutation5
    mixedMoment B raw32461step0 raw32461step0Labels = mixedMoment B raw32461step1 raw32461step1Labels := by
      have ha : raw32461step1 = -raw32461step0 := by apply Matrix.ext; change ∀ i j, raw32461step1 i j = -(raw32461step0 i j); unfold raw32461step1 raw32461step0; decide +kernel
      have hl : raw32461step1Labels = raw32461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32461step1 raw32461step1Labels = mixedMoment B raw32461step2 raw32461step2Labels := by
      have ha : raw32461step2 = raw32461step1 := by apply Matrix.ext; unfold raw32461step2 raw32461step1; decide +kernel
      have hl : raw32461step1Labels = labelEmbedding1 ∘ raw32461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32461step1 raw32461step1Labels raw32461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical32462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32462 raw32462Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw32462 raw32462Labels = mixedMoment B raw32462step0 raw32462step0Labels := by
      have ha : raw32462step0 = (fun i j => raw32462 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32462step0 raw32462; decide +kernel
      have hl : raw32462step0Labels = raw32462Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32462 raw32462Labels permutation162 permutation5
    mixedMoment B raw32462step0 raw32462step0Labels = mixedMoment B raw32462step1 raw32462step1Labels := by
      have ha : raw32462step1 = -raw32462step0 := by apply Matrix.ext; change ∀ i j, raw32462step1 i j = -(raw32462step0 i j); unfold raw32462step1 raw32462step0; decide +kernel
      have hl : raw32462step1Labels = raw32462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32462step1 raw32462step1Labels = mixedMoment B raw32462step2 raw32462step2Labels := by
      have ha : raw32462step2 = raw32462step1 := by apply Matrix.ext; unfold raw32462step2 raw32462step1; decide +kernel
      have hl : raw32462step1Labels = labelEmbedding1 ∘ raw32462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32462step1 raw32462step1Labels raw32462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical32463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32463 raw32463Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw32463 raw32463Labels = mixedMoment B raw32463step0 raw32463step0Labels := by
      have ha : raw32463step0 = (fun i j => raw32463 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32463step0 raw32463; decide +kernel
      have hl : raw32463step0Labels = raw32463Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32463 raw32463Labels permutation162 permutation5
    mixedMoment B raw32463step0 raw32463step0Labels = mixedMoment B raw32463step1 raw32463step1Labels := by
      have ha : raw32463step1 = -raw32463step0 := by apply Matrix.ext; change ∀ i j, raw32463step1 i j = -(raw32463step0 i j); unfold raw32463step1 raw32463step0; decide +kernel
      have hl : raw32463step1Labels = raw32463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32463step1 raw32463step1Labels = mixedMoment B raw32463step2 raw32463step2Labels := by
      have ha : raw32463step2 = raw32463step1 := by apply Matrix.ext; unfold raw32463step2 raw32463step1; decide +kernel
      have hl : raw32463step1Labels = labelEmbedding1 ∘ raw32463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32463step1 raw32463step1Labels raw32463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical32464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32464 raw32464Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw32464 raw32464Labels = mixedMoment B raw32464step0 raw32464step0Labels := by
      have ha : raw32464step0 = (fun i j => raw32464 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32464step0 raw32464; decide +kernel
      have hl : raw32464step0Labels = raw32464Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32464 raw32464Labels permutation153 permutation5
    mixedMoment B raw32464step0 raw32464step0Labels = mixedMoment B raw32464step1 raw32464step1Labels := by
      have ha : raw32464step1 = -raw32464step0 := by apply Matrix.ext; change ∀ i j, raw32464step1 i j = -(raw32464step0 i j); unfold raw32464step1 raw32464step0; decide +kernel
      have hl : raw32464step1Labels = raw32464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32464step1 raw32464step1Labels = mixedMoment B raw32464step2 raw32464step2Labels := by
      have ha : raw32464step2 = raw32464step1 := by apply Matrix.ext; unfold raw32464step2 raw32464step1; decide +kernel
      have hl : raw32464step1Labels = labelEmbedding1 ∘ raw32464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32464step1 raw32464step1Labels raw32464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

theorem canonical32465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32465 raw32465Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw32465 raw32465Labels = mixedMoment B raw32465step0 raw32465step0Labels := by
      have ha : raw32465step0 = (fun i j => raw32465 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32465step0 raw32465; decide +kernel
      have hl : raw32465step0Labels = raw32465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32465 raw32465Labels permutation204 permutation5
    mixedMoment B raw32465step0 raw32465step0Labels = mixedMoment B raw32465step1 raw32465step1Labels := by
      have ha : raw32465step1 = -raw32465step0 := by apply Matrix.ext; change ∀ i j, raw32465step1 i j = -(raw32465step0 i j); unfold raw32465step1 raw32465step0; decide +kernel
      have hl : raw32465step1Labels = raw32465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32465step1 raw32465step1Labels = mixedMoment B raw32465step2 raw32465step2Labels := by
      have ha : raw32465step2 = raw32465step1 := by apply Matrix.ext; unfold raw32465step2 raw32465step1; decide +kernel
      have hl : raw32465step1Labels = labelEmbedding1 ∘ raw32465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32465step1 raw32465step1Labels raw32465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical32466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32466 raw32466Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32466 raw32466Labels = mixedMoment B raw32466step0 raw32466step0Labels := by
      have ha : raw32466step0 = (fun i j => raw32466 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32466step0 raw32466; decide +kernel
      have hl : raw32466step0Labels = raw32466Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32466 raw32466Labels permutation248 permutation5
    mixedMoment B raw32466step0 raw32466step0Labels = mixedMoment B raw32466step1 raw32466step1Labels := by
      have ha : raw32466step1 = -raw32466step0 := by apply Matrix.ext; change ∀ i j, raw32466step1 i j = -(raw32466step0 i j); unfold raw32466step1 raw32466step0; decide +kernel
      have hl : raw32466step1Labels = raw32466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32466step1 raw32466step1Labels = mixedMoment B raw32466step2 raw32466step2Labels := by
      have ha : raw32466step2 = raw32466step1 := by apply Matrix.ext; unfold raw32466step2 raw32466step1; decide +kernel
      have hl : raw32466step1Labels = labelEmbedding1 ∘ raw32466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32466step1 raw32466step1Labels raw32466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical32467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32467 raw32467Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw32467 raw32467Labels = mixedMoment B raw32467step0 raw32467step0Labels := by
      have ha : raw32467step0 = (fun i j => raw32467 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32467step0 raw32467; decide +kernel
      have hl : raw32467step0Labels = raw32467Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32467 raw32467Labels permutation158 permutation5
    mixedMoment B raw32467step0 raw32467step0Labels = mixedMoment B raw32467step1 raw32467step1Labels := by
      have ha : raw32467step1 = -raw32467step0 := by apply Matrix.ext; change ∀ i j, raw32467step1 i j = -(raw32467step0 i j); unfold raw32467step1 raw32467step0; decide +kernel
      have hl : raw32467step1Labels = raw32467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32467step1 raw32467step1Labels = mixedMoment B raw32467step2 raw32467step2Labels := by
      have ha : raw32467step2 = raw32467step1 := by apply Matrix.ext; unfold raw32467step2 raw32467step1; decide +kernel
      have hl : raw32467step1Labels = labelEmbedding1 ∘ raw32467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32467step1 raw32467step1Labels raw32467step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical32468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32468 raw32468Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw32468 raw32468Labels = mixedMoment B raw32468step0 raw32468step0Labels := by
      have ha : raw32468step0 = (fun i j => raw32468 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32468step0 raw32468; decide +kernel
      have hl : raw32468step0Labels = raw32468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32468 raw32468Labels permutation158 permutation5
    mixedMoment B raw32468step0 raw32468step0Labels = mixedMoment B raw32468step1 raw32468step1Labels := by
      have ha : raw32468step1 = -raw32468step0 := by apply Matrix.ext; change ∀ i j, raw32468step1 i j = -(raw32468step0 i j); unfold raw32468step1 raw32468step0; decide +kernel
      have hl : raw32468step1Labels = raw32468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32468step1 raw32468step1Labels = mixedMoment B raw32468step2 raw32468step2Labels := by
      have ha : raw32468step2 = raw32468step1 := by apply Matrix.ext; unfold raw32468step2 raw32468step1; decide +kernel
      have hl : raw32468step1Labels = labelEmbedding1 ∘ raw32468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32468step1 raw32468step1Labels raw32468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical32469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32469 raw32469Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw32469 raw32469Labels = mixedMoment B raw32469step0 raw32469step0Labels := by
      have ha : raw32469step0 = (fun i j => raw32469 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32469step0 raw32469; decide +kernel
      have hl : raw32469step0Labels = raw32469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32469 raw32469Labels permutation662 permutation7
    mixedMoment B raw32469step0 raw32469step0Labels = mixedMoment B raw32469step1 raw32469step1Labels := by
      have ha : raw32469step1 = raw32469step0 := by apply Matrix.ext; unfold raw32469step1 raw32469step0; decide +kernel
      have hl : raw32469step0Labels = labelEmbedding1 ∘ raw32469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32469step0 raw32469step0Labels raw32469step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical32470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32470 raw32470Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32470 raw32470Labels = mixedMoment B raw32470step0 raw32470step0Labels := by
      have ha : raw32470step0 = (fun i j => raw32470 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32470step0 raw32470; decide +kernel
      have hl : raw32470step0Labels = raw32470Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32470 raw32470Labels permutation200 permutation5
    mixedMoment B raw32470step0 raw32470step0Labels = mixedMoment B raw32470step1 raw32470step1Labels := by
      have ha : raw32470step1 = -raw32470step0 := by apply Matrix.ext; change ∀ i j, raw32470step1 i j = -(raw32470step0 i j); unfold raw32470step1 raw32470step0; decide +kernel
      have hl : raw32470step1Labels = raw32470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32470step1 raw32470step1Labels = mixedMoment B raw32470step2 raw32470step2Labels := by
      have ha : raw32470step2 = raw32470step1 := by apply Matrix.ext; unfold raw32470step2 raw32470step1; decide +kernel
      have hl : raw32470step1Labels = labelEmbedding1 ∘ raw32470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32470step1 raw32470step1Labels raw32470step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical32471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32471 raw32471Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw32471 raw32471Labels = mixedMoment B raw32471step0 raw32471step0Labels := by
      have hz : ∀ j, raw32471 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32471step0 = (fun i j => raw32471 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32471step0 raw32471; decide +kernel
      have hl : raw32471step0Labels = raw32471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32471 raw32471Labels permutation520 hz
    mixedMoment B raw32471step0 raw32471step0Labels = mixedMoment B raw32471step1 raw32471step1Labels := by
      have ha : raw32471step1 = (fun i j => raw32471step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32471step1 raw32471step0; decide +kernel
      have hl : raw32471step1Labels = raw32471step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32471step0 raw32471step0Labels permutation151 permutation7
    mixedMoment B raw32471step1 raw32471step1Labels = mixedMoment B raw32471step2 raw32471step2Labels := by
      have ha : raw32471step2 = raw32471step1 := by apply Matrix.ext; unfold raw32471step2 raw32471step1; decide +kernel
      have hl : raw32471step1Labels = labelEmbedding1 ∘ raw32471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32471step1 raw32471step1Labels raw32471step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical32472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32472 raw32472Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw32472 raw32472Labels = mixedMoment B raw32472step0 raw32472step0Labels := by
      have ha : raw32472step0 = (fun i j => raw32472 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32472step0 raw32472; decide +kernel
      have hl : raw32472step0Labels = raw32472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32472 raw32472Labels permutation663 permutation2
    mixedMoment B raw32472step0 raw32472step0Labels = mixedMoment B raw32472step1 raw32472step1Labels := by
      have ha : raw32472step1 = -raw32472step0 := by apply Matrix.ext; change ∀ i j, raw32472step1 i j = -(raw32472step0 i j); unfold raw32472step1 raw32472step0; decide +kernel
      have hl : raw32472step1Labels = raw32472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical32473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32473 raw32473Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw32473 raw32473Labels = mixedMoment B raw32473step0 raw32473step0Labels := by
      have ha : raw32473step0 = (fun i j => raw32473 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32473step0 raw32473; decide +kernel
      have hl : raw32473step0Labels = raw32473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32473 raw32473Labels permutation154 permutation2
    _ = mixedMoment B node2826 node2826Labels := by rfl

theorem canonical32474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32474 raw32474Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw32474 raw32474Labels = mixedMoment B raw32474step0 raw32474step0Labels := by
      have ha : raw32474step0 = (fun i j => raw32474 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32474step0 raw32474; decide +kernel
      have hl : raw32474step0Labels = raw32474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32474 raw32474Labels permutation154 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

theorem canonical32475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32475 raw32475Labels = mixedMoment B node2824 node2824Labels := by
  calc
    _ = mixedMoment B node2824 node2824Labels := by rfl

theorem canonical32476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32476 raw32476Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw32476 raw32476Labels = mixedMoment B raw32476step0 raw32476step0Labels := by
      have ha : raw32476step0 = (fun i j => raw32476 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32476step0 raw32476; decide +kernel
      have hl : raw32476step0Labels = raw32476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32476 raw32476Labels permutation664 permutation2
    mixedMoment B raw32476step0 raw32476step0Labels = mixedMoment B raw32476step1 raw32476step1Labels := by
      have ha : raw32476step1 = -raw32476step0 := by apply Matrix.ext; change ∀ i j, raw32476step1 i j = -(raw32476step0 i j); unfold raw32476step1 raw32476step0; decide +kernel
      have hl : raw32476step1Labels = raw32476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2422 node2422Labels := by rfl

theorem canonical32493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32493 raw32493Labels = mixedMoment B node1169 node1169Labels := by
  calc
    _ = mixedMoment B node1169 node1169Labels := by rfl

theorem canonical32494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32494 raw32494Labels = mixedMoment B node2361 node2361Labels := by
  calc
    _ = mixedMoment B node2361 node2361Labels := by rfl

theorem canonical32495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32495 raw32495Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw32495 raw32495Labels = mixedMoment B raw32495step0 raw32495step0Labels := by
      have ha : raw32495step0 = (fun i j => raw32495 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32495step0 raw32495; decide +kernel
      have hl : raw32495step0Labels = raw32495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32495 raw32495Labels permutation164 permutation2
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical32496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32496 raw32496Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw32496 raw32496Labels = mixedMoment B raw32496step0 raw32496step0Labels := by
      have ha : raw32496step0 = (fun i j => raw32496 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32496step0 raw32496; decide +kernel
      have hl : raw32496step0Labels = raw32496Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32496 raw32496Labels permutation170 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical32497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32497 raw32497Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw32497 raw32497Labels = mixedMoment B raw32497step0 raw32497step0Labels := by
      have ha : raw32497step0 = (fun i j => raw32497 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32497step0 raw32497; decide +kernel
      have hl : raw32497step0Labels = raw32497Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32497 raw32497Labels permutation662 permutation2
    mixedMoment B raw32497step0 raw32497step0Labels = mixedMoment B raw32497step1 raw32497step1Labels := by
      have ha : raw32497step1 = -raw32497step0 := by apply Matrix.ext; change ∀ i j, raw32497step1 i j = -(raw32497step0 i j); unfold raw32497step1 raw32497step0; decide +kernel
      have hl : raw32497step1Labels = raw32497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

theorem canonical32498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32498 raw32498Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw32498 raw32498Labels = mixedMoment B raw32498step0 raw32498step0Labels := by
      have ha : raw32498step0 = (fun i j => raw32498 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32498step0 raw32498; decide +kernel
      have hl : raw32498step0Labels = raw32498Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32498 raw32498Labels permutation176 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical32499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32499 raw32499Labels = mixedMoment B node2923 node2923Labels := by
  calc
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical32500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32500 raw32500Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw32500 raw32500Labels = mixedMoment B raw32500step0 raw32500step0Labels := by
      have ha : raw32500step0 = (fun i j => raw32500 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32500step0 raw32500; decide +kernel
      have hl : raw32500step0Labels = raw32500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32500 raw32500Labels permutation154 permutation2
    _ = mixedMoment B node2892 node2892Labels := by rfl

theorem canonical32501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32501 raw32501Labels = mixedMoment B node2892 node2892Labels := by
  calc
    _ = mixedMoment B node2892 node2892Labels := by rfl

theorem canonical32502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32502 raw32502Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw32502 raw32502Labels = mixedMoment B raw32502step0 raw32502step0Labels := by
      have ha : raw32502step0 = (fun i j => raw32502 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32502step0 raw32502; decide +kernel
      have hl : raw32502step0Labels = raw32502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32502 raw32502Labels permutation662 permutation2
    mixedMoment B raw32502step0 raw32502step0Labels = mixedMoment B raw32502step1 raw32502step1Labels := by
      have ha : raw32502step1 = -raw32502step0 := by apply Matrix.ext; change ∀ i j, raw32502step1 i j = -(raw32502step0 i j); unfold raw32502step1 raw32502step0; decide +kernel
      have hl : raw32502step1Labels = raw32502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical32503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32503 raw32503Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw32503 raw32503Labels = mixedMoment B raw32503step0 raw32503step0Labels := by
      have hz : ∀ j, raw32503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32503step0 = (fun i j => raw32503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32503step0 raw32503; decide +kernel
      have hl : raw32503step0Labels = raw32503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32503 raw32503Labels permutation520 hz
    mixedMoment B raw32503step0 raw32503step0Labels = mixedMoment B raw32503step1 raw32503step1Labels := by
      have hz : ∀ j, raw32503step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw32503step1 = (fun i j => raw32503step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw32503step1 raw32503step0; decide +kernel
      have hl : raw32503step1Labels = raw32503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32503step0 raw32503step0Labels permutation104 hz
    mixedMoment B raw32503step1 raw32503step1Labels = mixedMoment B raw32503step2 raw32503step2Labels := by
      have ha : raw32503step2 = (fun i j => raw32503step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32503step2 raw32503step1; decide +kernel
      have hl : raw32503step2Labels = raw32503step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32503step1 raw32503step1Labels permutation26 permutation0
    mixedMoment B raw32503step2 raw32503step2Labels = mixedMoment B raw32503step3 raw32503step3Labels := by
      have ha : raw32503step3 = -raw32503step2 := by apply Matrix.ext; change ∀ i j, raw32503step3 i j = -(raw32503step2 i j); unfold raw32503step3 raw32503step2; decide +kernel
      have hl : raw32503step3Labels = raw32503step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32512 raw32512Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw32512 raw32512Labels = mixedMoment B raw32512step0 raw32512step0Labels := by
      have ha : raw32512step0 = (fun i j => raw32512 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32512step0 raw32512; decide +kernel
      have hl : raw32512step0Labels = raw32512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32512 raw32512Labels permutation265 permutation2
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical32513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32513 raw32513Labels = mixedMoment B node2864 node2864Labels := by
  calc
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical32514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32514 raw32514Labels = mixedMoment B node2814 node2814Labels := by
  calc
    _ = mixedMoment B node2814 node2814Labels := by rfl

theorem canonical32515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32515 raw32515Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw32515 raw32515Labels = mixedMoment B raw32515step0 raw32515step0Labels := by
      have ha : raw32515step0 = (fun i j => raw32515 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32515step0 raw32515; decide +kernel
      have hl : raw32515step0Labels = raw32515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32515 raw32515Labels permutation155 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

theorem canonical32516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32516 raw32516Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw32516 raw32516Labels = mixedMoment B raw32516step0 raw32516step0Labels := by
      have ha : raw32516step0 = (fun i j => raw32516 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32516step0 raw32516; decide +kernel
      have hl : raw32516step0Labels = raw32516Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32516 raw32516Labels permutation153 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

theorem canonical32517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32517 raw32517Labels = mixedMoment B node2800 node2800Labels := by
  calc
    _ = mixedMoment B node2800 node2800Labels := by rfl

theorem canonical32518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32518 raw32518Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw32518 raw32518Labels = mixedMoment B raw32518step0 raw32518step0Labels := by
      have ha : raw32518step0 = (fun i j => raw32518 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32518step0 raw32518; decide +kernel
      have hl : raw32518step0Labels = raw32518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32518 raw32518Labels permutation164 permutation2
    _ = mixedMoment B node2809 node2809Labels := by rfl

theorem canonical32519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32519 raw32519Labels = mixedMoment B node2799 node2799Labels := by
  calc
    mixedMoment B raw32519 raw32519Labels = mixedMoment B raw32519step0 raw32519step0Labels := by
      have ha : raw32519step0 = (fun i j => raw32519 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32519step0 raw32519; decide +kernel
      have hl : raw32519step0Labels = raw32519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32519 raw32519Labels permutation154 permutation2
    _ = mixedMoment B node2799 node2799Labels := by rfl

theorem canonical32520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32520 raw32520Labels = mixedMoment B node2801 node2801Labels := by
  calc
    _ = mixedMoment B node2801 node2801Labels := by rfl

theorem canonical32521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32521 raw32521Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw32521 raw32521Labels = mixedMoment B raw32521step0 raw32521step0Labels := by
      have ha : raw32521step0 = (fun i j => raw32521 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32521step0 raw32521; decide +kernel
      have hl : raw32521step0Labels = raw32521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32521 raw32521Labels permutation154 permutation2
    _ = mixedMoment B node2797 node2797Labels := by rfl

theorem canonical32522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32522 raw32522Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw32522 raw32522Labels = mixedMoment B raw32522step0 raw32522step0Labels := by
      have ha : raw32522step0 = (fun i j => raw32522 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32522step0 raw32522; decide +kernel
      have hl : raw32522step0Labels = raw32522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32522 raw32522Labels permutation265 permutation2
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical32523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32523 raw32523Labels = mixedMoment B node2861 node2861Labels := by
  calc
    _ = mixedMoment B node2861 node2861Labels := by rfl

theorem canonical32524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32524 raw32524Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw32524 raw32524Labels = mixedMoment B raw32524step0 raw32524step0Labels := by
      have ha : raw32524step0 = (fun i j => raw32524 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32524step0 raw32524; decide +kernel
      have hl : raw32524step0Labels = raw32524Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32524 raw32524Labels permutation160 permutation2
    _ = mixedMoment B node2807 node2807Labels := by rfl

theorem canonical32525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32525 raw32525Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw32525 raw32525Labels = mixedMoment B raw32525step0 raw32525step0Labels := by
      have ha : raw32525step0 = (fun i j => raw32525 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32525step0 raw32525; decide +kernel
      have hl : raw32525step0Labels = raw32525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32525 raw32525Labels permutation154 permutation2
    _ = mixedMoment B node2798 node2798Labels := by rfl

theorem canonical32526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32526 raw32526Labels = mixedMoment B node2798 node2798Labels := by
  calc
    _ = mixedMoment B node2798 node2798Labels := by rfl

theorem canonical32527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32527 raw32527Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw32527 raw32527Labels = mixedMoment B raw32527step0 raw32527step0Labels := by
      have ha : raw32527step0 = (fun i j => raw32527 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32527step0 raw32527; decide +kernel
      have hl : raw32527step0Labels = raw32527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32527 raw32527Labels permutation664 permutation2
    mixedMoment B raw32527step0 raw32527step0Labels = mixedMoment B raw32527step1 raw32527step1Labels := by
      have ha : raw32527step1 = -raw32527step0 := by apply Matrix.ext; change ∀ i j, raw32527step1 i j = -(raw32527step0 i j); unfold raw32527step1 raw32527step0; decide +kernel
      have hl : raw32527step1Labels = raw32527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2524 node2524Labels := by rfl

theorem canonical32528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32528 raw32528Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw32528 raw32528Labels = mixedMoment B raw32528step0 raw32528step0Labels := by
      have hz : ∀ j, raw32528 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32528step0 = (fun i j => raw32528 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32528step0 raw32528; decide +kernel
      have hl : raw32528step0Labels = raw32528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32528 raw32528Labels permutation520 hz
    mixedMoment B raw32528step0 raw32528step0Labels = mixedMoment B raw32528step1 raw32528step1Labels := by
      have hz : ∀ j, raw32528step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw32528step1 = (fun i j => raw32528step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw32528step1 raw32528step0; decide +kernel
      have hl : raw32528step1Labels = raw32528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32528step0 raw32528step0Labels permutation104 hz
    mixedMoment B raw32528step1 raw32528step1Labels = mixedMoment B raw32528step2 raw32528step2Labels := by
      have ha : raw32528step2 = (fun i j => raw32528step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32528step2 raw32528step1; decide +kernel
      have hl : raw32528step2Labels = raw32528step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32528step1 raw32528step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical32529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32529 raw32529Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw32529 raw32529Labels = mixedMoment B raw32529step0 raw32529step0Labels := by
      have ha : raw32529step0 = (fun i j => raw32529 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32529step0 raw32529; decide +kernel
      have hl : raw32529step0Labels = raw32529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32529 raw32529Labels permutation194 permutation4
    mixedMoment B raw32529step0 raw32529step0Labels = mixedMoment B raw32529step1 raw32529step1Labels := by
      have ha : raw32529step1 = -raw32529step0 := by apply Matrix.ext; change ∀ i j, raw32529step1 i j = -(raw32529step0 i j); unfold raw32529step1 raw32529step0; decide +kernel
      have hl : raw32529step1Labels = raw32529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical32530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32530 raw32530Labels = mixedMoment B node2036 node2036Labels := by
  calc
    mixedMoment B raw32530 raw32530Labels = mixedMoment B raw32530step0 raw32530step0Labels := by
      have ha : raw32530step0 = (fun i j => raw32530 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32530step0 raw32530; decide +kernel
      have hl : raw32530step0Labels = raw32530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32530 raw32530Labels permutation197 permutation4
    mixedMoment B raw32530step0 raw32530step0Labels = mixedMoment B raw32530step1 raw32530step1Labels := by
      have ha : raw32530step1 = -raw32530step0 := by apply Matrix.ext; change ∀ i j, raw32530step1 i j = -(raw32530step0 i j); unfold raw32530step1 raw32530step0; decide +kernel
      have hl : raw32530step1Labels = raw32530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2036 node2036Labels := by rfl

theorem canonical32531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32531 raw32531Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw32531 raw32531Labels = mixedMoment B raw32531step0 raw32531step0Labels := by
      have hz : ∀ j, raw32531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32531step0 = (fun i j => raw32531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32531step0 raw32531; decide +kernel
      have hl : raw32531step0Labels = raw32531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32531 raw32531Labels permutation346 hz
    mixedMoment B raw32531step0 raw32531step0Labels = mixedMoment B raw32531step1 raw32531step1Labels := by
      have ha : raw32531step1 = (fun i j => raw32531step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32531step1 raw32531step0; decide +kernel
      have hl : raw32531step1Labels = raw32531step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32531step0 raw32531step0Labels permutation50 permutation4
    mixedMoment B raw32531step1 raw32531step1Labels = mixedMoment B raw32531step2 raw32531step2Labels := by
      have ha : raw32531step2 = -raw32531step1 := by apply Matrix.ext; change ∀ i j, raw32531step2 i j = -(raw32531step1 i j); unfold raw32531step2 raw32531step1; decide +kernel
      have hl : raw32531step2Labels = raw32531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical32532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32532 raw32532Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw32532 raw32532Labels = mixedMoment B raw32532step0 raw32532step0Labels := by
      have ha : raw32532step0 = (fun i j => raw32532 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32532step0 raw32532; decide +kernel
      have hl : raw32532step0Labels = raw32532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32532 raw32532Labels permutation195 permutation4
    mixedMoment B raw32532step0 raw32532step0Labels = mixedMoment B raw32532step1 raw32532step1Labels := by
      have ha : raw32532step1 = -raw32532step0 := by apply Matrix.ext; change ∀ i j, raw32532step1 i j = -(raw32532step0 i j); unfold raw32532step1 raw32532step0; decide +kernel
      have hl : raw32532step1Labels = raw32532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

theorem canonical32533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32533 raw32533Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw32533 raw32533Labels = mixedMoment B raw32533step0 raw32533step0Labels := by
      have ha : raw32533step0 = (fun i j => raw32533 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32533step0 raw32533; decide +kernel
      have hl : raw32533step0Labels = raw32533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32533 raw32533Labels permutation194 permutation4
    mixedMoment B raw32533step0 raw32533step0Labels = mixedMoment B raw32533step1 raw32533step1Labels := by
      have ha : raw32533step1 = -raw32533step0 := by apply Matrix.ext; change ∀ i j, raw32533step1 i j = -(raw32533step0 i j); unfold raw32533step1 raw32533step0; decide +kernel
      have hl : raw32533step1Labels = raw32533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

theorem canonical32534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32534 raw32534Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw32534 raw32534Labels = mixedMoment B raw32534step0 raw32534step0Labels := by
      have ha : raw32534step0 = (fun i j => raw32534 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32534step0 raw32534; decide +kernel
      have hl : raw32534step0Labels = raw32534Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32534 raw32534Labels permutation176 permutation4
    mixedMoment B raw32534step0 raw32534step0Labels = mixedMoment B raw32534step1 raw32534step1Labels := by
      have ha : raw32534step1 = -raw32534step0 := by apply Matrix.ext; change ∀ i j, raw32534step1 i j = -(raw32534step0 i j); unfold raw32534step1 raw32534step0; decide +kernel
      have hl : raw32534step1Labels = raw32534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical32535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32535 raw32535Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw32535 raw32535Labels = mixedMoment B raw32535step0 raw32535step0Labels := by
      have hz : ∀ j, raw32535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32535step0 = (fun i j => raw32535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32535step0 raw32535; decide +kernel
      have hl : raw32535step0Labels = raw32535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32535 raw32535Labels permutation346 hz
    mixedMoment B raw32535step0 raw32535step0Labels = mixedMoment B raw32535step1 raw32535step1Labels := by
      have ha : raw32535step1 = (fun i j => raw32535step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32535step1 raw32535step0; decide +kernel
      have hl : raw32535step1Labels = raw32535step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32535step0 raw32535step0Labels permutation58 permutation2
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical32536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32536 raw32536Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw32536 raw32536Labels = mixedMoment B raw32536step0 raw32536step0Labels := by
      have hz : ∀ j, raw32536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32536step0 = (fun i j => raw32536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32536step0 raw32536; decide +kernel
      have hl : raw32536step0Labels = raw32536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32536 raw32536Labels permutation346 hz
    mixedMoment B raw32536step0 raw32536step0Labels = mixedMoment B raw32536step1 raw32536step1Labels := by
      have ha : raw32536step1 = (fun i j => raw32536step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32536step1 raw32536step0; decide +kernel
      have hl : raw32536step1Labels = raw32536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32536step0 raw32536step0Labels permutation34 permutation2
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical32537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32537 raw32537Labels = mixedMoment B node2810 node2810Labels := by
  calc
    mixedMoment B raw32537 raw32537Labels = mixedMoment B raw32537step0 raw32537step0Labels := by
      have ha : raw32537step0 = (fun i j => raw32537 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32537step0 raw32537; decide +kernel
      have hl : raw32537step0Labels = raw32537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32537 raw32537Labels permutation154 permutation2
    _ = mixedMoment B node2810 node2810Labels := by rfl

theorem canonical32538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32538 raw32538Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw32538 raw32538Labels = mixedMoment B raw32538step0 raw32538step0Labels := by
      have hz : ∀ j, raw32538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32538step0 = (fun i j => raw32538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32538step0 raw32538; decide +kernel
      have hl : raw32538step0Labels = raw32538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32538 raw32538Labels permutation346 hz
    mixedMoment B raw32538step0 raw32538step0Labels = mixedMoment B raw32538step1 raw32538step1Labels := by
      have ha : raw32538step1 = (fun i j => raw32538step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32538step1 raw32538step0; decide +kernel
      have hl : raw32538step1Labels = raw32538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32538step0 raw32538step0Labels permutation35 permutation2
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical32539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32539 raw32539Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw32539 raw32539Labels = mixedMoment B raw32539step0 raw32539step0Labels := by
      have hz : ∀ j, raw32539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32539step0 = (fun i j => raw32539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32539step0 raw32539; decide +kernel
      have hl : raw32539step0Labels = raw32539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32539 raw32539Labels permutation346 hz
    mixedMoment B raw32539step0 raw32539step0Labels = mixedMoment B raw32539step1 raw32539step1Labels := by
      have ha : raw32539step1 = (fun i j => raw32539step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32539step1 raw32539step0; decide +kernel
      have hl : raw32539step1Labels = raw32539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32539step0 raw32539step0Labels permutation33 permutation2
    _ = mixedMoment B node2819 node2819Labels := by rfl

theorem canonical32540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32540 raw32540Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw32540 raw32540Labels = mixedMoment B raw32540step0 raw32540step0Labels := by
      have hz : ∀ j, raw32540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32540step0 = (fun i j => raw32540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32540step0 raw32540; decide +kernel
      have hl : raw32540step0Labels = raw32540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32540 raw32540Labels permutation346 hz
    mixedMoment B raw32540step0 raw32540step0Labels = mixedMoment B raw32540step1 raw32540step1Labels := by
      have ha : raw32540step1 = (fun i j => raw32540step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32540step1 raw32540step0; decide +kernel
      have hl : raw32540step1Labels = raw32540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32540step0 raw32540step0Labels permutation34 permutation2
    _ = mixedMoment B node2816 node2816Labels := by rfl

theorem canonical32541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32541 raw32541Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw32541 raw32541Labels = mixedMoment B raw32541step0 raw32541step0Labels := by
      have hz : ∀ j, raw32541 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw32541step0 = (fun i j => raw32541 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw32541step0 raw32541; decide +kernel
      have hl : raw32541step0Labels = raw32541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32541 raw32541Labels permutation590 hz
    mixedMoment B raw32541step0 raw32541step0Labels = mixedMoment B raw32541step1 raw32541step1Labels := by
      have hz : ∀ j, raw32541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32541step1 = (fun i j => raw32541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32541step1 raw32541step0; decide +kernel
      have hl : raw32541step1Labels = raw32541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32541step0 raw32541step0Labels permutation80 hz
    mixedMoment B raw32541step1 raw32541step1Labels = mixedMoment B raw32541step2 raw32541step2Labels := by
      have ha : raw32541step2 = (fun i j => raw32541step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32541step2 raw32541step1; decide +kernel
      have hl : raw32541step2Labels = raw32541step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32541step1 raw32541step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9348 raw9348Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9348 raw9348Labels = mixedMoment B raw9348step0 raw9348step0Labels := by
      have hz : ∀ j, raw9348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9348step0 = (fun i j => raw9348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9348step0 raw9348; decide +kernel
      have hl : raw9348step0Labels = raw9348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9348 raw9348Labels permutation265 hz
    mixedMoment B raw9348step0 raw9348step0Labels = mixedMoment B raw9348step1 raw9348step1Labels := by
      have ha : raw9348step1 = (fun i j => raw9348step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9348step1 raw9348step0; decide +kernel
      have hl : raw9348step1Labels = raw9348step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9348step0 raw9348step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9354 raw9354Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw9354 raw9354Labels = mixedMoment B raw9354step0 raw9354step0Labels := by
      have ha : raw9354step0 = (fun i j => raw9354 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9354step0 raw9354; decide +kernel
      have hl : raw9354step0Labels = raw9354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9354 raw9354Labels permutation158 permutation2
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical9355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9355 raw9355Labels = mixedMoment B node2573 node2573Labels := by
  calc
    _ = mixedMoment B node2573 node2573Labels := by rfl

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

theorem sound1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1158 node1158Labels = Sparse.eval nodeValue1158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1158) = mixedMoment B node1158 node1158Labels := rfl
  simpa [nodeValue1158, Sparse.eval] using hc.symm

theorem sound1169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1169 node1169Labels = Sparse.eval nodeValue1169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1169) = mixedMoment B node1169 node1169Labels := rfl
  simpa [nodeValue1169, Sparse.eval] using hc.symm

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

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

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

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

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

theorem sound2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2031 node2031Labels = Sparse.eval nodeValue2031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2031) = mixedMoment B node2031 node2031Labels := rfl
  simpa [nodeValue2031, Sparse.eval] using hc.symm

theorem sound2036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2036 node2036Labels = Sparse.eval nodeValue2036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2036) = mixedMoment B node2036 node2036Labels := rfl
  simpa [nodeValue2036, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

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

theorem sound2354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2354 node2354Labels = Sparse.eval nodeValue2354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2354) = mixedMoment B node2354 node2354Labels := rfl
  simpa [nodeValue2354, Sparse.eval] using hc.symm

theorem sound2361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2361 node2361Labels = Sparse.eval nodeValue2361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2361) = mixedMoment B node2361 node2361Labels := rfl
  simpa [nodeValue2361, Sparse.eval] using hc.symm

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

theorem sound2422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2422 node2422Labels = Sparse.eval nodeValue2422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2422) = mixedMoment B node2422 node2422Labels := rfl
  simpa [nodeValue2422, Sparse.eval] using hc.symm

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

theorem sound2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2524 node2524Labels = Sparse.eval nodeValue2524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2524) = mixedMoment B node2524 node2524Labels := rfl
  simpa [nodeValue2524, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2567 node2567Labels = Sparse.eval nodeValue2567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2567) = mixedMoment B node2567 node2567Labels := rfl
  simpa [nodeValue2567, Sparse.eval] using hc.symm

theorem sound2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2573 node2573Labels = Sparse.eval nodeValue2573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2573) = mixedMoment B node2573 node2573Labels := rfl
  simpa [nodeValue2573, Sparse.eval] using hc.symm

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

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

theorem sound2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2798 node2798Labels = Sparse.eval nodeValue2798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2798) = mixedMoment B node2798 node2798Labels := rfl
  simpa [nodeValue2798, Sparse.eval] using hc.symm

theorem sound2799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2799 node2799Labels = Sparse.eval nodeValue2799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2799) = mixedMoment B node2799 node2799Labels := rfl
  simpa [nodeValue2799, Sparse.eval] using hc.symm

theorem sound2800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2800 node2800Labels = Sparse.eval nodeValue2800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2800) = mixedMoment B node2800 node2800Labels := rfl
  simpa [nodeValue2800, Sparse.eval] using hc.symm

theorem sound2801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2801 node2801Labels = Sparse.eval nodeValue2801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2801) = mixedMoment B node2801 node2801Labels := rfl
  simpa [nodeValue2801, Sparse.eval] using hc.symm

theorem sound2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2807 node2807Labels = Sparse.eval nodeValue2807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2807) = mixedMoment B node2807 node2807Labels := rfl
  simpa [nodeValue2807, Sparse.eval] using hc.symm

theorem sound2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2809 node2809Labels = Sparse.eval nodeValue2809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2809) = mixedMoment B node2809 node2809Labels := rfl
  simpa [nodeValue2809, Sparse.eval] using hc.symm

theorem sound2810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2810 node2810Labels = Sparse.eval nodeValue2810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2810) = mixedMoment B node2810 node2810Labels := rfl
  simpa [nodeValue2810, Sparse.eval] using hc.symm

theorem sound2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2814 node2814Labels = Sparse.eval nodeValue2814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2814) = mixedMoment B node2814 node2814Labels := rfl
  simpa [nodeValue2814, Sparse.eval] using hc.symm

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

theorem sound2816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2816 node2816Labels = Sparse.eval nodeValue2816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2816) = mixedMoment B node2816 node2816Labels := rfl
  simpa [nodeValue2816, Sparse.eval] using hc.symm

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

theorem sound2819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2819 node2819Labels = Sparse.eval nodeValue2819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2819) = mixedMoment B node2819 node2819Labels := rfl
  simpa [nodeValue2819, Sparse.eval] using hc.symm

theorem sound2822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2822 node2822Labels = Sparse.eval nodeValue2822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2822) = mixedMoment B node2822 node2822Labels := rfl
  simpa [nodeValue2822, Sparse.eval] using hc.symm

theorem sound2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2824 node2824Labels = Sparse.eval nodeValue2824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2824) = mixedMoment B node2824 node2824Labels := rfl
  simpa [nodeValue2824, Sparse.eval] using hc.symm

theorem sound2826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2826 node2826Labels = Sparse.eval nodeValue2826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2826) = mixedMoment B node2826 node2826Labels := rfl
  simpa [nodeValue2826, Sparse.eval] using hc.symm

theorem sound2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2847 node2847Labels = Sparse.eval nodeValue2847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2847) = mixedMoment B node2847 node2847Labels := rfl
  simpa [nodeValue2847, Sparse.eval] using hc.symm

theorem sound2861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2861 node2861Labels = Sparse.eval nodeValue2861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2861) = mixedMoment B node2861 node2861Labels := rfl
  simpa [nodeValue2861, Sparse.eval] using hc.symm

theorem sound2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2862 node2862Labels = Sparse.eval nodeValue2862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2862) = mixedMoment B node2862 node2862Labels := rfl
  simpa [nodeValue2862, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

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

theorem sound2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2895 node2895Labels = Sparse.eval nodeValue2895 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2895) = mixedMoment B node2895 node2895Labels := rfl
  simpa [nodeValue2895, Sparse.eval] using hc.symm

theorem sound2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2896 node2896Labels = Sparse.eval nodeValue2896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2896) = mixedMoment B node2896 node2896Labels := rfl
  simpa [nodeValue2896, Sparse.eval] using hc.symm

theorem sound2898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2898 node2898Labels = Sparse.eval nodeValue2898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2898) = mixedMoment B node2898 node2898Labels := rfl
  simpa [nodeValue2898, Sparse.eval] using hc.symm

theorem sound2922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2922 node2922Labels = Sparse.eval nodeValue2922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2922) = mixedMoment B node2922 node2922Labels := rfl
  simpa [nodeValue2922, Sparse.eval] using hc.symm

theorem sound2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2923 node2923Labels = Sparse.eval nodeValue2923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2923) = mixedMoment B node2923 node2923Labels := rfl
  simpa [nodeValue2923, Sparse.eval] using hc.symm

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

theorem sound2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2928 node2928Labels = Sparse.eval nodeValue2928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2928) = mixedMoment B node2928 node2928Labels := rfl
  simpa [nodeValue2928, Sparse.eval] using hc.symm

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

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3407 node3407Labels = Sparse.eval nodeValue3407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3407) = mixedMoment B node3407 node3407Labels := rfl
  simpa [nodeValue3407, Sparse.eval] using hc.symm

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

theorem sound3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3455 node3455Labels = Sparse.eval nodeValue3455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3455) = mixedMoment B node3455 node3455Labels := rfl
  simpa [nodeValue3455, Sparse.eval] using hc.symm

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

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3496 node3496Labels = Sparse.eval nodeValue3496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3496) = mixedMoment B node3496 node3496Labels := rfl
  simpa [nodeValue3496, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

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

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

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

theorem sound3597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3597 node3597Labels = Sparse.eval nodeValue3597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3597) = mixedMoment B node3597 node3597Labels := rfl
  simpa [nodeValue3597, Sparse.eval] using hc.symm

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

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

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

theorem sound3748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3748 node3748Labels = Sparse.eval nodeValue3748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3748) = mixedMoment B node3748 node3748Labels := rfl
  simpa [nodeValue3748, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

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

theorem zero3798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = 0 := by
  exact mixedMoment_order_one B hB node3798 node3798Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

theorem sound3798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = Sparse.eval nodeValue3798 (mixedVector B) := by
  simpa only [nodeValue3798, Sparse.eval_nil] using zero3798 B _hB _hF

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

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

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3973 node3973Labels = Sparse.eval nodeValue3973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3973) = mixedMoment B node3973 node3973Labels := rfl
  simpa [nodeValue3973, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2356 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2356 + difference 0 2) (sourceB2356 + difference 2 0) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2356 + difference 0 2) (sourceB2356 + difference 2 0) sourceC2356) = raw32259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32259; decide +kernel
    rw [ha]
    exact (canonical32259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2356 + difference 1 2) (sourceB2356 + difference 2 1) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2356 + difference 1 2) (sourceB2356 + difference 2 1) sourceC2356) = raw32260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32260; decide +kernel
    rw [ha]
    exact (canonical32260 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2356 + difference 2 2) (sourceB2356 + difference 2 2) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2356 + difference 2 2) (sourceB2356 + difference 2 2) sourceC2356) = raw13314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw13314; decide +kernel
    rw [ha]
    exact (canonical13314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2356 + difference 3 2) (sourceB2356 + difference 2 3) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2356 + difference 3 2) (sourceB2356 + difference 2 3) sourceC2356) = raw32261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32261; decide +kernel
    rw [ha]
    exact (canonical32261 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2356 + difference 4 2) (sourceB2356 + difference 2 4) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2898) := by
    have ha : (tripleCharges (sourceA2356 + difference 4 2) (sourceB2356 + difference 2 4) sourceC2356) = raw32262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32262; decide +kernel
    rw [ha]
    exact (canonical32262 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2356 + difference 5 2) (sourceB2356 + difference 2 5) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2356 + difference 5 2) (sourceB2356 + difference 2 5) sourceC2356) = raw32263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32263; decide +kernel
    rw [ha]
    exact (canonical32263 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2356 + sourceB2356) sourceC2356) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2356 + sourceB2356) sourceC2356) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2356 sourceB2356 sourceC2356 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2356 sourceB2356 sourceC2356
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2356, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2357 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 0) (sourceB2357 + difference 0 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 0) (sourceB2357 + difference 0 2) sourceC2357) = raw32264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32264; decide +kernel
    rw [ha]
    exact (canonical32264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 1) (sourceB2357 + difference 1 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2354) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 1) (sourceB2357 + difference 1 2) sourceC2357) = raw32265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32265; decide +kernel
    rw [ha]
    exact (canonical32265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 2) (sourceB2357 + difference 2 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 2) (sourceB2357 + difference 2 2) sourceC2357) = raw32266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32266; decide +kernel
    rw [ha]
    exact (canonical32266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 3) (sourceB2357 + difference 3 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 3) (sourceB2357 + difference 3 2) sourceC2357) = raw32267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32267; decide +kernel
    rw [ha]
    exact (canonical32267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 4) (sourceB2357 + difference 4 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 4) (sourceB2357 + difference 4 2) sourceC2357) = raw32268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32268; decide +kernel
    rw [ha]
    exact (canonical32268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 5) (sourceB2357 + difference 5 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 5) (sourceB2357 + difference 5 2) sourceC2357) = raw32269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32269; decide +kernel
    rw [ha]
    exact (canonical32269 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2357 + sourceB2357) sourceC2357) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2357 + sourceB2357) sourceC2357) = raw32270 := by
      apply Matrix.ext; unfold doubleCharges sourceA2357 sourceB2357 sourceC2357 raw32270; decide +kernel
    rw [ha]
    exact (canonical32270 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2357 sourceB2357 sourceC2357
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2357, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2358 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2358 + difference 0 2) (sourceB2358 + difference 2 0) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2358 + difference 0 2) (sourceB2358 + difference 2 0) sourceC2358) = raw17026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw17026; decide +kernel
    rw [ha]
    exact (canonical17026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2358 + difference 1 2) (sourceB2358 + difference 2 1) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2358 + difference 1 2) (sourceB2358 + difference 2 1) sourceC2358) = raw32271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32271; decide +kernel
    rw [ha]
    exact (canonical32271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2358 + difference 2 2) (sourceB2358 + difference 2 2) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2358 + difference 2 2) (sourceB2358 + difference 2 2) sourceC2358) = raw17020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw17020; decide +kernel
    rw [ha]
    exact (canonical17020 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2358 + difference 3 2) (sourceB2358 + difference 2 3) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2358 + difference 3 2) (sourceB2358 + difference 2 3) sourceC2358) = raw32272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32272; decide +kernel
    rw [ha]
    exact (canonical32272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2358 + difference 4 2) (sourceB2358 + difference 2 4) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2898) := by
    have ha : (tripleCharges (sourceA2358 + difference 4 2) (sourceB2358 + difference 2 4) sourceC2358) = raw32273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32273; decide +kernel
    rw [ha]
    exact (canonical32273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2358 + difference 5 2) (sourceB2358 + difference 2 5) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA2358 + difference 5 2) (sourceB2358 + difference 2 5) sourceC2358) = raw32274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32274; decide +kernel
    rw [ha]
    exact (canonical32274 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2358 + sourceB2358) sourceC2358) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2358 + sourceB2358) sourceC2358) = raw17023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2358 sourceB2358 sourceC2358 raw17023; decide +kernel
    rw [ha]
    exact (canonical17023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2358 sourceB2358 sourceC2358
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2358, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2359 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 0) (sourceB2359 + difference 0 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 0) (sourceB2359 + difference 0 0) sourceC2359) = raw32275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32275; decide +kernel
    rw [ha]
    exact (canonical32275 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 1) (sourceB2359 + difference 1 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3748) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 1) (sourceB2359 + difference 1 0) sourceC2359) = raw32276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32276; decide +kernel
    rw [ha]
    exact (canonical32276 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 2) (sourceB2359 + difference 2 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 2) (sourceB2359 + difference 2 0) sourceC2359) = raw32277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32277; decide +kernel
    rw [ha]
    exact (canonical32277 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 3) (sourceB2359 + difference 3 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 3) (sourceB2359 + difference 3 0) sourceC2359) = raw32278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32278; decide +kernel
    rw [ha]
    exact (canonical32278 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 4) (sourceB2359 + difference 4 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 4) (sourceB2359 + difference 4 0) sourceC2359) = raw32279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32279; decide +kernel
    rw [ha]
    exact (canonical32279 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 5) (sourceB2359 + difference 5 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 5) (sourceB2359 + difference 5 0) sourceC2359) = raw32280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32280; decide +kernel
    rw [ha]
    exact (canonical32280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2359 + sourceB2359) sourceC2359) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2359 + sourceB2359) sourceC2359) = raw32281 := by
      apply Matrix.ext; unfold doubleCharges sourceA2359 sourceB2359 sourceC2359 raw32281; decide +kernel
    rw [ha]
    exact (canonical32281 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2359 sourceB2359 sourceC2359
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2359, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 1) (sourceB2367 + difference 1 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 1) (sourceB2367 + difference 1 0) sourceC2367) = raw32442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32442; decide +kernel
    rw [ha]
    exact (canonical32442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 2) (sourceB2367 + difference 2 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 2) (sourceB2367 + difference 2 0) sourceC2367) = raw32443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32443; decide +kernel
    rw [ha]
    exact (canonical32443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 3) (sourceB2367 + difference 3 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 3) (sourceB2367 + difference 3 0) sourceC2367) = raw32444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32444; decide +kernel
    rw [ha]
    exact (canonical32444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 4) (sourceB2367 + difference 4 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 4) (sourceB2367 + difference 4 0) sourceC2367) = raw32445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32445; decide +kernel
    rw [ha]
    exact (canonical32445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 5) (sourceB2367 + difference 5 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 5) (sourceB2367 + difference 5 0) sourceC2367) = raw32446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32446; decide +kernel
    rw [ha]
    exact (canonical32446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 0) (sourceB2367 + difference 0 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 0) (sourceB2367 + difference 0 1) sourceC2367) = raw32447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32447; decide +kernel
    rw [ha]
    exact (canonical32447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 2) (sourceB2367 + difference 2 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 2) (sourceB2367 + difference 2 1) sourceC2367) = raw32448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32448; decide +kernel
    rw [ha]
    exact (canonical32448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 3) (sourceB2367 + difference 3 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 3) (sourceB2367 + difference 3 1) sourceC2367) = raw32449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32449; decide +kernel
    rw [ha]
    exact (canonical32449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 4) (sourceB2367 + difference 4 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 4) (sourceB2367 + difference 4 1) sourceC2367) = raw32450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32450; decide +kernel
    rw [ha]
    exact (canonical32450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 5) (sourceB2367 + difference 5 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 5) (sourceB2367 + difference 5 1) sourceC2367) = raw32451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32451; decide +kernel
    rw [ha]
    exact (canonical32451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 0) (sourceB2367 + difference 0 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 0) (sourceB2367 + difference 0 2) sourceC2367) = raw32452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32452; decide +kernel
    rw [ha]
    exact (canonical32452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 1) (sourceB2367 + difference 1 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 1) (sourceB2367 + difference 1 2) sourceC2367) = raw32453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32453; decide +kernel
    rw [ha]
    exact (canonical32453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 3) (sourceB2367 + difference 3 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 3) (sourceB2367 + difference 3 2) sourceC2367) = raw32454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32454; decide +kernel
    rw [ha]
    exact (canonical32454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 4) (sourceB2367 + difference 4 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 4) (sourceB2367 + difference 4 2) sourceC2367) = raw32455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32455; decide +kernel
    rw [ha]
    exact (canonical32455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 5) (sourceB2367 + difference 5 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 5) (sourceB2367 + difference 5 2) sourceC2367) = raw32456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32456; decide +kernel
    rw [ha]
    exact (canonical32456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 0) (sourceB2367 + difference 0 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 0) (sourceB2367 + difference 0 3) sourceC2367) = raw32457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32457; decide +kernel
    rw [ha]
    exact (canonical32457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 1) (sourceB2367 + difference 1 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 1) (sourceB2367 + difference 1 3) sourceC2367) = raw32458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32458; decide +kernel
    rw [ha]
    exact (canonical32458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 2) (sourceB2367 + difference 2 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3599) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 2) (sourceB2367 + difference 2 3) sourceC2367) = raw32459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32459; decide +kernel
    rw [ha]
    exact (canonical32459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 4) (sourceB2367 + difference 4 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 4) (sourceB2367 + difference 4 3) sourceC2367) = raw32460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32460; decide +kernel
    rw [ha]
    exact (canonical32460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 5) (sourceB2367 + difference 5 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 5) (sourceB2367 + difference 5 3) sourceC2367) = raw32461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32461; decide +kernel
    rw [ha]
    exact (canonical32461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 0) (sourceB2367 + difference 0 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 0) (sourceB2367 + difference 0 4) sourceC2367) = raw32462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32462; decide +kernel
    rw [ha]
    exact (canonical32462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 1) (sourceB2367 + difference 1 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 1) (sourceB2367 + difference 1 4) sourceC2367) = raw32463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32463; decide +kernel
    rw [ha]
    exact (canonical32463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 2) (sourceB2367 + difference 2 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3597) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 2) (sourceB2367 + difference 2 4) sourceC2367) = raw32464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32464; decide +kernel
    rw [ha]
    exact (canonical32464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 3) (sourceB2367 + difference 3 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 3) (sourceB2367 + difference 3 4) sourceC2367) = raw32465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32465; decide +kernel
    rw [ha]
    exact (canonical32465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 5) (sourceB2367 + difference 5 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 5) (sourceB2367 + difference 5 4) sourceC2367) = raw32466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32466; decide +kernel
    rw [ha]
    exact (canonical32466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 0) (sourceB2367 + difference 0 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 0) (sourceB2367 + difference 0 5) sourceC2367) = raw32467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32467; decide +kernel
    rw [ha]
    exact (canonical32467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 1) (sourceB2367 + difference 1 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 1) (sourceB2367 + difference 1 5) sourceC2367) = raw32468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32468; decide +kernel
    rw [ha]
    exact (canonical32468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 2) (sourceB2367 + difference 2 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 2) (sourceB2367 + difference 2 5) sourceC2367) = raw32469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32469; decide +kernel
    rw [ha]
    exact (canonical32469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 3) (sourceB2367 + difference 3 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 3) (sourceB2367 + difference 3 5) sourceC2367) = raw32470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32470; decide +kernel
    rw [ha]
    exact (canonical32470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 4) (sourceB2367 + difference 4 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 4) (sourceB2367 + difference 4 5) sourceC2367) = raw32471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32471; decide +kernel
    rw [ha]
    exact (canonical32471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2367 sourceB2367 sourceC2367
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2367, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2368 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2368 + difference 0 1) (sourceB2368 + difference 1 0) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2368 + difference 0 1) (sourceB2368 + difference 1 0) sourceC2368) = raw32472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32472; decide +kernel
    rw [ha]
    exact (canonical32472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2368 + difference 1 1) (sourceB2368 + difference 1 1) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2368 + difference 1 1) (sourceB2368 + difference 1 1) sourceC2368) = raw23905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw23905; decide +kernel
    rw [ha]
    exact (canonical23905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2368 + difference 2 1) (sourceB2368 + difference 1 2) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2826) := by
    have ha : (tripleCharges (sourceA2368 + difference 2 1) (sourceB2368 + difference 1 2) sourceC2368) = raw32473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32473; decide +kernel
    rw [ha]
    exact (canonical32473 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2368 + difference 3 1) (sourceB2368 + difference 1 3) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2368 + difference 3 1) (sourceB2368 + difference 1 3) sourceC2368) = raw32474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32474; decide +kernel
    rw [ha]
    exact (canonical32474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2368 + difference 4 1) (sourceB2368 + difference 1 4) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2368 + difference 4 1) (sourceB2368 + difference 1 4) sourceC2368) = raw32475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32475; decide +kernel
    rw [ha]
    exact (canonical32475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2368 + difference 5 1) (sourceB2368 + difference 1 5) sourceC2368) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2368 + difference 5 1) (sourceB2368 + difference 1 5) sourceC2368) = raw32476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2368 sourceB2368 sourceC2368 difference raw32476; decide +kernel
    rw [ha]
    exact (canonical32476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2368 + sourceB2368) sourceC2368) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2368 + sourceB2368) sourceC2368) = raw23911 := by
      apply Matrix.ext; unfold doubleCharges sourceA2368 sourceB2368 sourceC2368 raw23911; decide +kernel
    rw [ha]
    exact (canonical23911 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2368 sourceB2368 sourceC2368
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2368, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2370 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 0) (sourceB2370 + difference 0 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1169) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 0) (sourceB2370 + difference 0 2) sourceC2370) = raw32493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32493; decide +kernel
    rw [ha]
    exact (canonical32493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 1) (sourceB2370 + difference 1 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2361) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 1) (sourceB2370 + difference 1 2) sourceC2370) = raw32494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32494; decide +kernel
    rw [ha]
    exact (canonical32494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 2) (sourceB2370 + difference 2 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 2) (sourceB2370 + difference 2 2) sourceC2370) = raw9355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw9355; decide +kernel
    rw [ha]
    exact (canonical9355 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 3) (sourceB2370 + difference 3 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 3) (sourceB2370 + difference 3 2) sourceC2370) = raw9354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw9354; decide +kernel
    rw [ha]
    exact (canonical9354 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 4) (sourceB2370 + difference 4 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 4) (sourceB2370 + difference 4 2) sourceC2370) = raw32495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32495; decide +kernel
    rw [ha]
    exact (canonical32495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2370 + difference 2 5) (sourceB2370 + difference 5 2) sourceC2370) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2370 + difference 2 5) (sourceB2370 + difference 5 2) sourceC2370) = raw32496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2370 sourceB2370 sourceC2370 difference raw32496; decide +kernel
    rw [ha]
    exact (canonical32496 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2370 + sourceB2370) sourceC2370) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2370 + sourceB2370) sourceC2370) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2370 sourceB2370 sourceC2370 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2370 sourceB2370 sourceC2370
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2370, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2371 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2371 + difference 0 2) (sourceB2371 + difference 2 0) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3496) := by
    have ha : (tripleCharges (sourceA2371 + difference 0 2) (sourceB2371 + difference 2 0) sourceC2371) = raw32497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32497; decide +kernel
    rw [ha]
    exact (canonical32497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2371 + difference 1 2) (sourceB2371 + difference 2 1) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA2371 + difference 1 2) (sourceB2371 + difference 2 1) sourceC2371) = raw32498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32498; decide +kernel
    rw [ha]
    exact (canonical32498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2371 + difference 2 2) (sourceB2371 + difference 2 2) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA2371 + difference 2 2) (sourceB2371 + difference 2 2) sourceC2371) = raw32499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32499; decide +kernel
    rw [ha]
    exact (canonical32499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2371 + difference 3 2) (sourceB2371 + difference 2 3) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2371 + difference 3 2) (sourceB2371 + difference 2 3) sourceC2371) = raw32500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32500; decide +kernel
    rw [ha]
    exact (canonical32500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2371 + difference 4 2) (sourceB2371 + difference 2 4) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2371 + difference 4 2) (sourceB2371 + difference 2 4) sourceC2371) = raw32501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32501; decide +kernel
    rw [ha]
    exact (canonical32501 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2371 + difference 5 2) (sourceB2371 + difference 2 5) sourceC2371) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA2371 + difference 5 2) (sourceB2371 + difference 2 5) sourceC2371) = raw32502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2371 sourceB2371 sourceC2371 difference raw32502; decide +kernel
    rw [ha]
    exact (canonical32502 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2371 + sourceB2371) sourceC2371) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2371 + sourceB2371) sourceC2371) = raw32503 := by
      apply Matrix.ext; unfold doubleCharges sourceA2371 sourceB2371 sourceC2371 raw32503; decide +kernel
    rw [ha]
    exact (canonical32503 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2371 sourceB2371 sourceC2371
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2371, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2374 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2374 + difference 0 1) (sourceB2374 + difference 1 0) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2374 + difference 0 1) (sourceB2374 + difference 1 0) sourceC2374) = raw32512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32512; decide +kernel
    rw [ha]
    exact (canonical32512 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2374 + difference 1 1) (sourceB2374 + difference 1 1) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA2374 + difference 1 1) (sourceB2374 + difference 1 1) sourceC2374) = raw32513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32513; decide +kernel
    rw [ha]
    exact (canonical32513 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2374 + difference 2 1) (sourceB2374 + difference 1 2) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2814) := by
    have ha : (tripleCharges (sourceA2374 + difference 2 1) (sourceB2374 + difference 1 2) sourceC2374) = raw32514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32514; decide +kernel
    rw [ha]
    exact (canonical32514 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2374 + difference 3 1) (sourceB2374 + difference 1 3) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2374 + difference 3 1) (sourceB2374 + difference 1 3) sourceC2374) = raw32515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32515; decide +kernel
    rw [ha]
    exact (canonical32515 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2374 + difference 4 1) (sourceB2374 + difference 1 4) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2374 + difference 4 1) (sourceB2374 + difference 1 4) sourceC2374) = raw32516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32516; decide +kernel
    rw [ha]
    exact (canonical32516 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2374 + difference 5 1) (sourceB2374 + difference 1 5) sourceC2374) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2374 + difference 5 1) (sourceB2374 + difference 1 5) sourceC2374) = raw32517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2374 sourceB2374 sourceC2374 difference raw32517; decide +kernel
    rw [ha]
    exact (canonical32517 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2374 + sourceB2374) sourceC2374) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2374 + sourceB2374) sourceC2374) = raw26393 := by
      apply Matrix.ext; unfold doubleCharges sourceA2374 sourceB2374 sourceC2374 raw26393; decide +kernel
    rw [ha]
    exact (canonical26393 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2374 sourceB2374 sourceC2374
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2374, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2375 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2375 + difference 0 1) (sourceB2375 + difference 1 0) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2375 + difference 0 1) (sourceB2375 + difference 1 0) sourceC2375) = raw16835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw16835; decide +kernel
    rw [ha]
    exact (canonical16835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2375 + difference 1 1) (sourceB2375 + difference 1 1) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA2375 + difference 1 1) (sourceB2375 + difference 1 1) sourceC2375) = raw16829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw16829; decide +kernel
    rw [ha]
    exact (canonical16829 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2375 + difference 2 1) (sourceB2375 + difference 1 2) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2809) := by
    have ha : (tripleCharges (sourceA2375 + difference 2 1) (sourceB2375 + difference 1 2) sourceC2375) = raw32518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32518; decide +kernel
    rw [ha]
    exact (canonical32518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2375 + difference 3 1) (sourceB2375 + difference 1 3) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2375 + difference 3 1) (sourceB2375 + difference 1 3) sourceC2375) = raw32519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32519; decide +kernel
    rw [ha]
    exact (canonical32519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2375 + difference 4 1) (sourceB2375 + difference 1 4) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2375 + difference 4 1) (sourceB2375 + difference 1 4) sourceC2375) = raw32520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32520; decide +kernel
    rw [ha]
    exact (canonical32520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2375 + difference 5 1) (sourceB2375 + difference 1 5) sourceC2375) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA2375 + difference 5 1) (sourceB2375 + difference 1 5) sourceC2375) = raw32521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2375 sourceB2375 sourceC2375 difference raw32521; decide +kernel
    rw [ha]
    exact (canonical32521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2375 + sourceB2375) sourceC2375) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2375 + sourceB2375) sourceC2375) = raw16832 := by
      apply Matrix.ext; unfold doubleCharges sourceA2375 sourceB2375 sourceC2375 raw16832; decide +kernel
    rw [ha]
    exact (canonical16832 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2375 sourceB2375 sourceC2375
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2375, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2376 + difference 0 1) (sourceB2376 + difference 1 0) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2376 + difference 0 1) (sourceB2376 + difference 1 0) sourceC2376) = raw32522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32522; decide +kernel
    rw [ha]
    exact (canonical32522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2376 + difference 1 1) (sourceB2376 + difference 1 1) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA2376 + difference 1 1) (sourceB2376 + difference 1 1) sourceC2376) = raw32523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32523; decide +kernel
    rw [ha]
    exact (canonical32523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2376 + difference 2 1) (sourceB2376 + difference 1 2) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2807) := by
    have ha : (tripleCharges (sourceA2376 + difference 2 1) (sourceB2376 + difference 1 2) sourceC2376) = raw32524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32524; decide +kernel
    rw [ha]
    exact (canonical32524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2376 + difference 3 1) (sourceB2376 + difference 1 3) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2376 + difference 3 1) (sourceB2376 + difference 1 3) sourceC2376) = raw32525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32525; decide +kernel
    rw [ha]
    exact (canonical32525 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2376 + difference 4 1) (sourceB2376 + difference 1 4) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2376 + difference 4 1) (sourceB2376 + difference 1 4) sourceC2376) = raw32526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32526; decide +kernel
    rw [ha]
    exact (canonical32526 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2376 + difference 5 1) (sourceB2376 + difference 1 5) sourceC2376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA2376 + difference 5 1) (sourceB2376 + difference 1 5) sourceC2376) = raw32527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2376 sourceB2376 sourceC2376 difference raw32527; decide +kernel
    rw [ha]
    exact (canonical32527 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2376 + sourceB2376) sourceC2376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2376 + sourceB2376) sourceC2376) = raw32528 := by
      apply Matrix.ext; unfold doubleCharges sourceA2376 sourceB2376 sourceC2376 raw32528; decide +kernel
    rw [ha]
    exact (canonical32528 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2376 sourceB2376 sourceC2376
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2376, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2377 + difference 0 0) (sourceB2377 + difference 0 0) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2377 + difference 0 0) (sourceB2377 + difference 0 0) sourceC2377) = raw32529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32529; decide +kernel
    rw [ha]
    exact (canonical32529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2377 + difference 1 0) (sourceB2377 + difference 0 1) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2036) := by
    have ha : (tripleCharges (sourceA2377 + difference 1 0) (sourceB2377 + difference 0 1) sourceC2377) = raw32530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32530; decide +kernel
    rw [ha]
    exact (canonical32530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2377 + difference 2 0) (sourceB2377 + difference 0 2) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2377 + difference 2 0) (sourceB2377 + difference 0 2) sourceC2377) = raw32531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32531; decide +kernel
    rw [ha]
    exact (canonical32531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2377 + difference 3 0) (sourceB2377 + difference 0 3) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA2377 + difference 3 0) (sourceB2377 + difference 0 3) sourceC2377) = raw32532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32532; decide +kernel
    rw [ha]
    exact (canonical32532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2377 + difference 4 0) (sourceB2377 + difference 0 4) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA2377 + difference 4 0) (sourceB2377 + difference 0 4) sourceC2377) = raw32533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32533; decide +kernel
    rw [ha]
    exact (canonical32533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2377 + difference 5 0) (sourceB2377 + difference 0 5) sourceC2377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2046) := by
    have ha : (tripleCharges (sourceA2377 + difference 5 0) (sourceB2377 + difference 0 5) sourceC2377) = raw32534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2377 sourceB2377 sourceC2377 difference raw32534; decide +kernel
    rw [ha]
    exact (canonical32534 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2377 + sourceB2377) sourceC2377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2377 + sourceB2377) sourceC2377) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2377 sourceB2377 sourceC2377 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2377 sourceB2377 sourceC2377
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2377, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2378 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2378 + difference 0 1) (sourceB2378 + difference 1 0) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2378 + difference 0 1) (sourceB2378 + difference 1 0) sourceC2378) = raw32535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32535; decide +kernel
    rw [ha]
    exact (canonical32535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2378 + difference 1 1) (sourceB2378 + difference 1 1) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA2378 + difference 1 1) (sourceB2378 + difference 1 1) sourceC2378) = raw32536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32536; decide +kernel
    rw [ha]
    exact (canonical32536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2378 + difference 2 1) (sourceB2378 + difference 1 2) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2810) := by
    have ha : (tripleCharges (sourceA2378 + difference 2 1) (sourceB2378 + difference 1 2) sourceC2378) = raw32537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32537; decide +kernel
    rw [ha]
    exact (canonical32537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2378 + difference 3 1) (sourceB2378 + difference 1 3) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2378 + difference 3 1) (sourceB2378 + difference 1 3) sourceC2378) = raw32538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32538; decide +kernel
    rw [ha]
    exact (canonical32538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2378 + difference 4 1) (sourceB2378 + difference 1 4) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2378 + difference 4 1) (sourceB2378 + difference 1 4) sourceC2378) = raw32539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32539; decide +kernel
    rw [ha]
    exact (canonical32539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2378 + difference 5 1) (sourceB2378 + difference 1 5) sourceC2378) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2378 + difference 5 1) (sourceB2378 + difference 1 5) sourceC2378) = raw32540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2378 sourceB2378 sourceC2378 difference raw32540; decide +kernel
    rw [ha]
    exact (canonical32540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2378 + sourceB2378) sourceC2378) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2378 + sourceB2378) sourceC2378) = raw32541 := by
      apply Matrix.ext; unfold doubleCharges sourceA2378 sourceB2378 sourceC2378 raw32541; decide +kernel
    rw [ha]
    exact (canonical32541 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2378 sourceB2378 sourceC2378
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2378, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1920 : Integer.Sparse.reindex keyMap MixedData.row1920 = numericRow1920 := by decide +kernel

theorem numericCheck1920 (x : Master → ℝ) : Integer.Sparse.eval numericRow1920 x =
    (1 : ℝ) * reducedSource1920 x := by
  norm_num [numericRow1920, reducedSource1920, Integer.Sparse.eval, Sparse.eval, nodeValue2895, nodeValue2896, nodeValue2898, nodeValue2928, nodeValue3964, nodeValue4091]

theorem reindexCheck1921 : Integer.Sparse.reindex keyMap MixedData.row1921 = numericRow1921 := by decide +kernel

theorem numericCheck1921 (x : Master → ℝ) : Integer.Sparse.eval numericRow1921 x =
    (1 : ℝ) * reducedSource1921 x := by
  norm_num [numericRow1921, reducedSource1921, Integer.Sparse.eval, Sparse.eval, nodeValue1158, nodeValue2354, nodeValue2556, nodeValue2567, nodeValue2589, nodeValue4091]

theorem reindexCheck1922 : Integer.Sparse.reindex keyMap MixedData.row1922 = numericRow1922 := by decide +kernel

theorem numericCheck1922 (x : Master → ℝ) : Integer.Sparse.eval numericRow1922 x =
    (1 : ℝ) * reducedSource1922 x := by
  norm_num [numericRow1922, reducedSource1922, Integer.Sparse.eval, Sparse.eval, nodeValue2847, nodeValue2893, nodeValue2898, nodeValue2925, nodeValue3945, nodeValue4091]

theorem reindexCheck1923 : Integer.Sparse.reindex keyMap MixedData.row1923 = numericRow1923 := by decide +kernel

theorem numericCheck1923 (x : Master → ℝ) : Integer.Sparse.eval numericRow1923 x =
    (1 : ℝ) * reducedSource1923 x := by
  norm_num [numericRow1923, reducedSource1923, Integer.Sparse.eval, Sparse.eval, nodeValue2922, nodeValue3748, nodeValue3751, nodeValue3758, nodeValue3866, nodeValue3973, nodeValue4087]

theorem reindexCheck1926 : Integer.Sparse.reindex keyMap MixedData.row1926 = numericRow1926 := by decide +kernel

theorem numericCheck1926 (x : Master → ℝ) : Integer.Sparse.eval numericRow1926 x =
    (1 : ℝ) * reducedSource1926 x := by
  norm_num [numericRow1926, reducedSource1926, Integer.Sparse.eval, Sparse.eval, nodeValue1667, nodeValue1668, nodeValue1670, nodeValue1678, nodeValue1713, nodeValue3406, nodeValue3407, nodeValue3408, nodeValue3414, nodeValue3455, nodeValue3481, nodeValue3516, nodeValue3517, nodeValue3519, nodeValue3539, nodeValue3557, nodeValue3558, nodeValue3562, nodeValue3571, nodeValue3597, nodeValue3599, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3797, nodeValue3798, nodeValue3816, nodeValue3843, nodeValue3974]

theorem reindexCheck1927 : Integer.Sparse.reindex keyMap MixedData.row1927 = numericRow1927 := by decide +kernel

theorem numericCheck1927 (x : Master → ℝ) : Integer.Sparse.eval numericRow1927 x =
    (1 : ℝ) * reducedSource1927 x := by
  norm_num [numericRow1927, reducedSource1927, Integer.Sparse.eval, Sparse.eval, nodeValue2422, nodeValue2822, nodeValue2824, nodeValue2826, nodeValue2924, nodeValue3779, nodeValue4091]

theorem reindexCheck1928 : Integer.Sparse.reindex keyMap MixedData.row1928 = numericRow1928 := by decide +kernel

theorem numericCheck1928 (x : Master → ℝ) : Integer.Sparse.eval numericRow1928 x =
    (1 : ℝ) * reducedSource1928 x := by
  norm_num [numericRow1928, reducedSource1928, Integer.Sparse.eval, Sparse.eval, nodeValue1169, nodeValue2361, nodeValue2573, nodeValue2589, nodeValue4091]

theorem reindexCheck1929 : Integer.Sparse.reindex keyMap MixedData.row1929 = numericRow1929 := by decide +kernel

theorem numericCheck1929 (x : Master → ℝ) : Integer.Sparse.eval numericRow1929 x =
    (1 : ℝ) * reducedSource1929 x := by
  norm_num [numericRow1929, reducedSource1929, Integer.Sparse.eval, Sparse.eval, nodeValue1964, nodeValue2892, nodeValue2923, nodeValue3496, nodeValue4083]

theorem reindexCheck1930 : Integer.Sparse.reindex keyMap MixedData.row1930 = numericRow1930 := by decide +kernel

theorem numericCheck1930 (x : Master → ℝ) : Integer.Sparse.eval numericRow1930 x =
    (1 : ℝ) * reducedSource1930 x := by
  norm_num [numericRow1930, reducedSource1930, Integer.Sparse.eval, Sparse.eval, nodeValue2800, nodeValue2801, nodeValue2814, nodeValue2864, nodeValue3692, nodeValue4091]

theorem reindexCheck1931 : Integer.Sparse.reindex keyMap MixedData.row1931 = numericRow1931 := by decide +kernel

theorem numericCheck1931 (x : Master → ℝ) : Integer.Sparse.eval numericRow1931 x =
    (1 : ℝ) * reducedSource1931 x := by
  norm_num [numericRow1931, reducedSource1931, Integer.Sparse.eval, Sparse.eval, nodeValue2797, nodeValue2799, nodeValue2801, nodeValue2809, nodeValue2862, nodeValue3690, nodeValue4091]

theorem reindexCheck1932 : Integer.Sparse.reindex keyMap MixedData.row1932 = numericRow1932 := by decide +kernel

theorem numericCheck1932 (x : Master → ℝ) : Integer.Sparse.eval numericRow1932 x =
    (1 : ℝ) * reducedSource1932 x := by
  norm_num [numericRow1932, reducedSource1932, Integer.Sparse.eval, Sparse.eval, nodeValue2524, nodeValue2798, nodeValue2807, nodeValue2861, nodeValue3689, nodeValue4092]

theorem reindexCheck1933 : Integer.Sparse.reindex keyMap MixedData.row1933 = numericRow1933 := by decide +kernel

theorem numericCheck1933 (x : Master → ℝ) : Integer.Sparse.eval numericRow1933 x =
    (1 : ℝ) * reducedSource1933 x := by
  norm_num [numericRow1933, reducedSource1933, Integer.Sparse.eval, Sparse.eval, nodeValue2031, nodeValue2036, nodeValue2046, nodeValue2275, nodeValue3537, nodeValue4080]

theorem reindexCheck1934 : Integer.Sparse.reindex keyMap MixedData.row1934 = numericRow1934 := by decide +kernel

theorem numericCheck1934 (x : Master → ℝ) : Integer.Sparse.eval numericRow1934 x =
    (1 : ℝ) * reducedSource1934 x := by
  norm_num [numericRow1934, reducedSource1934, Integer.Sparse.eval, Sparse.eval, nodeValue2810, nodeValue2816, nodeValue2817, nodeValue2819, nodeValue2885, nodeValue3706, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1920 (mixedVector B) = 0 := by
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2898 : mixedVector B (Sum.inr 2898) = Sparse.eval nodeValue2898 (mixedVector B) := by
    change mixedMoment B node2898 node2898Labels = _
    exact sound2898 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2356, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2895, h2896, h2898, h2928, h3964, h4091, reducedSource1920] using sourceEq2356 B hB

theorem rowSound1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1920 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1920, numericCheck1920, reducedZero1920 B hB hF, mul_zero]

theorem reducedZero1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1921 (mixedVector B) = 0 := by
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h2354 : mixedVector B (Sum.inr 2354) = Sparse.eval nodeValue2354 (mixedVector B) := by
    change mixedMoment B node2354 node2354Labels = _
    exact sound2354 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2357, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1158, h2354, h2556, h2567, h2589, h4091, reducedSource1921] using sourceEq2357 B hB

theorem rowSound1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1921 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1921, numericCheck1921, reducedZero1921 B hB hF, mul_zero]

theorem reducedZero1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1922 (mixedVector B) = 0 := by
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2898 : mixedVector B (Sum.inr 2898) = Sparse.eval nodeValue2898 (mixedVector B) := by
    change mixedMoment B node2898 node2898Labels = _
    exact sound2898 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h3945 : mixedVector B (Sum.inr 3945) = Sparse.eval nodeValue3945 (mixedVector B) := by
    change mixedMoment B node3945 node3945Labels = _
    exact sound3945 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2358, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2847, h2893, h2898, h2925, h3945, h4091, reducedSource1922] using sourceEq2358 B hB

theorem rowSound1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1922 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1922, numericCheck1922, reducedZero1922 B hB hF, mul_zero]

theorem reducedZero1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1923 (mixedVector B) = 0 := by
  have h2922 : mixedVector B (Sum.inr 2922) = Sparse.eval nodeValue2922 (mixedVector B) := by
    change mixedMoment B node2922 node2922Labels = _
    exact sound2922 B hB hF
  have h3748 : mixedVector B (Sum.inr 3748) = Sparse.eval nodeValue3748 (mixedVector B) := by
    change mixedMoment B node3748 node3748Labels = _
    exact sound3748 B hB hF
  have h3751 : mixedVector B (Sum.inr 3751) = Sparse.eval nodeValue3751 (mixedVector B) := by
    change mixedMoment B node3751 node3751Labels = _
    exact sound3751 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3973 : mixedVector B (Sum.inr 3973) = Sparse.eval nodeValue3973 (mixedVector B) := by
    change mixedMoment B node3973 node3973Labels = _
    exact sound3973 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm2359, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2922, h3748, h3751, h3758, h3866, h3973, h4087, reducedSource1923] using sourceEq2359 B hB

theorem rowSound1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1923 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1923, numericCheck1923, reducedZero1923 B hB hF, mul_zero]

theorem reducedZero1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1926 (mixedVector B) = 0 := by
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3597 : mixedVector B (Sum.inr 3597) = Sparse.eval nodeValue3597 (mixedVector B) := by
    change mixedMoment B node3597 node3597Labels = _
    exact sound3597 B hB hF
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
  have h3797 : mixedVector B (Sum.inr 3797) = Sparse.eval nodeValue3797 (mixedVector B) := by
    change mixedMoment B node3797 node3797Labels = _
    exact sound3797 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  simpa only [sourceForm2367, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1667, h1668, h1670, h1678, h1713, h3406, h3407, h3408, h3414, h3455, h3481, h3516, h3517, h3519, h3539, h3557, h3558, h3562, h3571, h3597, h3599, h3605, h3606, h3612, h3625, h3797, h3798, h3816, h3843, h3974, reducedSource1926] using sourceEq2367 B hB

theorem rowSound1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1926 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1926, numericCheck1926, reducedZero1926 B hB hF, mul_zero]

theorem reducedZero1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1927 (mixedVector B) = 0 := by
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h2826 : mixedVector B (Sum.inr 2826) = Sparse.eval nodeValue2826 (mixedVector B) := by
    change mixedMoment B node2826 node2826Labels = _
    exact sound2826 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2368, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2422, h2822, h2824, h2826, h2924, h3779, h4091, reducedSource1927] using sourceEq2368 B hB

theorem rowSound1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1927 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1927, numericCheck1927, reducedZero1927 B hB hF, mul_zero]

theorem reducedZero1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1928 (mixedVector B) = 0 := by
  have h1169 : mixedVector B (Sum.inr 1169) = Sparse.eval nodeValue1169 (mixedVector B) := by
    change mixedMoment B node1169 node1169Labels = _
    exact sound1169 B hB hF
  have h2361 : mixedVector B (Sum.inr 2361) = Sparse.eval nodeValue2361 (mixedVector B) := by
    change mixedMoment B node2361 node2361Labels = _
    exact sound2361 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2370, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1169, h2361, h2573, h2589, h4091, reducedSource1928] using sourceEq2370 B hB

theorem rowSound1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1928 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1928, numericCheck1928, reducedZero1928 B hB hF, mul_zero]

theorem reducedZero1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1929 (mixedVector B) = 0 := by
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h2892 : mixedVector B (Sum.inr 2892) = Sparse.eval nodeValue2892 (mixedVector B) := by
    change mixedMoment B node2892 node2892Labels = _
    exact sound2892 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3496 : mixedVector B (Sum.inr 3496) = Sparse.eval nodeValue3496 (mixedVector B) := by
    change mixedMoment B node3496 node3496Labels = _
    exact sound3496 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2371, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1964, h2892, h2923, h3496, h4083, reducedSource1929] using sourceEq2371 B hB

theorem rowSound1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1929 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1929, numericCheck1929, reducedZero1929 B hB hF, mul_zero]

theorem reducedZero1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1930 (mixedVector B) = 0 := by
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2814 : mixedVector B (Sum.inr 2814) = Sparse.eval nodeValue2814 (mixedVector B) := by
    change mixedMoment B node2814 node2814Labels = _
    exact sound2814 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2374, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2800, h2801, h2814, h2864, h3692, h4091, reducedSource1930] using sourceEq2374 B hB

theorem rowSound1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1930 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1930, numericCheck1930, reducedZero1930 B hB hF, mul_zero]

theorem reducedZero1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1931 (mixedVector B) = 0 := by
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2799 : mixedVector B (Sum.inr 2799) = Sparse.eval nodeValue2799 (mixedVector B) := by
    change mixedMoment B node2799 node2799Labels = _
    exact sound2799 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2809 : mixedVector B (Sum.inr 2809) = Sparse.eval nodeValue2809 (mixedVector B) := by
    change mixedMoment B node2809 node2809Labels = _
    exact sound2809 B hB hF
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2375, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2797, h2799, h2801, h2809, h2862, h3690, h4091, reducedSource1931] using sourceEq2375 B hB

theorem rowSound1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1931 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1931, numericCheck1931, reducedZero1931 B hB hF, mul_zero]

theorem reducedZero1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1932 (mixedVector B) = 0 := by
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h2807 : mixedVector B (Sum.inr 2807) = Sparse.eval nodeValue2807 (mixedVector B) := by
    change mixedMoment B node2807 node2807Labels = _
    exact sound2807 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2376, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2524, h2798, h2807, h2861, h3689, h4092, reducedSource1932] using sourceEq2376 B hB

theorem rowSound1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1932 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1932, numericCheck1932, reducedZero1932 B hB hF, mul_zero]

theorem reducedZero1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1933 (mixedVector B) = 0 := by
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2036 : mixedVector B (Sum.inr 2036) = Sparse.eval nodeValue2036 (mixedVector B) := by
    change mixedMoment B node2036 node2036Labels = _
    exact sound2036 B hB hF
  have h2046 : mixedVector B (Sum.inr 2046) = Sparse.eval nodeValue2046 (mixedVector B) := by
    change mixedMoment B node2046 node2046Labels = _
    exact sound2046 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2377, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2031, h2036, h2046, h2275, h3537, h4080, reducedSource1933] using sourceEq2377 B hB

theorem rowSound1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1933 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1933, numericCheck1933, reducedZero1933 B hB hF, mul_zero]

theorem reducedZero1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1934 (mixedVector B) = 0 := by
  have h2810 : mixedVector B (Sum.inr 2810) = Sparse.eval nodeValue2810 (mixedVector B) := by
    change mixedMoment B node2810 node2810Labels = _
    exact sound2810 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2378, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2810, h2816, h2817, h2819, h2885, h3706, h4092, reducedSource1934] using sourceEq2378 B hB

theorem rowSound1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1934 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1934, numericCheck1934, reducedZero1934 B hB hF, mul_zero]

theorem sourceRowsAt1920 : MixedData.sourceRows (1920 : Fin 2425) =
    MixedData.row1920 := by decide +kernel

theorem sourceRowsAt1921 : MixedData.sourceRows (1921 : Fin 2425) =
    MixedData.row1921 := by decide +kernel

theorem sourceRowsAt1922 : MixedData.sourceRows (1922 : Fin 2425) =
    MixedData.row1922 := by decide +kernel

theorem sourceRowsAt1923 : MixedData.sourceRows (1923 : Fin 2425) =
    MixedData.row1923 := by decide +kernel

theorem sourceRowsAt1924 : MixedData.sourceRows (1924 : Fin 2425) =
    MixedData.row1924 := by decide +kernel

theorem sourceRowsAt1925 : MixedData.sourceRows (1925 : Fin 2425) =
    MixedData.row1925 := by decide +kernel

theorem sourceRowsAt1926 : MixedData.sourceRows (1926 : Fin 2425) =
    MixedData.row1926 := by decide +kernel

theorem sourceRowsAt1927 : MixedData.sourceRows (1927 : Fin 2425) =
    MixedData.row1927 := by decide +kernel

theorem sourceRowsAt1928 : MixedData.sourceRows (1928 : Fin 2425) =
    MixedData.row1928 := by decide +kernel

theorem sourceRowsAt1929 : MixedData.sourceRows (1929 : Fin 2425) =
    MixedData.row1929 := by decide +kernel

theorem sourceRowsAt1930 : MixedData.sourceRows (1930 : Fin 2425) =
    MixedData.row1930 := by decide +kernel

theorem sourceRowsAt1931 : MixedData.sourceRows (1931 : Fin 2425) =
    MixedData.row1931 := by decide +kernel

theorem sourceRowsAt1932 : MixedData.sourceRows (1932 : Fin 2425) =
    MixedData.row1932 := by decide +kernel

theorem sourceRowsAt1933 : MixedData.sourceRows (1933 : Fin 2425) =
    MixedData.row1933 := by decide +kernel

theorem sourceRowsAt1934 : MixedData.sourceRows (1934 : Fin 2425) =
    MixedData.row1934 := by decide +kernel

theorem sourceRowsAt1935 : MixedData.sourceRows (1935 : Fin 2425) =
    MixedData.row1935 := by decide +kernel

theorem chunkSound120_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 120) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1920 ∨ k.val = 1921 ∨ k.val = 1922 ∨ k.val = 1923 ∨ k.val = 1924 ∨ k.val = 1925 ∨ k.val = 1926 ∨ k.val = 1927 ∨ k.val = 1928 ∨ k.val = 1929 ∨ k.val = 1930 ∨ k.val = 1931 ∨ k.val = 1932 ∨ k.val = 1933 ∨ k.val = 1934 ∨ k.val = 1935 := by omega
  rcases heq with h1920 | h1921 | h1922 | h1923 | h1924 | h1925 | h1926 | h1927 | h1928 | h1929 | h1930 | h1931 | h1932 | h1933 | h1934 | h1935
  · have he : k = (1920 : Fin 2425) := Fin.ext h1920
    subst k
    rw [sourceRowsAt1920]
    exact rowSound1920 B hB hF
  · have he : k = (1921 : Fin 2425) := Fin.ext h1921
    subst k
    rw [sourceRowsAt1921]
    exact rowSound1921 B hB hF
  · have he : k = (1922 : Fin 2425) := Fin.ext h1922
    subst k
    rw [sourceRowsAt1922]
    exact rowSound1922 B hB hF
  · have he : k = (1923 : Fin 2425) := Fin.ext h1923
    subst k
    rw [sourceRowsAt1923]
    exact rowSound1923 B hB hF
  · have he : k = (1924 : Fin 2425) := Fin.ext h1924
    subst k
    rw [sourceRowsAt1924]
    exact rowSound1924_e B hB hF
  · have he : k = (1925 : Fin 2425) := Fin.ext h1925
    subst k
    rw [sourceRowsAt1925]
    exact rowSound1925_e B hB hF
  · have he : k = (1926 : Fin 2425) := Fin.ext h1926
    subst k
    rw [sourceRowsAt1926]
    exact rowSound1926 B hB hF
  · have he : k = (1927 : Fin 2425) := Fin.ext h1927
    subst k
    rw [sourceRowsAt1927]
    exact rowSound1927 B hB hF
  · have he : k = (1928 : Fin 2425) := Fin.ext h1928
    subst k
    rw [sourceRowsAt1928]
    exact rowSound1928 B hB hF
  · have he : k = (1929 : Fin 2425) := Fin.ext h1929
    subst k
    rw [sourceRowsAt1929]
    exact rowSound1929 B hB hF
  · have he : k = (1930 : Fin 2425) := Fin.ext h1930
    subst k
    rw [sourceRowsAt1930]
    exact rowSound1930 B hB hF
  · have he : k = (1931 : Fin 2425) := Fin.ext h1931
    subst k
    rw [sourceRowsAt1931]
    exact rowSound1931 B hB hF
  · have he : k = (1932 : Fin 2425) := Fin.ext h1932
    subst k
    rw [sourceRowsAt1932]
    exact rowSound1932 B hB hF
  · have he : k = (1933 : Fin 2425) := Fin.ext h1933
    subst k
    rw [sourceRowsAt1933]
    exact rowSound1933 B hB hF
  · have he : k = (1934 : Fin 2425) := Fin.ext h1934
    subst k
    rw [sourceRowsAt1934]
    exact rowSound1934 B hB hF
  · have he : k = (1935 : Fin 2425) := Fin.ext h1935
    subst k
    rw [sourceRowsAt1935]
    exact rowSound1935_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e_oai
