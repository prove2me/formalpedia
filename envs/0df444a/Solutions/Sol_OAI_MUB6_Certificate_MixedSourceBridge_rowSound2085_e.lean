-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:02:30.831303+00:00
-- url     : https://prove2.me/submissions/7dc1f9cb-ec9c-4d70-a026-5fef66aa2f0f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16796 raw16796Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw16796 raw16796Labels = mixedMoment B raw16796step0 raw16796step0Labels := by
      have ha : raw16796step0 = (fun i j => raw16796 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16796step0 raw16796; decide +kernel
      have hl : raw16796step0Labels = raw16796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16796 raw16796Labels permutation277 permutation7
    mixedMoment B raw16796step0 raw16796step0Labels = mixedMoment B raw16796step1 raw16796step1Labels := by
      have ha : raw16796step1 = -raw16796step0 := by apply Matrix.ext; change ∀ i j, raw16796step1 i j = -(raw16796step0 i j); unfold raw16796step1 raw16796step0; decide +kernel
      have hl : raw16796step1Labels = raw16796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16796step1 raw16796step1Labels = mixedMoment B raw16796step2 raw16796step2Labels := by
      have ha : raw16796step2 = raw16796step1 := by apply Matrix.ext; unfold raw16796step2 raw16796step1; decide +kernel
      have hl : raw16796step1Labels = labelEmbedding1 ∘ raw16796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16796step1 raw16796step1Labels raw16796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical16807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16807 raw16807Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw16807 raw16807Labels = mixedMoment B raw16807step0 raw16807step0Labels := by
      have ha : raw16807step0 = (fun i j => raw16807 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16807step0 raw16807; decide +kernel
      have hl : raw16807step0Labels = raw16807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16807 raw16807Labels permutation279 permutation7
    mixedMoment B raw16807step0 raw16807step0Labels = mixedMoment B raw16807step1 raw16807step1Labels := by
      have ha : raw16807step1 = -raw16807step0 := by apply Matrix.ext; change ∀ i j, raw16807step1 i j = -(raw16807step0 i j); unfold raw16807step1 raw16807step0; decide +kernel
      have hl : raw16807step1Labels = raw16807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16807step1 raw16807step1Labels = mixedMoment B raw16807step2 raw16807step2Labels := by
      have ha : raw16807step2 = raw16807step1 := by apply Matrix.ext; unfold raw16807step2 raw16807step1; decide +kernel
      have hl : raw16807step1Labels = labelEmbedding1 ∘ raw16807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16807step1 raw16807step1Labels raw16807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical16811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16811 raw16811Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw16811 raw16811Labels = mixedMoment B raw16811step0 raw16811step0Labels := by
      have ha : raw16811step0 = (fun i j => raw16811 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16811step0 raw16811; decide +kernel
      have hl : raw16811step0Labels = raw16811Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16811 raw16811Labels permutation182 permutation5
    mixedMoment B raw16811step0 raw16811step0Labels = mixedMoment B raw16811step1 raw16811step1Labels := by
      have ha : raw16811step1 = -raw16811step0 := by apply Matrix.ext; change ∀ i j, raw16811step1 i j = -(raw16811step0 i j); unfold raw16811step1 raw16811step0; decide +kernel
      have hl : raw16811step1Labels = raw16811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16811step1 raw16811step1Labels = mixedMoment B raw16811step2 raw16811step2Labels := by
      have ha : raw16811step2 = raw16811step1 := by apply Matrix.ext; unfold raw16811step2 raw16811step1; decide +kernel
      have hl : raw16811step1Labels = labelEmbedding1 ∘ raw16811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16811step1 raw16811step1Labels raw16811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical16813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16813 raw16813Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw16813 raw16813Labels = mixedMoment B raw16813step0 raw16813step0Labels := by
      have ha : raw16813step0 = (fun i j => raw16813 (permutation352 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16813step0 raw16813; decide +kernel
      have hl : raw16813step0Labels = raw16813Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16813 raw16813Labels permutation352 permutation5
    mixedMoment B raw16813step0 raw16813step0Labels = mixedMoment B raw16813step1 raw16813step1Labels := by
      have ha : raw16813step1 = -raw16813step0 := by apply Matrix.ext; change ∀ i j, raw16813step1 i j = -(raw16813step0 i j); unfold raw16813step1 raw16813step0; decide +kernel
      have hl : raw16813step1Labels = raw16813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16813step1 raw16813step1Labels = mixedMoment B raw16813step2 raw16813step2Labels := by
      have ha : raw16813step2 = raw16813step1 := by apply Matrix.ext; unfold raw16813step2 raw16813step1; decide +kernel
      have hl : raw16813step1Labels = labelEmbedding1 ∘ raw16813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16813step1 raw16813step1Labels raw16813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

theorem canonical16814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16814 raw16814Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16814 raw16814Labels = mixedMoment B raw16814step0 raw16814step0Labels := by
      have hz : ∀ j, raw16814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16814step0 = (fun i j => raw16814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16814step0 raw16814; decide +kernel
      have hl : raw16814step0Labels = raw16814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16814 raw16814Labels permutation520 hz
    mixedMoment B raw16814step0 raw16814step0Labels = mixedMoment B raw16814step1 raw16814step1Labels := by
      have ha : raw16814step1 = (fun i j => raw16814step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16814step1 raw16814step0; decide +kernel
      have hl : raw16814step1Labels = raw16814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16814step0 raw16814step0Labels permutation56 permutation7
    mixedMoment B raw16814step1 raw16814step1Labels = mixedMoment B raw16814step2 raw16814step2Labels := by
      have ha : raw16814step2 = -raw16814step1 := by apply Matrix.ext; change ∀ i j, raw16814step2 i j = -(raw16814step1 i j); unfold raw16814step2 raw16814step1; decide +kernel
      have hl : raw16814step2Labels = raw16814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16814step2 raw16814step2Labels = mixedMoment B raw16814step3 raw16814step3Labels := by
      have ha : raw16814step3 = raw16814step2 := by apply Matrix.ext; unfold raw16814step3 raw16814step2; decide +kernel
      have hl : raw16814step2Labels = labelEmbedding1 ∘ raw16814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16814step2 raw16814step2Labels raw16814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical16815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16815 raw16815Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw16815 raw16815Labels = mixedMoment B raw16815step0 raw16815step0Labels := by
      have ha : raw16815step0 = (fun i j => raw16815 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16815step0 raw16815; decide +kernel
      have hl : raw16815step0Labels = raw16815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16815 raw16815Labels permutation277 permutation7
    mixedMoment B raw16815step0 raw16815step0Labels = mixedMoment B raw16815step1 raw16815step1Labels := by
      have ha : raw16815step1 = -raw16815step0 := by apply Matrix.ext; change ∀ i j, raw16815step1 i j = -(raw16815step0 i j); unfold raw16815step1 raw16815step0; decide +kernel
      have hl : raw16815step1Labels = raw16815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16815step1 raw16815step1Labels = mixedMoment B raw16815step2 raw16815step2Labels := by
      have ha : raw16815step2 = raw16815step1 := by apply Matrix.ext; unfold raw16815step2 raw16815step1; decide +kernel
      have hl : raw16815step1Labels = labelEmbedding1 ∘ raw16815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16815step1 raw16815step1Labels raw16815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical16817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16817 raw16817Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw16817 raw16817Labels = mixedMoment B raw16817step0 raw16817step0Labels := by
      have ha : raw16817step0 = (fun i j => raw16817 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16817step0 raw16817; decide +kernel
      have hl : raw16817step0Labels = raw16817Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16817 raw16817Labels permutation577 permutation5
    mixedMoment B raw16817step0 raw16817step0Labels = mixedMoment B raw16817step1 raw16817step1Labels := by
      have ha : raw16817step1 = raw16817step0 := by apply Matrix.ext; unfold raw16817step1 raw16817step0; decide +kernel
      have hl : raw16817step0Labels = labelEmbedding1 ∘ raw16817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16817step0 raw16817step0Labels raw16817step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

theorem canonical16822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16822 raw16822Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw16822 raw16822Labels = mixedMoment B raw16822step0 raw16822step0Labels := by
      have ha : raw16822step0 = (fun i j => raw16822 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16822step0 raw16822; decide +kernel
      have hl : raw16822step0Labels = raw16822Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16822 raw16822Labels permutation674 permutation5
    mixedMoment B raw16822step0 raw16822step0Labels = mixedMoment B raw16822step1 raw16822step1Labels := by
      have ha : raw16822step1 = raw16822step0 := by apply Matrix.ext; unfold raw16822step1 raw16822step0; decide +kernel
      have hl : raw16822step0Labels = labelEmbedding1 ∘ raw16822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16822step0 raw16822step0Labels raw16822step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical284
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36463 raw36463Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw36463 raw36463Labels = mixedMoment B raw36463step0 raw36463step0Labels := by
      have ha : raw36463step0 = (fun i j => raw36463 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36463step0 raw36463; decide +kernel
      have hl : raw36463step0Labels = raw36463Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36463 raw36463Labels permutation277 permutation7
    mixedMoment B raw36463step0 raw36463step0Labels = mixedMoment B raw36463step1 raw36463step1Labels := by
      have ha : raw36463step1 = -raw36463step0 := by apply Matrix.ext; change ∀ i j, raw36463step1 i j = -(raw36463step0 i j); unfold raw36463step1 raw36463step0; decide +kernel
      have hl : raw36463step1Labels = raw36463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36463step1 raw36463step1Labels = mixedMoment B raw36463step2 raw36463step2Labels := by
      have ha : raw36463step2 = raw36463step1 := by apply Matrix.ext; unfold raw36463step2 raw36463step1; decide +kernel
      have hl : raw36463step1Labels = labelEmbedding1 ∘ raw36463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36463step1 raw36463step1Labels raw36463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical36464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36464 raw36464Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw36464 raw36464Labels = mixedMoment B raw36464step0 raw36464step0Labels := by
      have ha : raw36464step0 = (fun i j => raw36464 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36464step0 raw36464; decide +kernel
      have hl : raw36464step0Labels = raw36464Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36464 raw36464Labels permutation277 permutation7
    mixedMoment B raw36464step0 raw36464step0Labels = mixedMoment B raw36464step1 raw36464step1Labels := by
      have ha : raw36464step1 = -raw36464step0 := by apply Matrix.ext; change ∀ i j, raw36464step1 i j = -(raw36464step0 i j); unfold raw36464step1 raw36464step0; decide +kernel
      have hl : raw36464step1Labels = raw36464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36464step1 raw36464step1Labels = mixedMoment B raw36464step2 raw36464step2Labels := by
      have ha : raw36464step2 = raw36464step1 := by apply Matrix.ext; unfold raw36464step2 raw36464step1; decide +kernel
      have hl : raw36464step1Labels = labelEmbedding1 ∘ raw36464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36464step1 raw36464step1Labels raw36464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical36465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36465 raw36465Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36465 raw36465Labels = mixedMoment B raw36465step0 raw36465step0Labels := by
      have hz : ∀ j, raw36465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36465step0 = (fun i j => raw36465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36465step0 raw36465; decide +kernel
      have hl : raw36465step0Labels = raw36465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36465 raw36465Labels permutation520 hz
    mixedMoment B raw36465step0 raw36465step0Labels = mixedMoment B raw36465step1 raw36465step1Labels := by
      have ha : raw36465step1 = (fun i j => raw36465step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36465step1 raw36465step0; decide +kernel
      have hl : raw36465step1Labels = raw36465step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36465step0 raw36465step0Labels permutation56 permutation7
    mixedMoment B raw36465step1 raw36465step1Labels = mixedMoment B raw36465step2 raw36465step2Labels := by
      have ha : raw36465step2 = -raw36465step1 := by apply Matrix.ext; change ∀ i j, raw36465step2 i j = -(raw36465step1 i j); unfold raw36465step2 raw36465step1; decide +kernel
      have hl : raw36465step2Labels = raw36465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36465step2 raw36465step2Labels = mixedMoment B raw36465step3 raw36465step3Labels := by
      have ha : raw36465step3 = raw36465step2 := by apply Matrix.ext; unfold raw36465step3 raw36465step2; decide +kernel
      have hl : raw36465step2Labels = labelEmbedding1 ∘ raw36465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36465step2 raw36465step2Labels raw36465step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical36466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36466 raw36466Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw36466 raw36466Labels = mixedMoment B raw36466step0 raw36466step0Labels := by
      have ha : raw36466step0 = (fun i j => raw36466 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36466step0 raw36466; decide +kernel
      have hl : raw36466step0Labels = raw36466Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36466 raw36466Labels permutation277 permutation7
    mixedMoment B raw36466step0 raw36466step0Labels = mixedMoment B raw36466step1 raw36466step1Labels := by
      have ha : raw36466step1 = -raw36466step0 := by apply Matrix.ext; change ∀ i j, raw36466step1 i j = -(raw36466step0 i j); unfold raw36466step1 raw36466step0; decide +kernel
      have hl : raw36466step1Labels = raw36466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36466step1 raw36466step1Labels = mixedMoment B raw36466step2 raw36466step2Labels := by
      have ha : raw36466step2 = raw36466step1 := by apply Matrix.ext; unfold raw36466step2 raw36466step1; decide +kernel
      have hl : raw36466step1Labels = labelEmbedding1 ∘ raw36466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36466step1 raw36466step1Labels raw36466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical36467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36467 raw36467Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw36467 raw36467Labels = mixedMoment B raw36467step0 raw36467step0Labels := by
      have ha : raw36467step0 = (fun i j => raw36467 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36467step0 raw36467; decide +kernel
      have hl : raw36467step0Labels = raw36467Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36467 raw36467Labels permutation277 permutation7
    mixedMoment B raw36467step0 raw36467step0Labels = mixedMoment B raw36467step1 raw36467step1Labels := by
      have ha : raw36467step1 = -raw36467step0 := by apply Matrix.ext; change ∀ i j, raw36467step1 i j = -(raw36467step0 i j); unfold raw36467step1 raw36467step0; decide +kernel
      have hl : raw36467step1Labels = raw36467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36467step1 raw36467step1Labels = mixedMoment B raw36467step2 raw36467step2Labels := by
      have ha : raw36467step2 = raw36467step1 := by apply Matrix.ext; unfold raw36467step2 raw36467step1; decide +kernel
      have hl : raw36467step1Labels = labelEmbedding1 ∘ raw36467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36467step1 raw36467step1Labels raw36467step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical36468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36468 raw36468Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw36468 raw36468Labels = mixedMoment B raw36468step0 raw36468step0Labels := by
      have ha : raw36468step0 = (fun i j => raw36468 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36468step0 raw36468; decide +kernel
      have hl : raw36468step0Labels = raw36468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36468 raw36468Labels permutation152 permutation5
    mixedMoment B raw36468step0 raw36468step0Labels = mixedMoment B raw36468step1 raw36468step1Labels := by
      have ha : raw36468step1 = -raw36468step0 := by apply Matrix.ext; change ∀ i j, raw36468step1 i j = -(raw36468step0 i j); unfold raw36468step1 raw36468step0; decide +kernel
      have hl : raw36468step1Labels = raw36468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36468step1 raw36468step1Labels = mixedMoment B raw36468step2 raw36468step2Labels := by
      have ha : raw36468step2 = raw36468step1 := by apply Matrix.ext; unfold raw36468step2 raw36468step1; decide +kernel
      have hl : raw36468step1Labels = labelEmbedding1 ∘ raw36468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36468step1 raw36468step1Labels raw36468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

theorem canonical36469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36469 raw36469Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw36469 raw36469Labels = mixedMoment B raw36469step0 raw36469step0Labels := by
      have ha : raw36469step0 = (fun i j => raw36469 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36469step0 raw36469; decide +kernel
      have hl : raw36469step0Labels = raw36469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36469 raw36469Labels permutation277 permutation7
    mixedMoment B raw36469step0 raw36469step0Labels = mixedMoment B raw36469step1 raw36469step1Labels := by
      have ha : raw36469step1 = -raw36469step0 := by apply Matrix.ext; change ∀ i j, raw36469step1 i j = -(raw36469step0 i j); unfold raw36469step1 raw36469step0; decide +kernel
      have hl : raw36469step1Labels = raw36469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36469step1 raw36469step1Labels = mixedMoment B raw36469step2 raw36469step2Labels := by
      have ha : raw36469step2 = raw36469step1 := by apply Matrix.ext; unfold raw36469step2 raw36469step1; decide +kernel
      have hl : raw36469step1Labels = labelEmbedding1 ∘ raw36469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36469step1 raw36469step1Labels raw36469step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

theorem canonical36470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36470 raw36470Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw36470 raw36470Labels = mixedMoment B raw36470step0 raw36470step0Labels := by
      have hz : ∀ j, raw36470 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36470step0 = (fun i j => raw36470 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36470step0 raw36470; decide +kernel
      have hl : raw36470step0Labels = raw36470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36470 raw36470Labels permutation520 hz
    mixedMoment B raw36470step0 raw36470step0Labels = mixedMoment B raw36470step1 raw36470step1Labels := by
      have ha : raw36470step1 = (fun i j => raw36470step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36470step1 raw36470step0; decide +kernel
      have hl : raw36470step1Labels = raw36470step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36470step0 raw36470step0Labels permutation56 permutation7
    mixedMoment B raw36470step1 raw36470step1Labels = mixedMoment B raw36470step2 raw36470step2Labels := by
      have ha : raw36470step2 = -raw36470step1 := by apply Matrix.ext; change ∀ i j, raw36470step2 i j = -(raw36470step1 i j); unfold raw36470step2 raw36470step1; decide +kernel
      have hl : raw36470step2Labels = raw36470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36470step2 raw36470step2Labels = mixedMoment B raw36470step3 raw36470step3Labels := by
      have ha : raw36470step3 = raw36470step2 := by apply Matrix.ext; unfold raw36470step3 raw36470step2; decide +kernel
      have hl : raw36470step2Labels = labelEmbedding1 ∘ raw36470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36470step2 raw36470step2Labels raw36470step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

theorem canonical36471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36471 raw36471Labels = mixedMoment B node3765 node3765Labels := by
  calc
    mixedMoment B raw36471 raw36471Labels = mixedMoment B raw36471step0 raw36471step0Labels := by
      have ha : raw36471step0 = (fun i j => raw36471 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36471step0 raw36471; decide +kernel
      have hl : raw36471step0Labels = raw36471Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36471 raw36471Labels permutation277 permutation7
    mixedMoment B raw36471step0 raw36471step0Labels = mixedMoment B raw36471step1 raw36471step1Labels := by
      have ha : raw36471step1 = -raw36471step0 := by apply Matrix.ext; change ∀ i j, raw36471step1 i j = -(raw36471step0 i j); unfold raw36471step1 raw36471step0; decide +kernel
      have hl : raw36471step1Labels = raw36471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36471step1 raw36471step1Labels = mixedMoment B raw36471step2 raw36471step2Labels := by
      have ha : raw36471step2 = raw36471step1 := by apply Matrix.ext; unfold raw36471step2 raw36471step1; decide +kernel
      have hl : raw36471step1Labels = labelEmbedding1 ∘ raw36471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36471step1 raw36471step1Labels raw36471step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3765 node3765Labels := by rfl

theorem canonical36472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36472 raw36472Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw36472 raw36472Labels = mixedMoment B raw36472step0 raw36472step0Labels := by
      have ha : raw36472step0 = (fun i j => raw36472 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36472step0 raw36472; decide +kernel
      have hl : raw36472step0Labels = raw36472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36472 raw36472Labels permutation178 permutation5
    mixedMoment B raw36472step0 raw36472step0Labels = mixedMoment B raw36472step1 raw36472step1Labels := by
      have ha : raw36472step1 = -raw36472step0 := by apply Matrix.ext; change ∀ i j, raw36472step1 i j = -(raw36472step0 i j); unfold raw36472step1 raw36472step0; decide +kernel
      have hl : raw36472step1Labels = raw36472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36472step1 raw36472step1Labels = mixedMoment B raw36472step2 raw36472step2Labels := by
      have ha : raw36472step2 = raw36472step1 := by apply Matrix.ext; unfold raw36472step2 raw36472step1; decide +kernel
      have hl : raw36472step1Labels = labelEmbedding1 ∘ raw36472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36472step1 raw36472step1Labels raw36472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical36473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36473 raw36473Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw36473 raw36473Labels = mixedMoment B raw36473step0 raw36473step0Labels := by
      have ha : raw36473step0 = (fun i j => raw36473 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36473step0 raw36473; decide +kernel
      have hl : raw36473step0Labels = raw36473Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36473 raw36473Labels permutation277 permutation7
    mixedMoment B raw36473step0 raw36473step0Labels = mixedMoment B raw36473step1 raw36473step1Labels := by
      have ha : raw36473step1 = -raw36473step0 := by apply Matrix.ext; change ∀ i j, raw36473step1 i j = -(raw36473step0 i j); unfold raw36473step1 raw36473step0; decide +kernel
      have hl : raw36473step1Labels = raw36473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36473step1 raw36473step1Labels = mixedMoment B raw36473step2 raw36473step2Labels := by
      have ha : raw36473step2 = raw36473step1 := by apply Matrix.ext; unfold raw36473step2 raw36473step1; decide +kernel
      have hl : raw36473step1Labels = labelEmbedding1 ∘ raw36473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36473step1 raw36473step1Labels raw36473step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

theorem canonical36474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36474 raw36474Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw36474 raw36474Labels = mixedMoment B raw36474step0 raw36474step0Labels := by
      have ha : raw36474step0 = (fun i j => raw36474 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36474step0 raw36474; decide +kernel
      have hl : raw36474step0Labels = raw36474Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36474 raw36474Labels permutation277 permutation7
    mixedMoment B raw36474step0 raw36474step0Labels = mixedMoment B raw36474step1 raw36474step1Labels := by
      have ha : raw36474step1 = -raw36474step0 := by apply Matrix.ext; change ∀ i j, raw36474step1 i j = -(raw36474step0 i j); unfold raw36474step1 raw36474step0; decide +kernel
      have hl : raw36474step1Labels = raw36474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36474step1 raw36474step1Labels = mixedMoment B raw36474step2 raw36474step2Labels := by
      have ha : raw36474step2 = raw36474step1 := by apply Matrix.ext; unfold raw36474step2 raw36474step1; decide +kernel
      have hl : raw36474step1Labels = labelEmbedding1 ∘ raw36474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36474step1 raw36474step1Labels raw36474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

theorem canonical36475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36475 raw36475Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36475 raw36475Labels = mixedMoment B raw36475step0 raw36475step0Labels := by
      have hz : ∀ j, raw36475 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36475step0 = (fun i j => raw36475 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36475step0 raw36475; decide +kernel
      have hl : raw36475step0Labels = raw36475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36475 raw36475Labels permutation520 hz
    mixedMoment B raw36475step0 raw36475step0Labels = mixedMoment B raw36475step1 raw36475step1Labels := by
      have ha : raw36475step1 = (fun i j => raw36475step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36475step1 raw36475step0; decide +kernel
      have hl : raw36475step1Labels = raw36475step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36475step0 raw36475step0Labels permutation56 permutation7
    mixedMoment B raw36475step1 raw36475step1Labels = mixedMoment B raw36475step2 raw36475step2Labels := by
      have ha : raw36475step2 = -raw36475step1 := by apply Matrix.ext; change ∀ i j, raw36475step2 i j = -(raw36475step1 i j); unfold raw36475step2 raw36475step1; decide +kernel
      have hl : raw36475step2Labels = raw36475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36475step2 raw36475step2Labels = mixedMoment B raw36475step3 raw36475step3Labels := by
      have ha : raw36475step3 = raw36475step2 := by apply Matrix.ext; unfold raw36475step3 raw36475step2; decide +kernel
      have hl : raw36475step2Labels = labelEmbedding1 ∘ raw36475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36475step2 raw36475step2Labels raw36475step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical36476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36476 raw36476Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw36476 raw36476Labels = mixedMoment B raw36476step0 raw36476step0Labels := by
      have ha : raw36476step0 = (fun i j => raw36476 (permutation278 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36476step0 raw36476; decide +kernel
      have hl : raw36476step0Labels = raw36476Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36476 raw36476Labels permutation278 permutation7
    mixedMoment B raw36476step0 raw36476step0Labels = mixedMoment B raw36476step1 raw36476step1Labels := by
      have ha : raw36476step1 = -raw36476step0 := by apply Matrix.ext; change ∀ i j, raw36476step1 i j = -(raw36476step0 i j); unfold raw36476step1 raw36476step0; decide +kernel
      have hl : raw36476step1Labels = raw36476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36476step1 raw36476step1Labels = mixedMoment B raw36476step2 raw36476step2Labels := by
      have ha : raw36476step2 = raw36476step1 := by apply Matrix.ext; unfold raw36476step2 raw36476step1; decide +kernel
      have hl : raw36476step1Labels = labelEmbedding1 ∘ raw36476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36476step1 raw36476step1Labels raw36476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical36477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36477 raw36477Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36477 raw36477Labels = mixedMoment B raw36477step0 raw36477step0Labels := by
      have ha : raw36477step0 = (fun i j => raw36477 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36477step0 raw36477; decide +kernel
      have hl : raw36477step0Labels = raw36477Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36477 raw36477Labels permutation177 permutation5
    mixedMoment B raw36477step0 raw36477step0Labels = mixedMoment B raw36477step1 raw36477step1Labels := by
      have ha : raw36477step1 = -raw36477step0 := by apply Matrix.ext; change ∀ i j, raw36477step1 i j = -(raw36477step0 i j); unfold raw36477step1 raw36477step0; decide +kernel
      have hl : raw36477step1Labels = raw36477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36477step1 raw36477step1Labels = mixedMoment B raw36477step2 raw36477step2Labels := by
      have ha : raw36477step2 = raw36477step1 := by apply Matrix.ext; unfold raw36477step2 raw36477step1; decide +kernel
      have hl : raw36477step1Labels = labelEmbedding1 ∘ raw36477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36477step1 raw36477step1Labels raw36477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical36478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36478 raw36478Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36478 raw36478Labels = mixedMoment B raw36478step0 raw36478step0Labels := by
      have ha : raw36478step0 = (fun i j => raw36478 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36478step0 raw36478; decide +kernel
      have hl : raw36478step0Labels = raw36478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36478 raw36478Labels permutation277 permutation7
    mixedMoment B raw36478step0 raw36478step0Labels = mixedMoment B raw36478step1 raw36478step1Labels := by
      have ha : raw36478step1 = -raw36478step0 := by apply Matrix.ext; change ∀ i j, raw36478step1 i j = -(raw36478step0 i j); unfold raw36478step1 raw36478step0; decide +kernel
      have hl : raw36478step1Labels = raw36478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36478step1 raw36478step1Labels = mixedMoment B raw36478step2 raw36478step2Labels := by
      have ha : raw36478step2 = raw36478step1 := by apply Matrix.ext; unfold raw36478step2 raw36478step1; decide +kernel
      have hl : raw36478step1Labels = labelEmbedding1 ∘ raw36478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36478step1 raw36478step1Labels raw36478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

theorem canonical36479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36479 raw36479Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36479 raw36479Labels = mixedMoment B raw36479step0 raw36479step0Labels := by
      have ha : raw36479step0 = (fun i j => raw36479 (permutation586 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36479step0 raw36479; decide +kernel
      have hl : raw36479step0Labels = raw36479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36479 raw36479Labels permutation586 permutation5
    mixedMoment B raw36479step0 raw36479step0Labels = mixedMoment B raw36479step1 raw36479step1Labels := by
      have ha : raw36479step1 = raw36479step0 := by apply Matrix.ext; unfold raw36479step1 raw36479step0; decide +kernel
      have hl : raw36479step0Labels = labelEmbedding1 ∘ raw36479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36479step0 raw36479step0Labels raw36479step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36480 raw36480Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36480 raw36480Labels = mixedMoment B raw36480step0 raw36480step0Labels := by
      have ha : raw36480step0 = (fun i j => raw36480 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36480step0 raw36480; decide +kernel
      have hl : raw36480step0Labels = raw36480Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36480 raw36480Labels permutation277 permutation7
    mixedMoment B raw36480step0 raw36480step0Labels = mixedMoment B raw36480step1 raw36480step1Labels := by
      have ha : raw36480step1 = -raw36480step0 := by apply Matrix.ext; change ∀ i j, raw36480step1 i j = -(raw36480step0 i j); unfold raw36480step1 raw36480step0; decide +kernel
      have hl : raw36480step1Labels = raw36480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36480step1 raw36480step1Labels = mixedMoment B raw36480step2 raw36480step2Labels := by
      have ha : raw36480step2 = raw36480step1 := by apply Matrix.ext; unfold raw36480step2 raw36480step1; decide +kernel
      have hl : raw36480step1Labels = labelEmbedding1 ∘ raw36480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36480step1 raw36480step1Labels raw36480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical36481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36481 raw36481Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw36481 raw36481Labels = mixedMoment B raw36481step0 raw36481step0Labels := by
      have ha : raw36481step0 = (fun i j => raw36481 (permutation686 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36481step0 raw36481; decide +kernel
      have hl : raw36481step0Labels = raw36481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36481 raw36481Labels permutation686 permutation5
    mixedMoment B raw36481step0 raw36481step0Labels = mixedMoment B raw36481step1 raw36481step1Labels := by
      have ha : raw36481step1 = raw36481step0 := by apply Matrix.ext; unfold raw36481step1 raw36481step0; decide +kernel
      have hl : raw36481step0Labels = labelEmbedding1 ∘ raw36481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36481step0 raw36481step0Labels raw36481step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

theorem canonical36482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36482 raw36482Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw36482 raw36482Labels = mixedMoment B raw36482step0 raw36482step0Labels := by
      have ha : raw36482step0 = (fun i j => raw36482 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36482step0 raw36482; decide +kernel
      have hl : raw36482step0Labels = raw36482Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36482 raw36482Labels permutation277 permutation7
    mixedMoment B raw36482step0 raw36482step0Labels = mixedMoment B raw36482step1 raw36482step1Labels := by
      have ha : raw36482step1 = -raw36482step0 := by apply Matrix.ext; change ∀ i j, raw36482step1 i j = -(raw36482step0 i j); unfold raw36482step1 raw36482step0; decide +kernel
      have hl : raw36482step1Labels = raw36482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36482step1 raw36482step1Labels = mixedMoment B raw36482step2 raw36482step2Labels := by
      have ha : raw36482step2 = raw36482step1 := by apply Matrix.ext; unfold raw36482step2 raw36482step1; decide +kernel
      have hl : raw36482step1Labels = labelEmbedding1 ∘ raw36482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36482step1 raw36482step1Labels raw36482step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

theorem canonical36483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36483 raw36483Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw36483 raw36483Labels = mixedMoment B raw36483step0 raw36483step0Labels := by
      have ha : raw36483step0 = (fun i j => raw36483 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36483step0 raw36483; decide +kernel
      have hl : raw36483step0Labels = raw36483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36483 raw36483Labels permutation685 permutation5
    mixedMoment B raw36483step0 raw36483step0Labels = mixedMoment B raw36483step1 raw36483step1Labels := by
      have ha : raw36483step1 = raw36483step0 := by apply Matrix.ext; unfold raw36483step1 raw36483step0; decide +kernel
      have hl : raw36483step0Labels = labelEmbedding1 ∘ raw36483step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36483step0 raw36483step0Labels raw36483step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

theorem canonical36484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36484 raw36484Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw36484 raw36484Labels = mixedMoment B raw36484step0 raw36484step0Labels := by
      have hz : ∀ j, raw36484 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36484step0 = (fun i j => raw36484 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36484step0 raw36484; decide +kernel
      have hl : raw36484step0Labels = raw36484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36484 raw36484Labels permutation520 hz
    mixedMoment B raw36484step0 raw36484step0Labels = mixedMoment B raw36484step1 raw36484step1Labels := by
      have ha : raw36484step1 = (fun i j => raw36484step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36484step1 raw36484step0; decide +kernel
      have hl : raw36484step1Labels = raw36484step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36484step0 raw36484step0Labels permutation149 permutation5
    mixedMoment B raw36484step1 raw36484step1Labels = mixedMoment B raw36484step2 raw36484step2Labels := by
      have ha : raw36484step2 = raw36484step1 := by apply Matrix.ext; unfold raw36484step2 raw36484step1; decide +kernel
      have hl : raw36484step1Labels = labelEmbedding1 ∘ raw36484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36484step1 raw36484step1Labels raw36484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = 0 := by
  exact mixedMoment_alpha B hF node3409 node3409Labels 1 permutation487
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

theorem sound3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3408 node3408Labels = Sparse.eval nodeValue3408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3408) = mixedMoment B node3408 node3408Labels := rfl
  simpa [nodeValue3408, Sparse.eval] using hc.symm

theorem sound3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3409 node3409Labels = Sparse.eval nodeValue3409 (mixedVector B) := by
  simpa only [nodeValue3409, Sparse.eval_nil] using zero3409 B _hB _hF

theorem sound3410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3410 node3410Labels = Sparse.eval nodeValue3410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3410) = mixedMoment B node3410 node3410Labels := rfl
  simpa [nodeValue3410, Sparse.eval] using hc.symm

theorem sound3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3414 node3414Labels = Sparse.eval nodeValue3414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3414) = mixedMoment B node3414 node3414Labels := rfl
  simpa [nodeValue3414, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3511 node3511Labels = Sparse.eval nodeValue3511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3511) = mixedMoment B node3511 node3511Labels := rfl
  simpa [nodeValue3511, Sparse.eval] using hc.symm

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

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

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

theorem sound3587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3587 node3587Labels = Sparse.eval nodeValue3587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3587) = mixedMoment B node3587 node3587Labels := rfl
  simpa [nodeValue3587, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

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

theorem zero3765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3765 node3765Labels = 0 := by
  exact mixedMoment_order_one B hB node3765 node3765Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3755 node3755Labels = Sparse.eval nodeValue3755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3755) = mixedMoment B node3755 node3755Labels := rfl
  simpa [nodeValue3755, Sparse.eval] using hc.symm

theorem sound3763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3763 node3763Labels = Sparse.eval nodeValue3763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3763) = mixedMoment B node3763 node3763Labels := rfl
  simpa [nodeValue3763, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3765 node3765Labels = Sparse.eval nodeValue3765 (mixedVector B) := by
  simpa only [nodeValue3765, Sparse.eval_nil] using zero3765 B _hB _hF

theorem sound3768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3768 node3768Labels = Sparse.eval nodeValue3768 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3768) = mixedMoment B node3768 node3768Labels := rfl
  simpa [nodeValue3768, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = 0 := by
  exact mixedMoment_alpha B hF node3956 node3956Labels 1 permutation203
    (by decide +kernel)

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

theorem sound3955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3955 node3955Labels = Sparse.eval nodeValue3955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3955) = mixedMoment B node3955 node3955Labels := rfl
  simpa [nodeValue3955, Sparse.eval] using hc.symm

theorem sound3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = Sparse.eval nodeValue3956 (mixedVector B) := by
  simpa only [nodeValue3956, Sparse.eval_nil] using zero3956 B _hB _hF

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2615 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 1) (sourceB2615 + difference 1 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 1) (sourceB2615 + difference 1 0) sourceC2615) = raw36463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36463; decide +kernel
    rw [ha]
    exact (canonical36463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 2) (sourceB2615 + difference 2 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 2) (sourceB2615 + difference 2 0) sourceC2615) = raw36464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36464; decide +kernel
    rw [ha]
    exact (canonical36464 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 3) (sourceB2615 + difference 3 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 3) (sourceB2615 + difference 3 0) sourceC2615) = raw16796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16796; decide +kernel
    rw [ha]
    exact (canonical16796 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 4) (sourceB2615 + difference 4 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 4) (sourceB2615 + difference 4 0) sourceC2615) = raw36465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36465; decide +kernel
    rw [ha]
    exact (canonical36465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 5) (sourceB2615 + difference 5 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 5) (sourceB2615 + difference 5 0) sourceC2615) = raw36466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36466; decide +kernel
    rw [ha]
    exact (canonical36466 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 0) (sourceB2615 + difference 0 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 0) (sourceB2615 + difference 0 1) sourceC2615) = raw16811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16811; decide +kernel
    rw [ha]
    exact (canonical16811 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 2) (sourceB2615 + difference 2 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 2) (sourceB2615 + difference 2 1) sourceC2615) = raw16813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16813; decide +kernel
    rw [ha]
    exact (canonical16813 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 3) (sourceB2615 + difference 3 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 3) (sourceB2615 + difference 3 1) sourceC2615) = raw36467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36467; decide +kernel
    rw [ha]
    exact (canonical36467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 4) (sourceB2615 + difference 4 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 4) (sourceB2615 + difference 4 1) sourceC2615) = raw16814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16814; decide +kernel
    rw [ha]
    exact (canonical16814 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 5) (sourceB2615 + difference 5 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 5) (sourceB2615 + difference 5 1) sourceC2615) = raw16815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16815; decide +kernel
    rw [ha]
    exact (canonical16815 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 0) (sourceB2615 + difference 0 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3587) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 0) (sourceB2615 + difference 0 2) sourceC2615) = raw36468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36468; decide +kernel
    rw [ha]
    exact (canonical36468 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 1) (sourceB2615 + difference 1 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3410) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 1) (sourceB2615 + difference 1 2) sourceC2615) = raw36469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36469; decide +kernel
    rw [ha]
    exact (canonical36469 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 3) (sourceB2615 + difference 3 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 3) (sourceB2615 + difference 3 2) sourceC2615) = raw16807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16807; decide +kernel
    rw [ha]
    exact (canonical16807 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 4) (sourceB2615 + difference 4 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 4) (sourceB2615 + difference 4 2) sourceC2615) = raw36470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36470; decide +kernel
    rw [ha]
    exact (canonical36470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 5) (sourceB2615 + difference 5 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3765) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 5) (sourceB2615 + difference 5 2) sourceC2615) = raw36471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36471; decide +kernel
    rw [ha]
    exact (canonical36471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 0) (sourceB2615 + difference 0 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 0) (sourceB2615 + difference 0 3) sourceC2615) = raw36472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36472; decide +kernel
    rw [ha]
    exact (canonical36472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 1) (sourceB2615 + difference 1 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 1) (sourceB2615 + difference 1 3) sourceC2615) = raw36473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36473; decide +kernel
    rw [ha]
    exact (canonical36473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 2) (sourceB2615 + difference 2 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 2) (sourceB2615 + difference 2 3) sourceC2615) = raw36474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36474; decide +kernel
    rw [ha]
    exact (canonical36474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 4) (sourceB2615 + difference 4 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 4) (sourceB2615 + difference 4 3) sourceC2615) = raw36475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36475; decide +kernel
    rw [ha]
    exact (canonical36475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 5) (sourceB2615 + difference 5 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 5) (sourceB2615 + difference 5 3) sourceC2615) = raw36476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36476; decide +kernel
    rw [ha]
    exact (canonical36476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 0) (sourceB2615 + difference 0 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 0) (sourceB2615 + difference 0 4) sourceC2615) = raw36477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36477; decide +kernel
    rw [ha]
    exact (canonical36477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 1) (sourceB2615 + difference 1 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 1) (sourceB2615 + difference 1 4) sourceC2615) = raw36478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36478; decide +kernel
    rw [ha]
    exact (canonical36478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 2) (sourceB2615 + difference 2 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 2) (sourceB2615 + difference 2 4) sourceC2615) = raw36479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36479; decide +kernel
    rw [ha]
    exact (canonical36479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 3) (sourceB2615 + difference 3 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 3) (sourceB2615 + difference 3 4) sourceC2615) = raw16817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16817; decide +kernel
    rw [ha]
    exact (canonical16817 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 5) (sourceB2615 + difference 5 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 5) (sourceB2615 + difference 5 4) sourceC2615) = raw36480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36480; decide +kernel
    rw [ha]
    exact (canonical36480 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 0) (sourceB2615 + difference 0 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 0) (sourceB2615 + difference 0 5) sourceC2615) = raw36481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36481; decide +kernel
    rw [ha]
    exact (canonical36481 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 1) (sourceB2615 + difference 1 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 1) (sourceB2615 + difference 1 5) sourceC2615) = raw36482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36482; decide +kernel
    rw [ha]
    exact (canonical36482 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 2) (sourceB2615 + difference 2 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 2) (sourceB2615 + difference 2 5) sourceC2615) = raw36483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36483; decide +kernel
    rw [ha]
    exact (canonical36483 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 3) (sourceB2615 + difference 3 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 3) (sourceB2615 + difference 3 5) sourceC2615) = raw16822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16822; decide +kernel
    rw [ha]
    exact (canonical16822 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 4) (sourceB2615 + difference 4 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 4) (sourceB2615 + difference 4 5) sourceC2615) = raw36484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36484; decide +kernel
    rw [ha]
    exact (canonical36484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2615 sourceB2615 sourceC2615
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2615, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2085 : Integer.Sparse.reindex keyMap MixedData.row2085 = numericRow2085 := by decide +kernel

theorem numericCheck2085 (x : Master → ℝ) : Integer.Sparse.eval numericRow2085 x =
    (1 : ℝ) * reducedSource2085 x := by
  norm_num [numericRow2085, reducedSource2085, Integer.Sparse.eval, Sparse.eval, nodeValue3408, nodeValue3409, nodeValue3410, nodeValue3414, nodeValue3452, nodeValue3454, nodeValue3467, nodeValue3476, nodeValue3508, nodeValue3511, nodeValue3529, nodeValue3587, nodeValue3612, nodeValue3755, nodeValue3763, nodeValue3764, nodeValue3765, nodeValue3768, nodeValue3769, nodeValue3773, nodeValue3774, nodeValue3804, nodeValue3805, nodeValue3806, nodeValue3816, nodeValue3955, nodeValue3956, nodeValue3957, nodeValue3961]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2085 (mixedVector B) = 0 := by
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3409 : mixedVector B (Sum.inr 3409) = Sparse.eval nodeValue3409 (mixedVector B) := by
    change mixedMoment B node3409 node3409Labels = _
    exact sound3409 B hB hF
  have h3410 : mixedVector B (Sum.inr 3410) = Sparse.eval nodeValue3410 (mixedVector B) := by
    change mixedMoment B node3410 node3410Labels = _
    exact sound3410 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3587 : mixedVector B (Sum.inr 3587) = Sparse.eval nodeValue3587 (mixedVector B) := by
    change mixedMoment B node3587 node3587Labels = _
    exact sound3587 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3755 : mixedVector B (Sum.inr 3755) = Sparse.eval nodeValue3755 (mixedVector B) := by
    change mixedMoment B node3755 node3755Labels = _
    exact sound3755 B hB hF
  have h3763 : mixedVector B (Sum.inr 3763) = Sparse.eval nodeValue3763 (mixedVector B) := by
    change mixedMoment B node3763 node3763Labels = _
    exact sound3763 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3765 : mixedVector B (Sum.inr 3765) = Sparse.eval nodeValue3765 (mixedVector B) := by
    change mixedMoment B node3765 node3765Labels = _
    exact sound3765 B hB hF
  have h3768 : mixedVector B (Sum.inr 3768) = Sparse.eval nodeValue3768 (mixedVector B) := by
    change mixedMoment B node3768 node3768Labels = _
    exact sound3768 B hB hF
  have h3769 : mixedVector B (Sum.inr 3769) = Sparse.eval nodeValue3769 (mixedVector B) := by
    change mixedMoment B node3769 node3769Labels = _
    exact sound3769 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3955 : mixedVector B (Sum.inr 3955) = Sparse.eval nodeValue3955 (mixedVector B) := by
    change mixedMoment B node3955 node3955Labels = _
    exact sound3955 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  simpa only [sourceForm2615, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3408, h3409, h3410, h3414, h3452, h3454, h3467, h3476, h3508, h3511, h3529, h3587, h3612, h3755, h3763, h3764, h3765, h3768, h3769, h3773, h3774, h3804, h3805, h3806, h3816, h3955, h3956, h3957, h3961, reducedSource2085] using sourceEq2615 B hB

theorem rowSound2085_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2085 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2085, numericCheck2085, reducedZero2085 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e_oai
