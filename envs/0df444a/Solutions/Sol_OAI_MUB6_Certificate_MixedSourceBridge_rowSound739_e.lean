-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:22:10.383559+00:00
-- url     : https://prove2.me/submissions/47448c7f-fa20-42f6-8710-0e5633789232

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3853_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14103 raw14103Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14103 raw14103Labels = mixedMoment B raw14103step0 raw14103step0Labels := by
      have ha : raw14103step0 = (fun i j => raw14103 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14103step0 raw14103; decide +kernel
      have hl : raw14103step0Labels = raw14103Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14103 raw14103Labels permutation181 permutation7
    mixedMoment B raw14103step0 raw14103step0Labels = mixedMoment B raw14103step1 raw14103step1Labels := by
      have ha : raw14103step1 = -raw14103step0 := by apply Matrix.ext; change ∀ i j, raw14103step1 i j = -(raw14103step0 i j); unfold raw14103step1 raw14103step0; decide +kernel
      have hl : raw14103step1Labels = raw14103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14103step1 raw14103step1Labels = mixedMoment B raw14103step2 raw14103step2Labels := by
      have ha : raw14103step2 = raw14103step1 := by apply Matrix.ext; unfold raw14103step2 raw14103step1; decide +kernel
      have hl : raw14103step1Labels = labelEmbedding1 ∘ raw14103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14103step1 raw14103step1Labels raw14103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical14104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14104 raw14104Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw14104 raw14104Labels = mixedMoment B raw14104step0 raw14104step0Labels := by
      have hz : ∀ j, raw14104 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14104step0 = (fun i j => raw14104 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14104step0 raw14104; decide +kernel
      have hl : raw14104step0Labels = raw14104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14104 raw14104Labels permutation265 hz
    mixedMoment B raw14104step0 raw14104step0Labels = mixedMoment B raw14104step1 raw14104step1Labels := by
      have ha : raw14104step1 = (fun i j => raw14104step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14104step1 raw14104step0; decide +kernel
      have hl : raw14104step1Labels = raw14104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14104step0 raw14104step0Labels permutation37 permutation7
    mixedMoment B raw14104step1 raw14104step1Labels = mixedMoment B raw14104step2 raw14104step2Labels := by
      have ha : raw14104step2 = -raw14104step1 := by apply Matrix.ext; change ∀ i j, raw14104step2 i j = -(raw14104step1 i j); unfold raw14104step2 raw14104step1; decide +kernel
      have hl : raw14104step2Labels = raw14104step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14104step2 raw14104step2Labels = mixedMoment B raw14104step3 raw14104step3Labels := by
      have ha : raw14104step3 = raw14104step2 := by apply Matrix.ext; unfold raw14104step3 raw14104step2; decide +kernel
      have hl : raw14104step2Labels = labelEmbedding1 ∘ raw14104step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14104step2 raw14104step2Labels raw14104step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical14105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14105 raw14105Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14105 raw14105Labels = mixedMoment B raw14105step0 raw14105step0Labels := by
      have hz : ∀ j, raw14105 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14105step0 = (fun i j => raw14105 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14105step0 raw14105; decide +kernel
      have hl : raw14105step0Labels = raw14105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14105 raw14105Labels permutation265 hz
    mixedMoment B raw14105step0 raw14105step0Labels = mixedMoment B raw14105step1 raw14105step1Labels := by
      have ha : raw14105step1 = (fun i j => raw14105step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14105step1 raw14105step0; decide +kernel
      have hl : raw14105step1Labels = raw14105step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14105step0 raw14105step0Labels permutation37 permutation7
    mixedMoment B raw14105step1 raw14105step1Labels = mixedMoment B raw14105step2 raw14105step2Labels := by
      have ha : raw14105step2 = -raw14105step1 := by apply Matrix.ext; change ∀ i j, raw14105step2 i j = -(raw14105step1 i j); unfold raw14105step2 raw14105step1; decide +kernel
      have hl : raw14105step2Labels = raw14105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14105step2 raw14105step2Labels = mixedMoment B raw14105step3 raw14105step3Labels := by
      have ha : raw14105step3 = raw14105step2 := by apply Matrix.ext; unfold raw14105step3 raw14105step2; decide +kernel
      have hl : raw14105step2Labels = labelEmbedding1 ∘ raw14105step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14105step2 raw14105step2Labels raw14105step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical14106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14106 raw14106Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw14106 raw14106Labels = mixedMoment B raw14106step0 raw14106step0Labels := by
      have hz : ∀ j, raw14106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14106step0 = (fun i j => raw14106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14106step0 raw14106; decide +kernel
      have hl : raw14106step0Labels = raw14106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14106 raw14106Labels permutation265 hz
    mixedMoment B raw14106step0 raw14106step0Labels = mixedMoment B raw14106step1 raw14106step1Labels := by
      have ha : raw14106step1 = (fun i j => raw14106step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14106step1 raw14106step0; decide +kernel
      have hl : raw14106step1Labels = raw14106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14106step0 raw14106step0Labels permutation37 permutation7
    mixedMoment B raw14106step1 raw14106step1Labels = mixedMoment B raw14106step2 raw14106step2Labels := by
      have ha : raw14106step2 = -raw14106step1 := by apply Matrix.ext; change ∀ i j, raw14106step2 i j = -(raw14106step1 i j); unfold raw14106step2 raw14106step1; decide +kernel
      have hl : raw14106step2Labels = raw14106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14106step2 raw14106step2Labels = mixedMoment B raw14106step3 raw14106step3Labels := by
      have ha : raw14106step3 = raw14106step2 := by apply Matrix.ext; unfold raw14106step3 raw14106step2; decide +kernel
      have hl : raw14106step2Labels = labelEmbedding1 ∘ raw14106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14106step2 raw14106step2Labels raw14106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical14107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14107 raw14107Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw14107 raw14107Labels = mixedMoment B raw14107step0 raw14107step0Labels := by
      have hz : ∀ j, raw14107 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14107step0 = (fun i j => raw14107 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14107step0 raw14107; decide +kernel
      have hl : raw14107step0Labels = raw14107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14107 raw14107Labels permutation590 hz
    mixedMoment B raw14107step0 raw14107step0Labels = mixedMoment B raw14107step1 raw14107step1Labels := by
      have hz : ∀ j, raw14107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14107step1 = (fun i j => raw14107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14107step1 raw14107step0; decide +kernel
      have hl : raw14107step1Labels = raw14107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14107step0 raw14107step0Labels permutation56 hz
    mixedMoment B raw14107step1 raw14107step1Labels = mixedMoment B raw14107step2 raw14107step2Labels := by
      have ha : raw14107step2 = (fun i j => raw14107step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14107step2 raw14107step1; decide +kernel
      have hl : raw14107step2Labels = raw14107step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14107step1 raw14107step1Labels permutation9 permutation7
    mixedMoment B raw14107step2 raw14107step2Labels = mixedMoment B raw14107step3 raw14107step3Labels := by
      have ha : raw14107step3 = -raw14107step2 := by apply Matrix.ext; change ∀ i j, raw14107step3 i j = -(raw14107step2 i j); unfold raw14107step3 raw14107step2; decide +kernel
      have hl : raw14107step3Labels = raw14107step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14107step3 raw14107step3Labels = mixedMoment B raw14107step4 raw14107step4Labels := by
      have ha : raw14107step4 = raw14107step3 := by apply Matrix.ext; unfold raw14107step4 raw14107step3; decide +kernel
      have hl : raw14107step3Labels = labelEmbedding1 ∘ raw14107step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14107step3 raw14107step3Labels raw14107step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

theorem canonical14108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14108 raw14108Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw14108 raw14108Labels = mixedMoment B raw14108step0 raw14108step0Labels := by
      have ha : raw14108step0 = (fun i j => raw14108 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14108step0 raw14108; decide +kernel
      have hl : raw14108step0Labels = raw14108Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14108 raw14108Labels permutation181 permutation7
    mixedMoment B raw14108step0 raw14108step0Labels = mixedMoment B raw14108step1 raw14108step1Labels := by
      have ha : raw14108step1 = -raw14108step0 := by apply Matrix.ext; change ∀ i j, raw14108step1 i j = -(raw14108step0 i j); unfold raw14108step1 raw14108step0; decide +kernel
      have hl : raw14108step1Labels = raw14108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14108step1 raw14108step1Labels = mixedMoment B raw14108step2 raw14108step2Labels := by
      have ha : raw14108step2 = raw14108step1 := by apply Matrix.ext; unfold raw14108step2 raw14108step1; decide +kernel
      have hl : raw14108step1Labels = labelEmbedding1 ∘ raw14108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14108step1 raw14108step1Labels raw14108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical14109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14109 raw14109Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw14109 raw14109Labels = mixedMoment B raw14109step0 raw14109step0Labels := by
      have ha : raw14109step0 = (fun i j => raw14109 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14109step0 raw14109; decide +kernel
      have hl : raw14109step0Labels = raw14109Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14109 raw14109Labels permutation181 permutation7
    mixedMoment B raw14109step0 raw14109step0Labels = mixedMoment B raw14109step1 raw14109step1Labels := by
      have ha : raw14109step1 = -raw14109step0 := by apply Matrix.ext; change ∀ i j, raw14109step1 i j = -(raw14109step0 i j); unfold raw14109step1 raw14109step0; decide +kernel
      have hl : raw14109step1Labels = raw14109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14109step1 raw14109step1Labels = mixedMoment B raw14109step2 raw14109step2Labels := by
      have ha : raw14109step2 = raw14109step1 := by apply Matrix.ext; unfold raw14109step2 raw14109step1; decide +kernel
      have hl : raw14109step1Labels = labelEmbedding1 ∘ raw14109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14109step1 raw14109step1Labels raw14109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical14110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14110 raw14110Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw14110 raw14110Labels = mixedMoment B raw14110step0 raw14110step0Labels := by
      have ha : raw14110step0 = (fun i j => raw14110 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14110step0 raw14110; decide +kernel
      have hl : raw14110step0Labels = raw14110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14110 raw14110Labels permutation181 permutation7
    mixedMoment B raw14110step0 raw14110step0Labels = mixedMoment B raw14110step1 raw14110step1Labels := by
      have ha : raw14110step1 = -raw14110step0 := by apply Matrix.ext; change ∀ i j, raw14110step1 i j = -(raw14110step0 i j); unfold raw14110step1 raw14110step0; decide +kernel
      have hl : raw14110step1Labels = raw14110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14110step1 raw14110step1Labels = mixedMoment B raw14110step2 raw14110step2Labels := by
      have ha : raw14110step2 = raw14110step1 := by apply Matrix.ext; unfold raw14110step2 raw14110step1; decide +kernel
      have hl : raw14110step1Labels = labelEmbedding1 ∘ raw14110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14110step1 raw14110step1Labels raw14110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical14111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14111 raw14111Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw14111 raw14111Labels = mixedMoment B raw14111step0 raw14111step0Labels := by
      have ha : raw14111step0 = (fun i j => raw14111 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14111step0 raw14111; decide +kernel
      have hl : raw14111step0Labels = raw14111Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14111 raw14111Labels permutation181 permutation7
    mixedMoment B raw14111step0 raw14111step0Labels = mixedMoment B raw14111step1 raw14111step1Labels := by
      have ha : raw14111step1 = -raw14111step0 := by apply Matrix.ext; change ∀ i j, raw14111step1 i j = -(raw14111step0 i j); unfold raw14111step1 raw14111step0; decide +kernel
      have hl : raw14111step1Labels = raw14111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14111step1 raw14111step1Labels = mixedMoment B raw14111step2 raw14111step2Labels := by
      have ha : raw14111step2 = raw14111step1 := by apply Matrix.ext; unfold raw14111step2 raw14111step1; decide +kernel
      have hl : raw14111step1Labels = labelEmbedding1 ∘ raw14111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14111step1 raw14111step1Labels raw14111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical14112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14112 raw14112Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw14112 raw14112Labels = mixedMoment B raw14112step0 raw14112step0Labels := by
      have hz : ∀ j, raw14112 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14112step0 = (fun i j => raw14112 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14112step0 raw14112; decide +kernel
      have hl : raw14112step0Labels = raw14112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14112 raw14112Labels permutation590 hz
    mixedMoment B raw14112step0 raw14112step0Labels = mixedMoment B raw14112step1 raw14112step1Labels := by
      have ha : raw14112step1 = (fun i j => raw14112step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14112step1 raw14112step0; decide +kernel
      have hl : raw14112step1Labels = raw14112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14112step0 raw14112step0Labels permutation39 permutation7
    mixedMoment B raw14112step1 raw14112step1Labels = mixedMoment B raw14112step2 raw14112step2Labels := by
      have ha : raw14112step2 = -raw14112step1 := by apply Matrix.ext; change ∀ i j, raw14112step2 i j = -(raw14112step1 i j); unfold raw14112step2 raw14112step1; decide +kernel
      have hl : raw14112step2Labels = raw14112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14112step2 raw14112step2Labels = mixedMoment B raw14112step3 raw14112step3Labels := by
      have ha : raw14112step3 = raw14112step2 := by apply Matrix.ext; unfold raw14112step3 raw14112step2; decide +kernel
      have hl : raw14112step2Labels = labelEmbedding1 ∘ raw14112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14112step2 raw14112step2Labels raw14112step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical14113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14113 raw14113Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw14113 raw14113Labels = mixedMoment B raw14113step0 raw14113step0Labels := by
      have hz : ∀ j, raw14113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14113step0 = (fun i j => raw14113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14113step0 raw14113; decide +kernel
      have hl : raw14113step0Labels = raw14113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14113 raw14113Labels permutation265 hz
    mixedMoment B raw14113step0 raw14113step0Labels = mixedMoment B raw14113step1 raw14113step1Labels := by
      have ha : raw14113step1 = (fun i j => raw14113step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14113step1 raw14113step0; decide +kernel
      have hl : raw14113step1Labels = raw14113step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14113step0 raw14113step0Labels permutation41 permutation5
    mixedMoment B raw14113step1 raw14113step1Labels = mixedMoment B raw14113step2 raw14113step2Labels := by
      have ha : raw14113step2 = -raw14113step1 := by apply Matrix.ext; change ∀ i j, raw14113step2 i j = -(raw14113step1 i j); unfold raw14113step2 raw14113step1; decide +kernel
      have hl : raw14113step2Labels = raw14113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14113step2 raw14113step2Labels = mixedMoment B raw14113step3 raw14113step3Labels := by
      have ha : raw14113step3 = raw14113step2 := by apply Matrix.ext; unfold raw14113step3 raw14113step2; decide +kernel
      have hl : raw14113step2Labels = labelEmbedding1 ∘ raw14113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14113step2 raw14113step2Labels raw14113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical14114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14114 raw14114Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw14114 raw14114Labels = mixedMoment B raw14114step0 raw14114step0Labels := by
      have ha : raw14114step0 = (fun i j => raw14114 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14114step0 raw14114; decide +kernel
      have hl : raw14114step0Labels = raw14114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14114 raw14114Labels permutation181 permutation7
    mixedMoment B raw14114step0 raw14114step0Labels = mixedMoment B raw14114step1 raw14114step1Labels := by
      have ha : raw14114step1 = -raw14114step0 := by apply Matrix.ext; change ∀ i j, raw14114step1 i j = -(raw14114step0 i j); unfold raw14114step1 raw14114step0; decide +kernel
      have hl : raw14114step1Labels = raw14114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14114step1 raw14114step1Labels = mixedMoment B raw14114step2 raw14114step2Labels := by
      have ha : raw14114step2 = raw14114step1 := by apply Matrix.ext; unfold raw14114step2 raw14114step1; decide +kernel
      have hl : raw14114step1Labels = labelEmbedding1 ∘ raw14114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14114step1 raw14114step1Labels raw14114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical14115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14115 raw14115Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw14115 raw14115Labels = mixedMoment B raw14115step0 raw14115step0Labels := by
      have hz : ∀ j, raw14115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14115step0 = (fun i j => raw14115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14115step0 raw14115; decide +kernel
      have hl : raw14115step0Labels = raw14115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14115 raw14115Labels permutation265 hz
    mixedMoment B raw14115step0 raw14115step0Labels = mixedMoment B raw14115step1 raw14115step1Labels := by
      have ha : raw14115step1 = (fun i j => raw14115step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14115step1 raw14115step0; decide +kernel
      have hl : raw14115step1Labels = raw14115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14115step0 raw14115step0Labels permutation37 permutation7
    mixedMoment B raw14115step1 raw14115step1Labels = mixedMoment B raw14115step2 raw14115step2Labels := by
      have ha : raw14115step2 = -raw14115step1 := by apply Matrix.ext; change ∀ i j, raw14115step2 i j = -(raw14115step1 i j); unfold raw14115step2 raw14115step1; decide +kernel
      have hl : raw14115step2Labels = raw14115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14115step2 raw14115step2Labels = mixedMoment B raw14115step3 raw14115step3Labels := by
      have ha : raw14115step3 = raw14115step2 := by apply Matrix.ext; unfold raw14115step3 raw14115step2; decide +kernel
      have hl : raw14115step2Labels = labelEmbedding1 ∘ raw14115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14115step2 raw14115step2Labels raw14115step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical14116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14116 raw14116Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw14116 raw14116Labels = mixedMoment B raw14116step0 raw14116step0Labels := by
      have hz : ∀ j, raw14116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14116step0 = (fun i j => raw14116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14116step0 raw14116; decide +kernel
      have hl : raw14116step0Labels = raw14116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14116 raw14116Labels permutation265 hz
    mixedMoment B raw14116step0 raw14116step0Labels = mixedMoment B raw14116step1 raw14116step1Labels := by
      have ha : raw14116step1 = (fun i j => raw14116step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14116step1 raw14116step0; decide +kernel
      have hl : raw14116step1Labels = raw14116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14116step0 raw14116step0Labels permutation37 permutation7
    mixedMoment B raw14116step1 raw14116step1Labels = mixedMoment B raw14116step2 raw14116step2Labels := by
      have ha : raw14116step2 = -raw14116step1 := by apply Matrix.ext; change ∀ i j, raw14116step2 i j = -(raw14116step1 i j); unfold raw14116step2 raw14116step1; decide +kernel
      have hl : raw14116step2Labels = raw14116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14116step2 raw14116step2Labels = mixedMoment B raw14116step3 raw14116step3Labels := by
      have ha : raw14116step3 = raw14116step2 := by apply Matrix.ext; unfold raw14116step3 raw14116step2; decide +kernel
      have hl : raw14116step2Labels = labelEmbedding1 ∘ raw14116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14116step2 raw14116step2Labels raw14116step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical14117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14117 raw14117Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw14117 raw14117Labels = mixedMoment B raw14117step0 raw14117step0Labels := by
      have hz : ∀ j, raw14117 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14117step0 = (fun i j => raw14117 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14117step0 raw14117; decide +kernel
      have hl : raw14117step0Labels = raw14117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14117 raw14117Labels permutation590 hz
    mixedMoment B raw14117step0 raw14117step0Labels = mixedMoment B raw14117step1 raw14117step1Labels := by
      have hz : ∀ j, raw14117step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14117step1 = (fun i j => raw14117step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14117step1 raw14117step0; decide +kernel
      have hl : raw14117step1Labels = raw14117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14117step0 raw14117step0Labels permutation56 hz
    mixedMoment B raw14117step1 raw14117step1Labels = mixedMoment B raw14117step2 raw14117step2Labels := by
      have ha : raw14117step2 = (fun i j => raw14117step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14117step2 raw14117step1; decide +kernel
      have hl : raw14117step2Labels = raw14117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14117step1 raw14117step1Labels permutation9 permutation7
    mixedMoment B raw14117step2 raw14117step2Labels = mixedMoment B raw14117step3 raw14117step3Labels := by
      have ha : raw14117step3 = -raw14117step2 := by apply Matrix.ext; change ∀ i j, raw14117step3 i j = -(raw14117step2 i j); unfold raw14117step3 raw14117step2; decide +kernel
      have hl : raw14117step3Labels = raw14117step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14117step3 raw14117step3Labels = mixedMoment B raw14117step4 raw14117step4Labels := by
      have ha : raw14117step4 = raw14117step3 := by apply Matrix.ext; unfold raw14117step4 raw14117step3; decide +kernel
      have hl : raw14117step3Labels = labelEmbedding1 ∘ raw14117step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14117step3 raw14117step3Labels raw14117step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical14118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14118 raw14118Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw14118 raw14118Labels = mixedMoment B raw14118step0 raw14118step0Labels := by
      have hz : ∀ j, raw14118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14118step0 = (fun i j => raw14118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14118step0 raw14118; decide +kernel
      have hl : raw14118step0Labels = raw14118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14118 raw14118Labels permutation265 hz
    mixedMoment B raw14118step0 raw14118step0Labels = mixedMoment B raw14118step1 raw14118step1Labels := by
      have ha : raw14118step1 = (fun i j => raw14118step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14118step1 raw14118step0; decide +kernel
      have hl : raw14118step1Labels = raw14118step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14118step0 raw14118step0Labels permutation37 permutation7
    mixedMoment B raw14118step1 raw14118step1Labels = mixedMoment B raw14118step2 raw14118step2Labels := by
      have ha : raw14118step2 = -raw14118step1 := by apply Matrix.ext; change ∀ i j, raw14118step2 i j = -(raw14118step1 i j); unfold raw14118step2 raw14118step1; decide +kernel
      have hl : raw14118step2Labels = raw14118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14118step2 raw14118step2Labels = mixedMoment B raw14118step3 raw14118step3Labels := by
      have ha : raw14118step3 = raw14118step2 := by apply Matrix.ext; unfold raw14118step3 raw14118step2; decide +kernel
      have hl : raw14118step2Labels = labelEmbedding1 ∘ raw14118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14118step2 raw14118step2Labels raw14118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical14119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14119 raw14119Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw14119 raw14119Labels = mixedMoment B raw14119step0 raw14119step0Labels := by
      have ha : raw14119step0 = (fun i j => raw14119 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14119step0 raw14119; decide +kernel
      have hl : raw14119step0Labels = raw14119Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14119 raw14119Labels permutation181 permutation7
    mixedMoment B raw14119step0 raw14119step0Labels = mixedMoment B raw14119step1 raw14119step1Labels := by
      have ha : raw14119step1 = -raw14119step0 := by apply Matrix.ext; change ∀ i j, raw14119step1 i j = -(raw14119step0 i j); unfold raw14119step1 raw14119step0; decide +kernel
      have hl : raw14119step1Labels = raw14119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14119step1 raw14119step1Labels = mixedMoment B raw14119step2 raw14119step2Labels := by
      have ha : raw14119step2 = raw14119step1 := by apply Matrix.ext; unfold raw14119step2 raw14119step1; decide +kernel
      have hl : raw14119step1Labels = labelEmbedding1 ∘ raw14119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14119step1 raw14119step1Labels raw14119step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical14120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14120 raw14120Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw14120 raw14120Labels = mixedMoment B raw14120step0 raw14120step0Labels := by
      have hz : ∀ j, raw14120 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14120step0 = (fun i j => raw14120 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14120step0 raw14120; decide +kernel
      have hl : raw14120step0Labels = raw14120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14120 raw14120Labels permutation265 hz
    mixedMoment B raw14120step0 raw14120step0Labels = mixedMoment B raw14120step1 raw14120step1Labels := by
      have ha : raw14120step1 = (fun i j => raw14120step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14120step1 raw14120step0; decide +kernel
      have hl : raw14120step1Labels = raw14120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14120step0 raw14120step0Labels permutation37 permutation7
    mixedMoment B raw14120step1 raw14120step1Labels = mixedMoment B raw14120step2 raw14120step2Labels := by
      have ha : raw14120step2 = -raw14120step1 := by apply Matrix.ext; change ∀ i j, raw14120step2 i j = -(raw14120step1 i j); unfold raw14120step2 raw14120step1; decide +kernel
      have hl : raw14120step2Labels = raw14120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14120step2 raw14120step2Labels = mixedMoment B raw14120step3 raw14120step3Labels := by
      have ha : raw14120step3 = raw14120step2 := by apply Matrix.ext; unfold raw14120step3 raw14120step2; decide +kernel
      have hl : raw14120step2Labels = labelEmbedding1 ∘ raw14120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14120step2 raw14120step2Labels raw14120step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

theorem canonical14121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14121 raw14121Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw14121 raw14121Labels = mixedMoment B raw14121step0 raw14121step0Labels := by
      have hz : ∀ j, raw14121 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14121step0 = (fun i j => raw14121 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14121step0 raw14121; decide +kernel
      have hl : raw14121step0Labels = raw14121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14121 raw14121Labels permutation265 hz
    mixedMoment B raw14121step0 raw14121step0Labels = mixedMoment B raw14121step1 raw14121step1Labels := by
      have ha : raw14121step1 = (fun i j => raw14121step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14121step1 raw14121step0; decide +kernel
      have hl : raw14121step1Labels = raw14121step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14121step0 raw14121step0Labels permutation37 permutation7
    mixedMoment B raw14121step1 raw14121step1Labels = mixedMoment B raw14121step2 raw14121step2Labels := by
      have ha : raw14121step2 = -raw14121step1 := by apply Matrix.ext; change ∀ i j, raw14121step2 i j = -(raw14121step1 i j); unfold raw14121step2 raw14121step1; decide +kernel
      have hl : raw14121step2Labels = raw14121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14121step2 raw14121step2Labels = mixedMoment B raw14121step3 raw14121step3Labels := by
      have ha : raw14121step3 = raw14121step2 := by apply Matrix.ext; unfold raw14121step3 raw14121step2; decide +kernel
      have hl : raw14121step2Labels = labelEmbedding1 ∘ raw14121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14121step2 raw14121step2Labels raw14121step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical14122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14122 raw14122Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw14122 raw14122Labels = mixedMoment B raw14122step0 raw14122step0Labels := by
      have hz : ∀ j, raw14122 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14122step0 = (fun i j => raw14122 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14122step0 raw14122; decide +kernel
      have hl : raw14122step0Labels = raw14122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14122 raw14122Labels permutation590 hz
    mixedMoment B raw14122step0 raw14122step0Labels = mixedMoment B raw14122step1 raw14122step1Labels := by
      have hz : ∀ j, raw14122step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14122step1 = (fun i j => raw14122step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14122step1 raw14122step0; decide +kernel
      have hl : raw14122step1Labels = raw14122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14122step0 raw14122step0Labels permutation56 hz
    mixedMoment B raw14122step1 raw14122step1Labels = mixedMoment B raw14122step2 raw14122step2Labels := by
      have ha : raw14122step2 = (fun i j => raw14122step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14122step2 raw14122step1; decide +kernel
      have hl : raw14122step2Labels = raw14122step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14122step1 raw14122step1Labels permutation9 permutation7
    mixedMoment B raw14122step2 raw14122step2Labels = mixedMoment B raw14122step3 raw14122step3Labels := by
      have ha : raw14122step3 = -raw14122step2 := by apply Matrix.ext; change ∀ i j, raw14122step3 i j = -(raw14122step2 i j); unfold raw14122step3 raw14122step2; decide +kernel
      have hl : raw14122step3Labels = raw14122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14122step3 raw14122step3Labels = mixedMoment B raw14122step4 raw14122step4Labels := by
      have ha : raw14122step4 = raw14122step3 := by apply Matrix.ext; unfold raw14122step4 raw14122step3; decide +kernel
      have hl : raw14122step3Labels = labelEmbedding1 ∘ raw14122step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14122step3 raw14122step3Labels raw14122step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical14123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14123 raw14123Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw14123 raw14123Labels = mixedMoment B raw14123step0 raw14123step0Labels := by
      have hz : ∀ j, raw14123 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14123step0 = (fun i j => raw14123 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14123step0 raw14123; decide +kernel
      have hl : raw14123step0Labels = raw14123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14123 raw14123Labels permutation265 hz
    mixedMoment B raw14123step0 raw14123step0Labels = mixedMoment B raw14123step1 raw14123step1Labels := by
      have ha : raw14123step1 = (fun i j => raw14123step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14123step1 raw14123step0; decide +kernel
      have hl : raw14123step1Labels = raw14123step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14123step0 raw14123step0Labels permutation37 permutation7
    mixedMoment B raw14123step1 raw14123step1Labels = mixedMoment B raw14123step2 raw14123step2Labels := by
      have ha : raw14123step2 = -raw14123step1 := by apply Matrix.ext; change ∀ i j, raw14123step2 i j = -(raw14123step1 i j); unfold raw14123step2 raw14123step1; decide +kernel
      have hl : raw14123step2Labels = raw14123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14123step2 raw14123step2Labels = mixedMoment B raw14123step3 raw14123step3Labels := by
      have ha : raw14123step3 = raw14123step2 := by apply Matrix.ext; unfold raw14123step3 raw14123step2; decide +kernel
      have hl : raw14123step2Labels = labelEmbedding1 ∘ raw14123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14123step2 raw14123step2Labels raw14123step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical14124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14124 raw14124Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw14124 raw14124Labels = mixedMoment B raw14124step0 raw14124step0Labels := by
      have ha : raw14124step0 = (fun i j => raw14124 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14124step0 raw14124; decide +kernel
      have hl : raw14124step0Labels = raw14124Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14124 raw14124Labels permutation181 permutation7
    mixedMoment B raw14124step0 raw14124step0Labels = mixedMoment B raw14124step1 raw14124step1Labels := by
      have ha : raw14124step1 = -raw14124step0 := by apply Matrix.ext; change ∀ i j, raw14124step1 i j = -(raw14124step0 i j); unfold raw14124step1 raw14124step0; decide +kernel
      have hl : raw14124step1Labels = raw14124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14124step1 raw14124step1Labels = mixedMoment B raw14124step2 raw14124step2Labels := by
      have ha : raw14124step2 = raw14124step1 := by apply Matrix.ext; unfold raw14124step2 raw14124step1; decide +kernel
      have hl : raw14124step1Labels = labelEmbedding1 ∘ raw14124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14124step1 raw14124step1Labels raw14124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

theorem canonical14125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14125 raw14125Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw14125 raw14125Labels = mixedMoment B raw14125step0 raw14125step0Labels := by
      have hz : ∀ j, raw14125 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14125step0 = (fun i j => raw14125 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14125step0 raw14125; decide +kernel
      have hl : raw14125step0Labels = raw14125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14125 raw14125Labels permutation265 hz
    mixedMoment B raw14125step0 raw14125step0Labels = mixedMoment B raw14125step1 raw14125step1Labels := by
      have ha : raw14125step1 = (fun i j => raw14125step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14125step1 raw14125step0; decide +kernel
      have hl : raw14125step1Labels = raw14125step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14125step0 raw14125step0Labels permutation37 permutation7
    mixedMoment B raw14125step1 raw14125step1Labels = mixedMoment B raw14125step2 raw14125step2Labels := by
      have ha : raw14125step2 = -raw14125step1 := by apply Matrix.ext; change ∀ i j, raw14125step2 i j = -(raw14125step1 i j); unfold raw14125step2 raw14125step1; decide +kernel
      have hl : raw14125step2Labels = raw14125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14125step2 raw14125step2Labels = mixedMoment B raw14125step3 raw14125step3Labels := by
      have ha : raw14125step3 = raw14125step2 := by apply Matrix.ext; unfold raw14125step3 raw14125step2; decide +kernel
      have hl : raw14125step2Labels = labelEmbedding1 ∘ raw14125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14125step2 raw14125step2Labels raw14125step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

theorem canonical14126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14126 raw14126Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw14126 raw14126Labels = mixedMoment B raw14126step0 raw14126step0Labels := by
      have hz : ∀ j, raw14126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14126step0 = (fun i j => raw14126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14126step0 raw14126; decide +kernel
      have hl : raw14126step0Labels = raw14126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14126 raw14126Labels permutation265 hz
    mixedMoment B raw14126step0 raw14126step0Labels = mixedMoment B raw14126step1 raw14126step1Labels := by
      have ha : raw14126step1 = (fun i j => raw14126step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14126step1 raw14126step0; decide +kernel
      have hl : raw14126step1Labels = raw14126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14126step0 raw14126step0Labels permutation37 permutation7
    mixedMoment B raw14126step1 raw14126step1Labels = mixedMoment B raw14126step2 raw14126step2Labels := by
      have ha : raw14126step2 = -raw14126step1 := by apply Matrix.ext; change ∀ i j, raw14126step2 i j = -(raw14126step1 i j); unfold raw14126step2 raw14126step1; decide +kernel
      have hl : raw14126step2Labels = raw14126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14126step2 raw14126step2Labels = mixedMoment B raw14126step3 raw14126step3Labels := by
      have ha : raw14126step3 = raw14126step2 := by apply Matrix.ext; unfold raw14126step3 raw14126step2; decide +kernel
      have hl : raw14126step2Labels = labelEmbedding1 ∘ raw14126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14126step2 raw14126step2Labels raw14126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical14127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14127 raw14127Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw14127 raw14127Labels = mixedMoment B raw14127step0 raw14127step0Labels := by
      have hz : ∀ j, raw14127 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14127step0 = (fun i j => raw14127 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14127step0 raw14127; decide +kernel
      have hl : raw14127step0Labels = raw14127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14127 raw14127Labels permutation590 hz
    mixedMoment B raw14127step0 raw14127step0Labels = mixedMoment B raw14127step1 raw14127step1Labels := by
      have hz : ∀ j, raw14127step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14127step1 = (fun i j => raw14127step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14127step1 raw14127step0; decide +kernel
      have hl : raw14127step1Labels = raw14127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14127step0 raw14127step0Labels permutation56 hz
    mixedMoment B raw14127step1 raw14127step1Labels = mixedMoment B raw14127step2 raw14127step2Labels := by
      have ha : raw14127step2 = (fun i j => raw14127step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14127step2 raw14127step1; decide +kernel
      have hl : raw14127step2Labels = raw14127step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14127step1 raw14127step1Labels permutation9 permutation7
    mixedMoment B raw14127step2 raw14127step2Labels = mixedMoment B raw14127step3 raw14127step3Labels := by
      have ha : raw14127step3 = -raw14127step2 := by apply Matrix.ext; change ∀ i j, raw14127step3 i j = -(raw14127step2 i j); unfold raw14127step3 raw14127step2; decide +kernel
      have hl : raw14127step3Labels = raw14127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14127step3 raw14127step3Labels = mixedMoment B raw14127step4 raw14127step4Labels := by
      have ha : raw14127step4 = raw14127step3 := by apply Matrix.ext; unfold raw14127step4 raw14127step3; decide +kernel
      have hl : raw14127step3Labels = labelEmbedding1 ∘ raw14127step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14127step3 raw14127step3Labels raw14127step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical14128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14128 raw14128Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw14128 raw14128Labels = mixedMoment B raw14128step0 raw14128step0Labels := by
      have hz : ∀ j, raw14128 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14128step0 = (fun i j => raw14128 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14128step0 raw14128; decide +kernel
      have hl : raw14128step0Labels = raw14128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14128 raw14128Labels permutation265 hz
    mixedMoment B raw14128step0 raw14128step0Labels = mixedMoment B raw14128step1 raw14128step1Labels := by
      have ha : raw14128step1 = (fun i j => raw14128step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14128step1 raw14128step0; decide +kernel
      have hl : raw14128step1Labels = raw14128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14128step0 raw14128step0Labels permutation37 permutation7
    mixedMoment B raw14128step1 raw14128step1Labels = mixedMoment B raw14128step2 raw14128step2Labels := by
      have ha : raw14128step2 = -raw14128step1 := by apply Matrix.ext; change ∀ i j, raw14128step2 i j = -(raw14128step1 i j); unfold raw14128step2 raw14128step1; decide +kernel
      have hl : raw14128step2Labels = raw14128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14128step2 raw14128step2Labels = mixedMoment B raw14128step3 raw14128step3Labels := by
      have ha : raw14128step3 = raw14128step2 := by apply Matrix.ext; unfold raw14128step3 raw14128step2; decide +kernel
      have hl : raw14128step2Labels = labelEmbedding1 ∘ raw14128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14128step2 raw14128step2Labels raw14128step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical14129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14129 raw14129Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw14129 raw14129Labels = mixedMoment B raw14129step0 raw14129step0Labels := by
      have ha : raw14129step0 = (fun i j => raw14129 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14129step0 raw14129; decide +kernel
      have hl : raw14129step0Labels = raw14129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14129 raw14129Labels permutation181 permutation7
    mixedMoment B raw14129step0 raw14129step0Labels = mixedMoment B raw14129step1 raw14129step1Labels := by
      have ha : raw14129step1 = -raw14129step0 := by apply Matrix.ext; change ∀ i j, raw14129step1 i j = -(raw14129step0 i j); unfold raw14129step1 raw14129step0; decide +kernel
      have hl : raw14129step1Labels = raw14129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14129step1 raw14129step1Labels = mixedMoment B raw14129step2 raw14129step2Labels := by
      have ha : raw14129step2 = raw14129step1 := by apply Matrix.ext; unfold raw14129step2 raw14129step1; decide +kernel
      have hl : raw14129step1Labels = labelEmbedding1 ∘ raw14129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14129step1 raw14129step1Labels raw14129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical14130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14130 raw14130Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw14130 raw14130Labels = mixedMoment B raw14130step0 raw14130step0Labels := by
      have hz : ∀ j, raw14130 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14130step0 = (fun i j => raw14130 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14130step0 raw14130; decide +kernel
      have hl : raw14130step0Labels = raw14130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14130 raw14130Labels permutation265 hz
    mixedMoment B raw14130step0 raw14130step0Labels = mixedMoment B raw14130step1 raw14130step1Labels := by
      have ha : raw14130step1 = (fun i j => raw14130step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14130step1 raw14130step0; decide +kernel
      have hl : raw14130step1Labels = raw14130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14130step0 raw14130step0Labels permutation37 permutation7
    mixedMoment B raw14130step1 raw14130step1Labels = mixedMoment B raw14130step2 raw14130step2Labels := by
      have ha : raw14130step2 = -raw14130step1 := by apply Matrix.ext; change ∀ i j, raw14130step2 i j = -(raw14130step1 i j); unfold raw14130step2 raw14130step1; decide +kernel
      have hl : raw14130step2Labels = raw14130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14130step2 raw14130step2Labels = mixedMoment B raw14130step3 raw14130step3Labels := by
      have ha : raw14130step3 = raw14130step2 := by apply Matrix.ext; unfold raw14130step3 raw14130step2; decide +kernel
      have hl : raw14130step2Labels = labelEmbedding1 ∘ raw14130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14130step2 raw14130step2Labels raw14130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

theorem canonical14131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14131 raw14131Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw14131 raw14131Labels = mixedMoment B raw14131step0 raw14131step0Labels := by
      have hz : ∀ j, raw14131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14131step0 = (fun i j => raw14131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14131step0 raw14131; decide +kernel
      have hl : raw14131step0Labels = raw14131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14131 raw14131Labels permutation265 hz
    mixedMoment B raw14131step0 raw14131step0Labels = mixedMoment B raw14131step1 raw14131step1Labels := by
      have ha : raw14131step1 = (fun i j => raw14131step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14131step1 raw14131step0; decide +kernel
      have hl : raw14131step1Labels = raw14131step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14131step0 raw14131step0Labels permutation37 permutation7
    mixedMoment B raw14131step1 raw14131step1Labels = mixedMoment B raw14131step2 raw14131step2Labels := by
      have ha : raw14131step2 = -raw14131step1 := by apply Matrix.ext; change ∀ i j, raw14131step2 i j = -(raw14131step1 i j); unfold raw14131step2 raw14131step1; decide +kernel
      have hl : raw14131step2Labels = raw14131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14131step2 raw14131step2Labels = mixedMoment B raw14131step3 raw14131step3Labels := by
      have ha : raw14131step3 = raw14131step2 := by apply Matrix.ext; unfold raw14131step3 raw14131step2; decide +kernel
      have hl : raw14131step2Labels = labelEmbedding1 ∘ raw14131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14131step2 raw14131step2Labels raw14131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical14132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14132 raw14132Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw14132 raw14132Labels = mixedMoment B raw14132step0 raw14132step0Labels := by
      have hz : ∀ j, raw14132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14132step0 = (fun i j => raw14132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14132step0 raw14132; decide +kernel
      have hl : raw14132step0Labels = raw14132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14132 raw14132Labels permutation265 hz
    mixedMoment B raw14132step0 raw14132step0Labels = mixedMoment B raw14132step1 raw14132step1Labels := by
      have ha : raw14132step1 = (fun i j => raw14132step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14132step1 raw14132step0; decide +kernel
      have hl : raw14132step1Labels = raw14132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14132step0 raw14132step0Labels permutation37 permutation7
    mixedMoment B raw14132step1 raw14132step1Labels = mixedMoment B raw14132step2 raw14132step2Labels := by
      have ha : raw14132step2 = -raw14132step1 := by apply Matrix.ext; change ∀ i j, raw14132step2 i j = -(raw14132step1 i j); unfold raw14132step2 raw14132step1; decide +kernel
      have hl : raw14132step2Labels = raw14132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14132step2 raw14132step2Labels = mixedMoment B raw14132step3 raw14132step3Labels := by
      have ha : raw14132step3 = raw14132step2 := by apply Matrix.ext; unfold raw14132step3 raw14132step2; decide +kernel
      have hl : raw14132step2Labels = labelEmbedding1 ∘ raw14132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14132step2 raw14132step2Labels raw14132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

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

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

theorem sound3303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3303 node3303Labels = Sparse.eval nodeValue3303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3303) = mixedMoment B node3303 node3303Labels := rfl
  simpa [nodeValue3303, Sparse.eval] using hc.symm

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

theorem zero3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = 0 := by
  exact mixedMoment_alpha B hF node3515 node3515Labels 1 permutation443
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

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3470 node3470Labels = Sparse.eval nodeValue3470 (mixedVector B) := by
  simpa only [nodeValue3470, Sparse.eval_nil] using zero3470 B _hB _hF

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

theorem sound3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3515 node3515Labels = Sparse.eval nodeValue3515 (mixedVector B) := by
  simpa only [nodeValue3515, Sparse.eval_nil] using zero3515 B _hB _hF

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

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

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

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

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
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

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem zero3861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = 0 := by
  exact mixedMoment_order_one B hB node3861 node3861Labels 1
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

theorem sound3861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = Sparse.eval nodeValue3861 (mixedVector B) := by
  simpa only [nodeValue3861, Sparse.eval_nil] using zero3861 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm849 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA849 + difference 0 1) (sourceB849 + difference 1 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA849 + difference 0 1) (sourceB849 + difference 1 0) sourceC849) = raw14103 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14103; decide +kernel
    rw [ha]
    exact (canonical14103 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA849 + difference 0 2) (sourceB849 + difference 2 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA849 + difference 0 2) (sourceB849 + difference 2 0) sourceC849) = raw14104 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14104; decide +kernel
    rw [ha]
    exact (canonical14104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA849 + difference 0 3) (sourceB849 + difference 3 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA849 + difference 0 3) (sourceB849 + difference 3 0) sourceC849) = raw14105 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14105; decide +kernel
    rw [ha]
    exact (canonical14105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA849 + difference 0 4) (sourceB849 + difference 4 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA849 + difference 0 4) (sourceB849 + difference 4 0) sourceC849) = raw14106 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14106; decide +kernel
    rw [ha]
    exact (canonical14106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA849 + difference 0 5) (sourceB849 + difference 5 0) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA849 + difference 0 5) (sourceB849 + difference 5 0) sourceC849) = raw14107 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14107; decide +kernel
    rw [ha]
    exact (canonical14107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA849 + difference 1 0) (sourceB849 + difference 0 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA849 + difference 1 0) (sourceB849 + difference 0 1) sourceC849) = raw14108 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14108; decide +kernel
    rw [ha]
    exact (canonical14108 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA849 + difference 1 2) (sourceB849 + difference 2 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA849 + difference 1 2) (sourceB849 + difference 2 1) sourceC849) = raw14109 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14109; decide +kernel
    rw [ha]
    exact (canonical14109 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA849 + difference 1 3) (sourceB849 + difference 3 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA849 + difference 1 3) (sourceB849 + difference 3 1) sourceC849) = raw14110 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14110; decide +kernel
    rw [ha]
    exact (canonical14110 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA849 + difference 1 4) (sourceB849 + difference 4 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA849 + difference 1 4) (sourceB849 + difference 4 1) sourceC849) = raw14111 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14111; decide +kernel
    rw [ha]
    exact (canonical14111 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA849 + difference 1 5) (sourceB849 + difference 5 1) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA849 + difference 1 5) (sourceB849 + difference 5 1) sourceC849) = raw14112 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14112; decide +kernel
    rw [ha]
    exact (canonical14112 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA849 + difference 2 0) (sourceB849 + difference 0 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA849 + difference 2 0) (sourceB849 + difference 0 2) sourceC849) = raw14113 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14113; decide +kernel
    rw [ha]
    exact (canonical14113 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA849 + difference 2 1) (sourceB849 + difference 1 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA849 + difference 2 1) (sourceB849 + difference 1 2) sourceC849) = raw14114 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14114; decide +kernel
    rw [ha]
    exact (canonical14114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA849 + difference 2 3) (sourceB849 + difference 3 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA849 + difference 2 3) (sourceB849 + difference 3 2) sourceC849) = raw14115 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14115; decide +kernel
    rw [ha]
    exact (canonical14115 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA849 + difference 2 4) (sourceB849 + difference 4 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA849 + difference 2 4) (sourceB849 + difference 4 2) sourceC849) = raw14116 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14116; decide +kernel
    rw [ha]
    exact (canonical14116 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA849 + difference 2 5) (sourceB849 + difference 5 2) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA849 + difference 2 5) (sourceB849 + difference 5 2) sourceC849) = raw14117 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14117; decide +kernel
    rw [ha]
    exact (canonical14117 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA849 + difference 3 0) (sourceB849 + difference 0 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA849 + difference 3 0) (sourceB849 + difference 0 3) sourceC849) = raw14118 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14118; decide +kernel
    rw [ha]
    exact (canonical14118 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA849 + difference 3 1) (sourceB849 + difference 1 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA849 + difference 3 1) (sourceB849 + difference 1 3) sourceC849) = raw14119 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14119; decide +kernel
    rw [ha]
    exact (canonical14119 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA849 + difference 3 2) (sourceB849 + difference 2 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA849 + difference 3 2) (sourceB849 + difference 2 3) sourceC849) = raw14120 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14120; decide +kernel
    rw [ha]
    exact (canonical14120 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA849 + difference 3 4) (sourceB849 + difference 4 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA849 + difference 3 4) (sourceB849 + difference 4 3) sourceC849) = raw14121 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14121; decide +kernel
    rw [ha]
    exact (canonical14121 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA849 + difference 3 5) (sourceB849 + difference 5 3) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA849 + difference 3 5) (sourceB849 + difference 5 3) sourceC849) = raw14122 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14122; decide +kernel
    rw [ha]
    exact (canonical14122 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA849 + difference 4 0) (sourceB849 + difference 0 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA849 + difference 4 0) (sourceB849 + difference 0 4) sourceC849) = raw14123 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14123; decide +kernel
    rw [ha]
    exact (canonical14123 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA849 + difference 4 1) (sourceB849 + difference 1 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA849 + difference 4 1) (sourceB849 + difference 1 4) sourceC849) = raw14124 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14124; decide +kernel
    rw [ha]
    exact (canonical14124 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA849 + difference 4 2) (sourceB849 + difference 2 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA849 + difference 4 2) (sourceB849 + difference 2 4) sourceC849) = raw14125 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14125; decide +kernel
    rw [ha]
    exact (canonical14125 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA849 + difference 4 3) (sourceB849 + difference 3 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA849 + difference 4 3) (sourceB849 + difference 3 4) sourceC849) = raw14126 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14126; decide +kernel
    rw [ha]
    exact (canonical14126 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA849 + difference 4 5) (sourceB849 + difference 5 4) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA849 + difference 4 5) (sourceB849 + difference 5 4) sourceC849) = raw14127 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14127; decide +kernel
    rw [ha]
    exact (canonical14127 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA849 + difference 5 0) (sourceB849 + difference 0 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA849 + difference 5 0) (sourceB849 + difference 0 5) sourceC849) = raw14128 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14128; decide +kernel
    rw [ha]
    exact (canonical14128 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA849 + difference 5 1) (sourceB849 + difference 1 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA849 + difference 5 1) (sourceB849 + difference 1 5) sourceC849) = raw14129 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14129; decide +kernel
    rw [ha]
    exact (canonical14129 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA849 + difference 5 2) (sourceB849 + difference 2 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA849 + difference 5 2) (sourceB849 + difference 2 5) sourceC849) = raw14130 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14130; decide +kernel
    rw [ha]
    exact (canonical14130 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA849 + difference 5 3) (sourceB849 + difference 3 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA849 + difference 5 3) (sourceB849 + difference 3 5) sourceC849) = raw14131 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14131; decide +kernel
    rw [ha]
    exact (canonical14131 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA849 + difference 5 4) (sourceB849 + difference 4 5) sourceC849) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA849 + difference 5 4) (sourceB849 + difference 4 5) sourceC849) = raw14132 := by
      apply Matrix.ext; unfold tripleCharges sourceA849 sourceB849 sourceC849 difference raw14132; decide +kernel
    rw [ha]
    exact (canonical14132 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA849 sourceB849 sourceC849
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm849, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck739 : Integer.Sparse.reindex keyMap MixedData.row739 = numericRow739 := by decide +kernel

theorem numericCheck739 (x : Master → ℝ) : Integer.Sparse.eval numericRow739 x =
    (4320 : ℝ) * reducedSource739 x := by
  norm_num [numericRow739, reducedSource739, Integer.Sparse.eval, Sparse.eval, nodeValue3289, nodeValue3293, nodeValue3294, nodeValue3296, nodeValue3303, nodeValue3460, nodeValue3470, nodeValue3471, nodeValue3479, nodeValue3514, nodeValue3515, nodeValue3517, nodeValue3525, nodeValue3526, nodeValue3533, nodeValue3534, nodeValue3535, nodeValue3540, nodeValue3541, nodeValue3547, nodeValue3548, nodeValue3558, nodeValue3572, nodeValue3573, nodeValue3583, nodeValue3808, nodeValue3838, nodeValue3852, nodeValue3853, nodeValue3861] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource739 (mixedVector B) = 0 := by
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  have h3861 : mixedVector B (Sum.inr 3861) = Sparse.eval nodeValue3861 (mixedVector B) := by
    change mixedMoment B node3861 node3861Labels = _
    exact sound3861 B hB hF
  simpa only [sourceForm849, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3289, h3293, h3294, h3296, h3303, h3460, h3470, h3471, h3479, h3514, h3515, h3517, h3525, h3526, h3533, h3534, h3535, h3540, h3541, h3547, h3548, h3558, h3572, h3573, h3583, h3808, h3838, h3852, h3853, h3861, reducedSource739] using sourceEq849 B hB

theorem rowSound739_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row739 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck739, numericCheck739, reducedZero739 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e_oai
