-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:42:27.612415+00:00
-- url     : https://prove2.me/submissions/8b196828-437b-4fd5-8838-f1e3e98720ef

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1937_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1941_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1942_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1944_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1945_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1948_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1949_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1950_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24061 raw24061Labels = mixedMoment B node2607 node2607Labels := by
  calc
    _ = mixedMoment B node2607 node2607Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24066 raw24066Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw24066 raw24066Labels = mixedMoment B raw24066step0 raw24066step0Labels := by
      have ha : raw24066step0 = (fun i j => raw24066 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24066step0 raw24066; decide +kernel
      have hl : raw24066step0Labels = raw24066Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24066 raw24066Labels permutation176 permutation0
    _ = mixedMoment B node4087 node4087Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24517 raw24517Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw24517 raw24517Labels = mixedMoment B raw24517step0 raw24517step0Labels := by
      have hz : ∀ j, raw24517 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24517step0 = (fun i j => raw24517 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24517step0 raw24517; decide +kernel
      have hl : raw24517step0Labels = raw24517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24517 raw24517Labels permutation265 hz
    mixedMoment B raw24517step0 raw24517step0Labels = mixedMoment B raw24517step1 raw24517step1Labels := by
      have ha : raw24517step1 = (fun i j => raw24517step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24517step1 raw24517step0; decide +kernel
      have hl : raw24517step1Labels = raw24517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24517step0 raw24517step0Labels permutation32 permutation7
    mixedMoment B raw24517step1 raw24517step1Labels = mixedMoment B raw24517step2 raw24517step2Labels := by
      have ha : raw24517step2 = -raw24517step1 := by apply Matrix.ext; change ∀ i j, raw24517step2 i j = -(raw24517step1 i j); unfold raw24517step2 raw24517step1; decide +kernel
      have hl : raw24517step2Labels = raw24517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24517step2 raw24517step2Labels = mixedMoment B raw24517step3 raw24517step3Labels := by
      have ha : raw24517step3 = raw24517step2 := by apply Matrix.ext; unfold raw24517step3 raw24517step2; decide +kernel
      have hl : raw24517step2Labels = labelEmbedding1 ∘ raw24517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24517step2 raw24517step2Labels raw24517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical24518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24518 raw24518Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24518 raw24518Labels = mixedMoment B raw24518step0 raw24518step0Labels := by
      have hz : ∀ j, raw24518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24518step0 = (fun i j => raw24518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24518step0 raw24518; decide +kernel
      have hl : raw24518step0Labels = raw24518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24518 raw24518Labels permutation265 hz
    mixedMoment B raw24518step0 raw24518step0Labels = mixedMoment B raw24518step1 raw24518step1Labels := by
      have ha : raw24518step1 = (fun i j => raw24518step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24518step1 raw24518step0; decide +kernel
      have hl : raw24518step1Labels = raw24518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24518step0 raw24518step0Labels permutation32 permutation7
    mixedMoment B raw24518step1 raw24518step1Labels = mixedMoment B raw24518step2 raw24518step2Labels := by
      have ha : raw24518step2 = -raw24518step1 := by apply Matrix.ext; change ∀ i j, raw24518step2 i j = -(raw24518step1 i j); unfold raw24518step2 raw24518step1; decide +kernel
      have hl : raw24518step2Labels = raw24518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24518step2 raw24518step2Labels = mixedMoment B raw24518step3 raw24518step3Labels := by
      have ha : raw24518step3 = raw24518step2 := by apply Matrix.ext; unfold raw24518step3 raw24518step2; decide +kernel
      have hl : raw24518step2Labels = labelEmbedding1 ∘ raw24518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24518step2 raw24518step2Labels raw24518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical24519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24519 raw24519Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24519 raw24519Labels = mixedMoment B raw24519step0 raw24519step0Labels := by
      have hz : ∀ j, raw24519 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24519step0 = (fun i j => raw24519 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24519step0 raw24519; decide +kernel
      have hl : raw24519step0Labels = raw24519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24519 raw24519Labels permutation265 hz
    mixedMoment B raw24519step0 raw24519step0Labels = mixedMoment B raw24519step1 raw24519step1Labels := by
      have ha : raw24519step1 = (fun i j => raw24519step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24519step1 raw24519step0; decide +kernel
      have hl : raw24519step1Labels = raw24519step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24519step0 raw24519step0Labels permutation34 permutation7
    mixedMoment B raw24519step1 raw24519step1Labels = mixedMoment B raw24519step2 raw24519step2Labels := by
      have ha : raw24519step2 = -raw24519step1 := by apply Matrix.ext; change ∀ i j, raw24519step2 i j = -(raw24519step1 i j); unfold raw24519step2 raw24519step1; decide +kernel
      have hl : raw24519step2Labels = raw24519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24519step2 raw24519step2Labels = mixedMoment B raw24519step3 raw24519step3Labels := by
      have ha : raw24519step3 = raw24519step2 := by apply Matrix.ext; unfold raw24519step3 raw24519step2; decide +kernel
      have hl : raw24519step2Labels = labelEmbedding1 ∘ raw24519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24519step2 raw24519step2Labels raw24519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical24520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24520 raw24520Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw24520 raw24520Labels = mixedMoment B raw24520step0 raw24520step0Labels := by
      have hz : ∀ j, raw24520 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24520step0 = (fun i j => raw24520 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24520step0 raw24520; decide +kernel
      have hl : raw24520step0Labels = raw24520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24520 raw24520Labels permutation265 hz
    mixedMoment B raw24520step0 raw24520step0Labels = mixedMoment B raw24520step1 raw24520step1Labels := by
      have ha : raw24520step1 = (fun i j => raw24520step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24520step1 raw24520step0; decide +kernel
      have hl : raw24520step1Labels = raw24520step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24520step0 raw24520step0Labels permutation32 permutation7
    mixedMoment B raw24520step1 raw24520step1Labels = mixedMoment B raw24520step2 raw24520step2Labels := by
      have ha : raw24520step2 = -raw24520step1 := by apply Matrix.ext; change ∀ i j, raw24520step2 i j = -(raw24520step1 i j); unfold raw24520step2 raw24520step1; decide +kernel
      have hl : raw24520step2Labels = raw24520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24520step2 raw24520step2Labels = mixedMoment B raw24520step3 raw24520step3Labels := by
      have ha : raw24520step3 = raw24520step2 := by apply Matrix.ext; unfold raw24520step3 raw24520step2; decide +kernel
      have hl : raw24520step2Labels = labelEmbedding1 ∘ raw24520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24520step2 raw24520step2Labels raw24520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical24527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24527 raw24527Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw24527 raw24527Labels = mixedMoment B raw24527step0 raw24527step0Labels := by
      have ha : raw24527step0 = (fun i j => raw24527 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24527step0 raw24527; decide +kernel
      have hl : raw24527step0Labels = raw24527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24527 raw24527Labels permutation161 permutation5
    mixedMoment B raw24527step0 raw24527step0Labels = mixedMoment B raw24527step1 raw24527step1Labels := by
      have ha : raw24527step1 = -raw24527step0 := by apply Matrix.ext; change ∀ i j, raw24527step1 i j = -(raw24527step0 i j); unfold raw24527step1 raw24527step0; decide +kernel
      have hl : raw24527step1Labels = raw24527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24527step1 raw24527step1Labels = mixedMoment B raw24527step2 raw24527step2Labels := by
      have ha : raw24527step2 = raw24527step1 := by apply Matrix.ext; unfold raw24527step2 raw24527step1; decide +kernel
      have hl : raw24527step1Labels = labelEmbedding1 ∘ raw24527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24527step1 raw24527step1Labels raw24527step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical24532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24532 raw24532Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24532 raw24532Labels = mixedMoment B raw24532step0 raw24532step0Labels := by
      have ha : raw24532step0 = (fun i j => raw24532 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24532step0 raw24532; decide +kernel
      have hl : raw24532step0Labels = raw24532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24532 raw24532Labels permutation164 permutation5
    mixedMoment B raw24532step0 raw24532step0Labels = mixedMoment B raw24532step1 raw24532step1Labels := by
      have ha : raw24532step1 = -raw24532step0 := by apply Matrix.ext; change ∀ i j, raw24532step1 i j = -(raw24532step0 i j); unfold raw24532step1 raw24532step0; decide +kernel
      have hl : raw24532step1Labels = raw24532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24532step1 raw24532step1Labels = mixedMoment B raw24532step2 raw24532step2Labels := by
      have ha : raw24532step2 = raw24532step1 := by apply Matrix.ext; unfold raw24532step2 raw24532step1; decide +kernel
      have hl : raw24532step1Labels = labelEmbedding1 ∘ raw24532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24532step1 raw24532step1Labels raw24532step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical24537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24537 raw24537Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24537 raw24537Labels = mixedMoment B raw24537step0 raw24537step0Labels := by
      have ha : raw24537step0 = (fun i j => raw24537 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24537step0 raw24537; decide +kernel
      have hl : raw24537step0Labels = raw24537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24537 raw24537Labels permutation158 permutation5
    mixedMoment B raw24537step0 raw24537step0Labels = mixedMoment B raw24537step1 raw24537step1Labels := by
      have ha : raw24537step1 = -raw24537step0 := by apply Matrix.ext; change ∀ i j, raw24537step1 i j = -(raw24537step0 i j); unfold raw24537step1 raw24537step0; decide +kernel
      have hl : raw24537step1Labels = raw24537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24537step1 raw24537step1Labels = mixedMoment B raw24537step2 raw24537step2Labels := by
      have ha : raw24537step2 = raw24537step1 := by apply Matrix.ext; unfold raw24537step2 raw24537step1; decide +kernel
      have hl : raw24537step1Labels = labelEmbedding1 ∘ raw24537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24537step1 raw24537step1Labels raw24537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

theorem canonical24542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24542 raw24542Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw24542 raw24542Labels = mixedMoment B raw24542step0 raw24542step0Labels := by
      have ha : raw24542step0 = (fun i j => raw24542 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24542step0 raw24542; decide +kernel
      have hl : raw24542step0Labels = raw24542Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24542 raw24542Labels permutation160 permutation5
    mixedMoment B raw24542step0 raw24542step0Labels = mixedMoment B raw24542step1 raw24542step1Labels := by
      have ha : raw24542step1 = -raw24542step0 := by apply Matrix.ext; change ∀ i j, raw24542step1 i j = -(raw24542step0 i j); unfold raw24542step1 raw24542step0; decide +kernel
      have hl : raw24542step1Labels = raw24542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24542step1 raw24542step1Labels = mixedMoment B raw24542step2 raw24542step2Labels := by
      have ha : raw24542step2 = raw24542step1 := by apply Matrix.ext; unfold raw24542step2 raw24542step1; decide +kernel
      have hl : raw24542step1Labels = labelEmbedding1 ∘ raw24542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24542step1 raw24542step1Labels raw24542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical24553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24553 raw24553Labels = mixedMoment B node2556 node2556Labels := by
  calc
    _ = mixedMoment B node2556 node2556Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24746 raw24746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24746 raw24746Labels = mixedMoment B raw24746step0 raw24746step0Labels := by
      have hz : ∀ j, raw24746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24746step0 = (fun i j => raw24746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24746step0 raw24746; decide +kernel
      have hl : raw24746step0Labels = raw24746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746 raw24746Labels permutation520 hz
    mixedMoment B raw24746step0 raw24746step0Labels = mixedMoment B raw24746step1 raw24746step1Labels := by
      have hz : ∀ j, raw24746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24746step1 = (fun i j => raw24746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24746step1 raw24746step0; decide +kernel
      have hl : raw24746step1Labels = raw24746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746step0 raw24746step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical24747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24747 raw24747Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw24747 raw24747Labels = mixedMoment B raw24747step0 raw24747step0Labels := by
      have ha : raw24747step0 = (fun i j => raw24747 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24747step0 raw24747; decide +kernel
      have hl : raw24747step0Labels = raw24747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24747 raw24747Labels permutation154 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

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

theorem canonical27531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27531 raw27531Labels = mixedMoment B node2349 node2349Labels := by
  calc
    _ = mixedMoment B node2349 node2349Labels := by rfl

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

theorem canonical27812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27812 raw27812Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw27812 raw27812Labels = mixedMoment B raw27812step0 raw27812step0Labels := by
      have hz : ∀ j, raw27812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27812step0 = (fun i j => raw27812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27812step0 raw27812; decide +kernel
      have hl : raw27812step0Labels = raw27812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27812 raw27812Labels permutation346 hz
    mixedMoment B raw27812step0 raw27812step0Labels = mixedMoment B raw27812step1 raw27812step1Labels := by
      have ha : raw27812step1 = (fun i j => raw27812step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27812step1 raw27812step0; decide +kernel
      have hl : raw27812step1Labels = raw27812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27812step0 raw27812step0Labels permutation34 permutation2
    _ = mixedMoment B node2355 node2355Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28458 raw28458Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28458 raw28458Labels = mixedMoment B raw28458step0 raw28458step0Labels := by
      have hz : ∀ j, raw28458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28458step0 = (fun i j => raw28458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28458step0 raw28458; decide +kernel
      have hl : raw28458step0Labels = raw28458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28458 raw28458Labels permutation346 hz
    mixedMoment B raw28458step0 raw28458step0Labels = mixedMoment B raw28458step1 raw28458step1Labels := by
      have ha : raw28458step1 = (fun i j => raw28458step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28458step1 raw28458step0; decide +kernel
      have hl : raw28458step1Labels = raw28458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28458step0 raw28458step0Labels permutation145 permutation2
    mixedMoment B raw28458step1 raw28458step1Labels = mixedMoment B raw28458step2 raw28458step2Labels := by
      have ha : raw28458step2 = -raw28458step1 := by apply Matrix.ext; change ∀ i j, raw28458step2 i j = -(raw28458step1 i j); unfold raw28458step2 raw28458step1; decide +kernel
      have hl : raw28458step2Labels = raw28458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical28461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28461 raw28461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw28461 raw28461Labels = mixedMoment B raw28461step0 raw28461step0Labels := by
      have hz : ∀ j, raw28461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28461step0 = (fun i j => raw28461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28461step0 raw28461; decide +kernel
      have hl : raw28461step0Labels = raw28461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461 raw28461Labels permutation520 hz
    mixedMoment B raw28461step0 raw28461step0Labels = mixedMoment B raw28461step1 raw28461step1Labels := by
      have hz : ∀ j, raw28461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28461step1 = (fun i j => raw28461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28461step1 raw28461step0; decide +kernel
      have hl : raw28461step1Labels = raw28461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step0 raw28461step0Labels permutation104 hz
    mixedMoment B raw28461step1 raw28461step1Labels = mixedMoment B raw28461step2 raw28461step2Labels := by
      have hz : ∀ j, raw28461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28461step2 = (fun i j => raw28461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28461step2 raw28461step1; decide +kernel
      have hl : raw28461step2Labels = raw28461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step1 raw28461step1Labels permutation20 hz
    mixedMoment B raw28461step2 raw28461step2Labels = mixedMoment B raw28461step3 raw28461step3Labels := by
      have ha : raw28461step3 = (fun i j => raw28461step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28461step3 raw28461step2; decide +kernel
      have hl : raw28461step3Labels = raw28461step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28461step2 raw28461step2Labels permutation6 permutation0
    mixedMoment B raw28461step3 raw28461step3Labels = mixedMoment B raw28461step4 raw28461step4Labels := by
      have ha : raw28461step4 = -raw28461step3 := by apply Matrix.ext; change ∀ i j, raw28461step4 i j = -(raw28461step3 i j); unfold raw28461step4 raw28461step3; decide +kernel
      have hl : raw28461step4Labels = raw28461step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical29460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29460 raw29460Labels = mixedMoment B node2350 node2350Labels := by
  calc
    _ = mixedMoment B node2350 node2350Labels := by rfl

theorem canonical29487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29487 raw29487Labels = mixedMoment B node2351 node2351Labels := by
  calc
    _ = mixedMoment B node2351 node2351Labels := by rfl

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

theorem canonical32597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32597 raw32597Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw32597 raw32597Labels = mixedMoment B raw32597step0 raw32597step0Labels := by
      have hz : ∀ j, raw32597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32597step0 = (fun i j => raw32597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32597step0 raw32597; decide +kernel
      have hl : raw32597step0Labels = raw32597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32597 raw32597Labels permutation346 hz
    mixedMoment B raw32597step0 raw32597step0Labels = mixedMoment B raw32597step1 raw32597step1Labels := by
      have ha : raw32597step1 = (fun i j => raw32597step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32597step1 raw32597step0; decide +kernel
      have hl : raw32597step1Labels = raw32597step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32597step0 raw32597step0Labels permutation56 permutation7
    mixedMoment B raw32597step1 raw32597step1Labels = mixedMoment B raw32597step2 raw32597step2Labels := by
      have ha : raw32597step2 = -raw32597step1 := by apply Matrix.ext; change ∀ i j, raw32597step2 i j = -(raw32597step1 i j); unfold raw32597step2 raw32597step1; decide +kernel
      have hl : raw32597step2Labels = raw32597step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32597step2 raw32597step2Labels = mixedMoment B raw32597step3 raw32597step3Labels := by
      have ha : raw32597step3 = raw32597step2 := by apply Matrix.ext; unfold raw32597step3 raw32597step2; decide +kernel
      have hl : raw32597step2Labels = labelEmbedding1 ∘ raw32597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32597step2 raw32597step2Labels raw32597step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

theorem canonical32598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32598 raw32598Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw32598 raw32598Labels = mixedMoment B raw32598step0 raw32598step0Labels := by
      have ha : raw32598step0 = (fun i j => raw32598 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32598step0 raw32598; decide +kernel
      have hl : raw32598step0Labels = raw32598Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32598 raw32598Labels permutation265 permutation7
    mixedMoment B raw32598step0 raw32598step0Labels = mixedMoment B raw32598step1 raw32598step1Labels := by
      have ha : raw32598step1 = -raw32598step0 := by apply Matrix.ext; change ∀ i j, raw32598step1 i j = -(raw32598step0 i j); unfold raw32598step1 raw32598step0; decide +kernel
      have hl : raw32598step1Labels = raw32598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32598step1 raw32598step1Labels = mixedMoment B raw32598step2 raw32598step2Labels := by
      have ha : raw32598step2 = raw32598step1 := by apply Matrix.ext; unfold raw32598step2 raw32598step1; decide +kernel
      have hl : raw32598step1Labels = labelEmbedding1 ∘ raw32598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32598step1 raw32598step1Labels raw32598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

theorem canonical32599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32599 raw32599Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw32599 raw32599Labels = mixedMoment B raw32599step0 raw32599step0Labels := by
      have hz : ∀ j, raw32599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32599step0 = (fun i j => raw32599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32599step0 raw32599; decide +kernel
      have hl : raw32599step0Labels = raw32599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32599 raw32599Labels permutation346 hz
    mixedMoment B raw32599step0 raw32599step0Labels = mixedMoment B raw32599step1 raw32599step1Labels := by
      have ha : raw32599step1 = (fun i j => raw32599step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32599step1 raw32599step0; decide +kernel
      have hl : raw32599step1Labels = raw32599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32599step0 raw32599step0Labels permutation56 permutation7
    mixedMoment B raw32599step1 raw32599step1Labels = mixedMoment B raw32599step2 raw32599step2Labels := by
      have ha : raw32599step2 = -raw32599step1 := by apply Matrix.ext; change ∀ i j, raw32599step2 i j = -(raw32599step1 i j); unfold raw32599step2 raw32599step1; decide +kernel
      have hl : raw32599step2Labels = raw32599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32599step2 raw32599step2Labels = mixedMoment B raw32599step3 raw32599step3Labels := by
      have ha : raw32599step3 = raw32599step2 := by apply Matrix.ext; unfold raw32599step3 raw32599step2; decide +kernel
      have hl : raw32599step2Labels = labelEmbedding1 ∘ raw32599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32599step2 raw32599step2Labels raw32599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical32600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32600 raw32600Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw32600 raw32600Labels = mixedMoment B raw32600step0 raw32600step0Labels := by
      have hz : ∀ j, raw32600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32600step0 = (fun i j => raw32600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32600step0 raw32600; decide +kernel
      have hl : raw32600step0Labels = raw32600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32600 raw32600Labels permutation346 hz
    mixedMoment B raw32600step0 raw32600step0Labels = mixedMoment B raw32600step1 raw32600step1Labels := by
      have ha : raw32600step1 = (fun i j => raw32600step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32600step1 raw32600step0; decide +kernel
      have hl : raw32600step1Labels = raw32600step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32600step0 raw32600step0Labels permutation58 permutation7
    mixedMoment B raw32600step1 raw32600step1Labels = mixedMoment B raw32600step2 raw32600step2Labels := by
      have ha : raw32600step2 = -raw32600step1 := by apply Matrix.ext; change ∀ i j, raw32600step2 i j = -(raw32600step1 i j); unfold raw32600step2 raw32600step1; decide +kernel
      have hl : raw32600step2Labels = raw32600step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32600step2 raw32600step2Labels = mixedMoment B raw32600step3 raw32600step3Labels := by
      have ha : raw32600step3 = raw32600step2 := by apply Matrix.ext; unfold raw32600step3 raw32600step2; decide +kernel
      have hl : raw32600step2Labels = labelEmbedding1 ∘ raw32600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32600step2 raw32600step2Labels raw32600step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical32601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32601 raw32601Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw32601 raw32601Labels = mixedMoment B raw32601step0 raw32601step0Labels := by
      have hz : ∀ j, raw32601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32601step0 = (fun i j => raw32601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32601step0 raw32601; decide +kernel
      have hl : raw32601step0Labels = raw32601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32601 raw32601Labels permutation346 hz
    mixedMoment B raw32601step0 raw32601step0Labels = mixedMoment B raw32601step1 raw32601step1Labels := by
      have ha : raw32601step1 = (fun i j => raw32601step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32601step1 raw32601step0; decide +kernel
      have hl : raw32601step1Labels = raw32601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32601step0 raw32601step0Labels permutation56 permutation7
    mixedMoment B raw32601step1 raw32601step1Labels = mixedMoment B raw32601step2 raw32601step2Labels := by
      have ha : raw32601step2 = -raw32601step1 := by apply Matrix.ext; change ∀ i j, raw32601step2 i j = -(raw32601step1 i j); unfold raw32601step2 raw32601step1; decide +kernel
      have hl : raw32601step2Labels = raw32601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32601step2 raw32601step2Labels = mixedMoment B raw32601step3 raw32601step3Labels := by
      have ha : raw32601step3 = raw32601step2 := by apply Matrix.ext; unfold raw32601step3 raw32601step2; decide +kernel
      have hl : raw32601step2Labels = labelEmbedding1 ∘ raw32601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32601step2 raw32601step2Labels raw32601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

theorem canonical32602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32602 raw32602Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw32602 raw32602Labels = mixedMoment B raw32602step0 raw32602step0Labels := by
      have hz : ∀ j, raw32602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32602step0 = (fun i j => raw32602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32602step0 raw32602; decide +kernel
      have hl : raw32602step0Labels = raw32602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32602 raw32602Labels permutation346 hz
    mixedMoment B raw32602step0 raw32602step0Labels = mixedMoment B raw32602step1 raw32602step1Labels := by
      have ha : raw32602step1 = (fun i j => raw32602step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32602step1 raw32602step0; decide +kernel
      have hl : raw32602step1Labels = raw32602step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32602step0 raw32602step0Labels permutation41 permutation5
    mixedMoment B raw32602step1 raw32602step1Labels = mixedMoment B raw32602step2 raw32602step2Labels := by
      have ha : raw32602step2 = -raw32602step1 := by apply Matrix.ext; change ∀ i j, raw32602step2 i j = -(raw32602step1 i j); unfold raw32602step2 raw32602step1; decide +kernel
      have hl : raw32602step2Labels = raw32602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32602step2 raw32602step2Labels = mixedMoment B raw32602step3 raw32602step3Labels := by
      have ha : raw32602step3 = raw32602step2 := by apply Matrix.ext; unfold raw32602step3 raw32602step2; decide +kernel
      have hl : raw32602step2Labels = labelEmbedding1 ∘ raw32602step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32602step2 raw32602step2Labels raw32602step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical32603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32603 raw32603Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw32603 raw32603Labels = mixedMoment B raw32603step0 raw32603step0Labels := by
      have ha : raw32603step0 = (fun i j => raw32603 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32603step0 raw32603; decide +kernel
      have hl : raw32603step0Labels = raw32603Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32603 raw32603Labels permutation185 permutation5
    mixedMoment B raw32603step0 raw32603step0Labels = mixedMoment B raw32603step1 raw32603step1Labels := by
      have ha : raw32603step1 = -raw32603step0 := by apply Matrix.ext; change ∀ i j, raw32603step1 i j = -(raw32603step0 i j); unfold raw32603step1 raw32603step0; decide +kernel
      have hl : raw32603step1Labels = raw32603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32603step1 raw32603step1Labels = mixedMoment B raw32603step2 raw32603step2Labels := by
      have ha : raw32603step2 = raw32603step1 := by apply Matrix.ext; unfold raw32603step2 raw32603step1; decide +kernel
      have hl : raw32603step1Labels = labelEmbedding1 ∘ raw32603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32603step1 raw32603step1Labels raw32603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

theorem canonical32604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32604 raw32604Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw32604 raw32604Labels = mixedMoment B raw32604step0 raw32604step0Labels := by
      have hz : ∀ j, raw32604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32604step0 = (fun i j => raw32604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32604step0 raw32604; decide +kernel
      have hl : raw32604step0Labels = raw32604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32604 raw32604Labels permutation346 hz
    mixedMoment B raw32604step0 raw32604step0Labels = mixedMoment B raw32604step1 raw32604step1Labels := by
      have ha : raw32604step1 = (fun i j => raw32604step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32604step1 raw32604step0; decide +kernel
      have hl : raw32604step1Labels = raw32604step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32604step0 raw32604step0Labels permutation41 permutation5
    mixedMoment B raw32604step1 raw32604step1Labels = mixedMoment B raw32604step2 raw32604step2Labels := by
      have ha : raw32604step2 = -raw32604step1 := by apply Matrix.ext; change ∀ i j, raw32604step2 i j = -(raw32604step1 i j); unfold raw32604step2 raw32604step1; decide +kernel
      have hl : raw32604step2Labels = raw32604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32604step2 raw32604step2Labels = mixedMoment B raw32604step3 raw32604step3Labels := by
      have ha : raw32604step3 = raw32604step2 := by apply Matrix.ext; unfold raw32604step3 raw32604step2; decide +kernel
      have hl : raw32604step2Labels = labelEmbedding1 ∘ raw32604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32604step2 raw32604step2Labels raw32604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical32605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32605 raw32605Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw32605 raw32605Labels = mixedMoment B raw32605step0 raw32605step0Labels := by
      have hz : ∀ j, raw32605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32605step0 = (fun i j => raw32605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32605step0 raw32605; decide +kernel
      have hl : raw32605step0Labels = raw32605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32605 raw32605Labels permutation346 hz
    mixedMoment B raw32605step0 raw32605step0Labels = mixedMoment B raw32605step1 raw32605step1Labels := by
      have ha : raw32605step1 = (fun i j => raw32605step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32605step1 raw32605step0; decide +kernel
      have hl : raw32605step1Labels = raw32605step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32605step0 raw32605step0Labels permutation47 permutation5
    mixedMoment B raw32605step1 raw32605step1Labels = mixedMoment B raw32605step2 raw32605step2Labels := by
      have ha : raw32605step2 = -raw32605step1 := by apply Matrix.ext; change ∀ i j, raw32605step2 i j = -(raw32605step1 i j); unfold raw32605step2 raw32605step1; decide +kernel
      have hl : raw32605step2Labels = raw32605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32605step2 raw32605step2Labels = mixedMoment B raw32605step3 raw32605step3Labels := by
      have ha : raw32605step3 = raw32605step2 := by apply Matrix.ext; unfold raw32605step3 raw32605step2; decide +kernel
      have hl : raw32605step2Labels = labelEmbedding1 ∘ raw32605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32605step2 raw32605step2Labels raw32605step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical32606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32606 raw32606Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw32606 raw32606Labels = mixedMoment B raw32606step0 raw32606step0Labels := by
      have hz : ∀ j, raw32606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32606step0 = (fun i j => raw32606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32606step0 raw32606; decide +kernel
      have hl : raw32606step0Labels = raw32606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32606 raw32606Labels permutation346 hz
    mixedMoment B raw32606step0 raw32606step0Labels = mixedMoment B raw32606step1 raw32606step1Labels := by
      have ha : raw32606step1 = (fun i j => raw32606step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32606step1 raw32606step0; decide +kernel
      have hl : raw32606step1Labels = raw32606step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32606step0 raw32606step0Labels permutation41 permutation5
    mixedMoment B raw32606step1 raw32606step1Labels = mixedMoment B raw32606step2 raw32606step2Labels := by
      have ha : raw32606step2 = -raw32606step1 := by apply Matrix.ext; change ∀ i j, raw32606step2 i j = -(raw32606step1 i j); unfold raw32606step2 raw32606step1; decide +kernel
      have hl : raw32606step2Labels = raw32606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32606step2 raw32606step2Labels = mixedMoment B raw32606step3 raw32606step3Labels := by
      have ha : raw32606step3 = raw32606step2 := by apply Matrix.ext; unfold raw32606step3 raw32606step2; decide +kernel
      have hl : raw32606step2Labels = labelEmbedding1 ∘ raw32606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32606step2 raw32606step2Labels raw32606step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical32607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32607 raw32607Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw32607 raw32607Labels = mixedMoment B raw32607step0 raw32607step0Labels := by
      have ha : raw32607step0 = (fun i j => raw32607 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32607step0 raw32607; decide +kernel
      have hl : raw32607step0Labels = raw32607Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32607 raw32607Labels permutation212 permutation5
    mixedMoment B raw32607step0 raw32607step0Labels = mixedMoment B raw32607step1 raw32607step1Labels := by
      have ha : raw32607step1 = -raw32607step0 := by apply Matrix.ext; change ∀ i j, raw32607step1 i j = -(raw32607step0 i j); unfold raw32607step1 raw32607step0; decide +kernel
      have hl : raw32607step1Labels = raw32607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32607step1 raw32607step1Labels = mixedMoment B raw32607step2 raw32607step2Labels := by
      have ha : raw32607step2 = raw32607step1 := by apply Matrix.ext; unfold raw32607step2 raw32607step1; decide +kernel
      have hl : raw32607step1Labels = labelEmbedding1 ∘ raw32607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32607step1 raw32607step1Labels raw32607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical32608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32608 raw32608Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw32608 raw32608Labels = mixedMoment B raw32608step0 raw32608step0Labels := by
      have ha : raw32608step0 = (fun i j => raw32608 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32608step0 raw32608; decide +kernel
      have hl : raw32608step0Labels = raw32608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32608 raw32608Labels permutation160 permutation5
    mixedMoment B raw32608step0 raw32608step0Labels = mixedMoment B raw32608step1 raw32608step1Labels := by
      have ha : raw32608step1 = -raw32608step0 := by apply Matrix.ext; change ∀ i j, raw32608step1 i j = -(raw32608step0 i j); unfold raw32608step1 raw32608step0; decide +kernel
      have hl : raw32608step1Labels = raw32608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32608step1 raw32608step1Labels = mixedMoment B raw32608step2 raw32608step2Labels := by
      have ha : raw32608step2 = raw32608step1 := by apply Matrix.ext; unfold raw32608step2 raw32608step1; decide +kernel
      have hl : raw32608step1Labels = labelEmbedding1 ∘ raw32608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32608step1 raw32608step1Labels raw32608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

theorem canonical32609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32609 raw32609Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw32609 raw32609Labels = mixedMoment B raw32609step0 raw32609step0Labels := by
      have ha : raw32609step0 = (fun i j => raw32609 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32609step0 raw32609; decide +kernel
      have hl : raw32609step0Labels = raw32609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32609 raw32609Labels permutation212 permutation5
    mixedMoment B raw32609step0 raw32609step0Labels = mixedMoment B raw32609step1 raw32609step1Labels := by
      have ha : raw32609step1 = -raw32609step0 := by apply Matrix.ext; change ∀ i j, raw32609step1 i j = -(raw32609step0 i j); unfold raw32609step1 raw32609step0; decide +kernel
      have hl : raw32609step1Labels = raw32609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32609step1 raw32609step1Labels = mixedMoment B raw32609step2 raw32609step2Labels := by
      have ha : raw32609step2 = raw32609step1 := by apply Matrix.ext; unfold raw32609step2 raw32609step1; decide +kernel
      have hl : raw32609step1Labels = labelEmbedding1 ∘ raw32609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32609step1 raw32609step1Labels raw32609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical32610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32610 raw32610Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw32610 raw32610Labels = mixedMoment B raw32610step0 raw32610step0Labels := by
      have ha : raw32610step0 = (fun i j => raw32610 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32610step0 raw32610; decide +kernel
      have hl : raw32610step0Labels = raw32610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32610 raw32610Labels permutation234 permutation5
    mixedMoment B raw32610step0 raw32610step0Labels = mixedMoment B raw32610step1 raw32610step1Labels := by
      have ha : raw32610step1 = -raw32610step0 := by apply Matrix.ext; change ∀ i j, raw32610step1 i j = -(raw32610step0 i j); unfold raw32610step1 raw32610step0; decide +kernel
      have hl : raw32610step1Labels = raw32610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32610step1 raw32610step1Labels = mixedMoment B raw32610step2 raw32610step2Labels := by
      have ha : raw32610step2 = raw32610step1 := by apply Matrix.ext; unfold raw32610step2 raw32610step1; decide +kernel
      have hl : raw32610step1Labels = labelEmbedding1 ∘ raw32610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32610step1 raw32610step1Labels raw32610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical32611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32611 raw32611Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw32611 raw32611Labels = mixedMoment B raw32611step0 raw32611step0Labels := by
      have ha : raw32611step0 = (fun i j => raw32611 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32611step0 raw32611; decide +kernel
      have hl : raw32611step0Labels = raw32611Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32611 raw32611Labels permutation216 permutation5
    mixedMoment B raw32611step0 raw32611step0Labels = mixedMoment B raw32611step1 raw32611step1Labels := by
      have ha : raw32611step1 = -raw32611step0 := by apply Matrix.ext; change ∀ i j, raw32611step1 i j = -(raw32611step0 i j); unfold raw32611step1 raw32611step0; decide +kernel
      have hl : raw32611step1Labels = raw32611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32611step1 raw32611step1Labels = mixedMoment B raw32611step2 raw32611step2Labels := by
      have ha : raw32611step2 = raw32611step1 := by apply Matrix.ext; unfold raw32611step2 raw32611step1; decide +kernel
      have hl : raw32611step1Labels = labelEmbedding1 ∘ raw32611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32611step1 raw32611step1Labels raw32611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

theorem canonical32612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32612 raw32612Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw32612 raw32612Labels = mixedMoment B raw32612step0 raw32612step0Labels := by
      have hz : ∀ j, raw32612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32612step0 = (fun i j => raw32612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32612step0 raw32612; decide +kernel
      have hl : raw32612step0Labels = raw32612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32612 raw32612Labels permutation346 hz
    mixedMoment B raw32612step0 raw32612step0Labels = mixedMoment B raw32612step1 raw32612step1Labels := by
      have ha : raw32612step1 = (fun i j => raw32612step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32612step1 raw32612step0; decide +kernel
      have hl : raw32612step1Labels = raw32612step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32612step0 raw32612step0Labels permutation44 permutation5
    mixedMoment B raw32612step1 raw32612step1Labels = mixedMoment B raw32612step2 raw32612step2Labels := by
      have ha : raw32612step2 = -raw32612step1 := by apply Matrix.ext; change ∀ i j, raw32612step2 i j = -(raw32612step1 i j); unfold raw32612step2 raw32612step1; decide +kernel
      have hl : raw32612step2Labels = raw32612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32612step2 raw32612step2Labels = mixedMoment B raw32612step3 raw32612step3Labels := by
      have ha : raw32612step3 = raw32612step2 := by apply Matrix.ext; unfold raw32612step3 raw32612step2; decide +kernel
      have hl : raw32612step2Labels = labelEmbedding1 ∘ raw32612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32612step2 raw32612step2Labels raw32612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical32613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32613 raw32613Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw32613 raw32613Labels = mixedMoment B raw32613step0 raw32613step0Labels := by
      have hz : ∀ j, raw32613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32613step0 = (fun i j => raw32613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32613step0 raw32613; decide +kernel
      have hl : raw32613step0Labels = raw32613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32613 raw32613Labels permutation346 hz
    mixedMoment B raw32613step0 raw32613step0Labels = mixedMoment B raw32613step1 raw32613step1Labels := by
      have ha : raw32613step1 = (fun i j => raw32613step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32613step1 raw32613step0; decide +kernel
      have hl : raw32613step1Labels = raw32613step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32613step0 raw32613step0Labels permutation34 permutation5
    mixedMoment B raw32613step1 raw32613step1Labels = mixedMoment B raw32613step2 raw32613step2Labels := by
      have ha : raw32613step2 = -raw32613step1 := by apply Matrix.ext; change ∀ i j, raw32613step2 i j = -(raw32613step1 i j); unfold raw32613step2 raw32613step1; decide +kernel
      have hl : raw32613step2Labels = raw32613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32613step2 raw32613step2Labels = mixedMoment B raw32613step3 raw32613step3Labels := by
      have ha : raw32613step3 = raw32613step2 := by apply Matrix.ext; unfold raw32613step3 raw32613step2; decide +kernel
      have hl : raw32613step2Labels = labelEmbedding1 ∘ raw32613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32613step2 raw32613step2Labels raw32613step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

theorem canonical32614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32614 raw32614Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw32614 raw32614Labels = mixedMoment B raw32614step0 raw32614step0Labels := by
      have ha : raw32614step0 = (fun i j => raw32614 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32614step0 raw32614; decide +kernel
      have hl : raw32614step0Labels = raw32614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32614 raw32614Labels permutation188 permutation5
    mixedMoment B raw32614step0 raw32614step0Labels = mixedMoment B raw32614step1 raw32614step1Labels := by
      have ha : raw32614step1 = -raw32614step0 := by apply Matrix.ext; change ∀ i j, raw32614step1 i j = -(raw32614step0 i j); unfold raw32614step1 raw32614step0; decide +kernel
      have hl : raw32614step1Labels = raw32614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32614step1 raw32614step1Labels = mixedMoment B raw32614step2 raw32614step2Labels := by
      have ha : raw32614step2 = raw32614step1 := by apply Matrix.ext; unfold raw32614step2 raw32614step1; decide +kernel
      have hl : raw32614step1Labels = labelEmbedding1 ∘ raw32614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32614step1 raw32614step1Labels raw32614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical32615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32615 raw32615Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw32615 raw32615Labels = mixedMoment B raw32615step0 raw32615step0Labels := by
      have hz : ∀ j, raw32615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32615step0 = (fun i j => raw32615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32615step0 raw32615; decide +kernel
      have hl : raw32615step0Labels = raw32615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32615 raw32615Labels permutation346 hz
    mixedMoment B raw32615step0 raw32615step0Labels = mixedMoment B raw32615step1 raw32615step1Labels := by
      have ha : raw32615step1 = (fun i j => raw32615step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32615step1 raw32615step0; decide +kernel
      have hl : raw32615step1Labels = raw32615step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32615step0 raw32615step0Labels permutation44 permutation5
    mixedMoment B raw32615step1 raw32615step1Labels = mixedMoment B raw32615step2 raw32615step2Labels := by
      have ha : raw32615step2 = -raw32615step1 := by apply Matrix.ext; change ∀ i j, raw32615step2 i j = -(raw32615step1 i j); unfold raw32615step2 raw32615step1; decide +kernel
      have hl : raw32615step2Labels = raw32615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32615step2 raw32615step2Labels = mixedMoment B raw32615step3 raw32615step3Labels := by
      have ha : raw32615step3 = raw32615step2 := by apply Matrix.ext; unfold raw32615step3 raw32615step2; decide +kernel
      have hl : raw32615step2Labels = labelEmbedding1 ∘ raw32615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32615step2 raw32615step2Labels raw32615step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical32616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32616 raw32616Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw32616 raw32616Labels = mixedMoment B raw32616step0 raw32616step0Labels := by
      have hz : ∀ j, raw32616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32616step0 = (fun i j => raw32616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32616step0 raw32616; decide +kernel
      have hl : raw32616step0Labels = raw32616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32616 raw32616Labels permutation346 hz
    mixedMoment B raw32616step0 raw32616step0Labels = mixedMoment B raw32616step1 raw32616step1Labels := by
      have ha : raw32616step1 = (fun i j => raw32616step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32616step1 raw32616step0; decide +kernel
      have hl : raw32616step1Labels = raw32616step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32616step0 raw32616step0Labels permutation48 permutation5
    mixedMoment B raw32616step1 raw32616step1Labels = mixedMoment B raw32616step2 raw32616step2Labels := by
      have ha : raw32616step2 = -raw32616step1 := by apply Matrix.ext; change ∀ i j, raw32616step2 i j = -(raw32616step1 i j); unfold raw32616step2 raw32616step1; decide +kernel
      have hl : raw32616step2Labels = raw32616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32616step2 raw32616step2Labels = mixedMoment B raw32616step3 raw32616step3Labels := by
      have ha : raw32616step3 = raw32616step2 := by apply Matrix.ext; unfold raw32616step3 raw32616step2; decide +kernel
      have hl : raw32616step2Labels = labelEmbedding1 ∘ raw32616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32616step2 raw32616step2Labels raw32616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

theorem canonical32617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32617 raw32617Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw32617 raw32617Labels = mixedMoment B raw32617step0 raw32617step0Labels := by
      have hz : ∀ j, raw32617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32617step0 = (fun i j => raw32617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32617step0 raw32617; decide +kernel
      have hl : raw32617step0Labels = raw32617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32617 raw32617Labels permutation346 hz
    mixedMoment B raw32617step0 raw32617step0Labels = mixedMoment B raw32617step1 raw32617step1Labels := by
      have ha : raw32617step1 = (fun i j => raw32617step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32617step1 raw32617step0; decide +kernel
      have hl : raw32617step1Labels = raw32617step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32617step0 raw32617step0Labels permutation38 permutation5
    mixedMoment B raw32617step1 raw32617step1Labels = mixedMoment B raw32617step2 raw32617step2Labels := by
      have ha : raw32617step2 = -raw32617step1 := by apply Matrix.ext; change ∀ i j, raw32617step2 i j = -(raw32617step1 i j); unfold raw32617step2 raw32617step1; decide +kernel
      have hl : raw32617step2Labels = raw32617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32617step2 raw32617step2Labels = mixedMoment B raw32617step3 raw32617step3Labels := by
      have ha : raw32617step3 = raw32617step2 := by apply Matrix.ext; unfold raw32617step3 raw32617step2; decide +kernel
      have hl : raw32617step2Labels = labelEmbedding1 ∘ raw32617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32617step2 raw32617step2Labels raw32617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical32618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32618 raw32618Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw32618 raw32618Labels = mixedMoment B raw32618step0 raw32618step0Labels := by
      have hz : ∀ j, raw32618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32618step0 = (fun i j => raw32618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32618step0 raw32618; decide +kernel
      have hl : raw32618step0Labels = raw32618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32618 raw32618Labels permutation346 hz
    mixedMoment B raw32618step0 raw32618step0Labels = mixedMoment B raw32618step1 raw32618step1Labels := by
      have ha : raw32618step1 = (fun i j => raw32618step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32618step1 raw32618step0; decide +kernel
      have hl : raw32618step1Labels = raw32618step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32618step0 raw32618step0Labels permutation32 permutation5
    mixedMoment B raw32618step1 raw32618step1Labels = mixedMoment B raw32618step2 raw32618step2Labels := by
      have ha : raw32618step2 = -raw32618step1 := by apply Matrix.ext; change ∀ i j, raw32618step2 i j = -(raw32618step1 i j); unfold raw32618step2 raw32618step1; decide +kernel
      have hl : raw32618step2Labels = raw32618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32618step2 raw32618step2Labels = mixedMoment B raw32618step3 raw32618step3Labels := by
      have ha : raw32618step3 = raw32618step2 := by apply Matrix.ext; unfold raw32618step3 raw32618step2; decide +kernel
      have hl : raw32618step2Labels = labelEmbedding1 ∘ raw32618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32618step2 raw32618step2Labels raw32618step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

theorem canonical32619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32619 raw32619Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw32619 raw32619Labels = mixedMoment B raw32619step0 raw32619step0Labels := by
      have ha : raw32619step0 = (fun i j => raw32619 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32619step0 raw32619; decide +kernel
      have hl : raw32619step0Labels = raw32619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32619 raw32619Labels permutation182 permutation5
    mixedMoment B raw32619step0 raw32619step0Labels = mixedMoment B raw32619step1 raw32619step1Labels := by
      have ha : raw32619step1 = -raw32619step0 := by apply Matrix.ext; change ∀ i j, raw32619step1 i j = -(raw32619step0 i j); unfold raw32619step1 raw32619step0; decide +kernel
      have hl : raw32619step1Labels = raw32619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32619step1 raw32619step1Labels = mixedMoment B raw32619step2 raw32619step2Labels := by
      have ha : raw32619step2 = raw32619step1 := by apply Matrix.ext; unfold raw32619step2 raw32619step1; decide +kernel
      have hl : raw32619step1Labels = labelEmbedding1 ∘ raw32619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32619step1 raw32619step1Labels raw32619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

theorem canonical32620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32620 raw32620Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw32620 raw32620Labels = mixedMoment B raw32620step0 raw32620step0Labels := by
      have hz : ∀ j, raw32620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32620step0 = (fun i j => raw32620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32620step0 raw32620; decide +kernel
      have hl : raw32620step0Labels = raw32620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32620 raw32620Labels permutation346 hz
    mixedMoment B raw32620step0 raw32620step0Labels = mixedMoment B raw32620step1 raw32620step1Labels := by
      have ha : raw32620step1 = (fun i j => raw32620step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32620step1 raw32620step0; decide +kernel
      have hl : raw32620step1Labels = raw32620step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32620step0 raw32620step0Labels permutation38 permutation5
    mixedMoment B raw32620step1 raw32620step1Labels = mixedMoment B raw32620step2 raw32620step2Labels := by
      have ha : raw32620step2 = -raw32620step1 := by apply Matrix.ext; change ∀ i j, raw32620step2 i j = -(raw32620step1 i j); unfold raw32620step2 raw32620step1; decide +kernel
      have hl : raw32620step2Labels = raw32620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32620step2 raw32620step2Labels = mixedMoment B raw32620step3 raw32620step3Labels := by
      have ha : raw32620step3 = raw32620step2 := by apply Matrix.ext; unfold raw32620step3 raw32620step2; decide +kernel
      have hl : raw32620step2Labels = labelEmbedding1 ∘ raw32620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32620step2 raw32620step2Labels raw32620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical32621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32621 raw32621Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw32621 raw32621Labels = mixedMoment B raw32621step0 raw32621step0Labels := by
      have hz : ∀ j, raw32621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32621step0 = (fun i j => raw32621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32621step0 raw32621; decide +kernel
      have hl : raw32621step0Labels = raw32621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32621 raw32621Labels permutation346 hz
    mixedMoment B raw32621step0 raw32621step0Labels = mixedMoment B raw32621step1 raw32621step1Labels := by
      have ha : raw32621step1 = (fun i j => raw32621step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32621step1 raw32621step0; decide +kernel
      have hl : raw32621step1Labels = raw32621step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32621step0 raw32621step0Labels permutation42 permutation5
    mixedMoment B raw32621step1 raw32621step1Labels = mixedMoment B raw32621step2 raw32621step2Labels := by
      have ha : raw32621step2 = -raw32621step1 := by apply Matrix.ext; change ∀ i j, raw32621step2 i j = -(raw32621step1 i j); unfold raw32621step2 raw32621step1; decide +kernel
      have hl : raw32621step2Labels = raw32621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32621step2 raw32621step2Labels = mixedMoment B raw32621step3 raw32621step3Labels := by
      have ha : raw32621step3 = raw32621step2 := by apply Matrix.ext; unfold raw32621step3 raw32621step2; decide +kernel
      have hl : raw32621step2Labels = labelEmbedding1 ∘ raw32621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32621step2 raw32621step2Labels raw32621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

theorem canonical32622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32622 raw32622Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw32622 raw32622Labels = mixedMoment B raw32622step0 raw32622step0Labels := by
      have hz : ∀ j, raw32622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32622step0 = (fun i j => raw32622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32622step0 raw32622; decide +kernel
      have hl : raw32622step0Labels = raw32622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32622 raw32622Labels permutation346 hz
    mixedMoment B raw32622step0 raw32622step0Labels = mixedMoment B raw32622step1 raw32622step1Labels := by
      have ha : raw32622step1 = (fun i j => raw32622step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32622step1 raw32622step0; decide +kernel
      have hl : raw32622step1Labels = raw32622step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32622step0 raw32622step0Labels permutation40 permutation5
    mixedMoment B raw32622step1 raw32622step1Labels = mixedMoment B raw32622step2 raw32622step2Labels := by
      have ha : raw32622step2 = -raw32622step1 := by apply Matrix.ext; change ∀ i j, raw32622step2 i j = -(raw32622step1 i j); unfold raw32622step2 raw32622step1; decide +kernel
      have hl : raw32622step2Labels = raw32622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32622step2 raw32622step2Labels = mixedMoment B raw32622step3 raw32622step3Labels := by
      have ha : raw32622step3 = raw32622step2 := by apply Matrix.ext; unfold raw32622step3 raw32622step2; decide +kernel
      have hl : raw32622step2Labels = labelEmbedding1 ∘ raw32622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32622step2 raw32622step2Labels raw32622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical32623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32623 raw32623Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw32623 raw32623Labels = mixedMoment B raw32623step0 raw32623step0Labels := by
      have hz : ∀ j, raw32623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32623step0 = (fun i j => raw32623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32623step0 raw32623; decide +kernel
      have hl : raw32623step0Labels = raw32623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32623 raw32623Labels permutation346 hz
    mixedMoment B raw32623step0 raw32623step0Labels = mixedMoment B raw32623step1 raw32623step1Labels := by
      have ha : raw32623step1 = (fun i j => raw32623step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32623step1 raw32623step0; decide +kernel
      have hl : raw32623step1Labels = raw32623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32623step0 raw32623step0Labels permutation32 permutation5
    mixedMoment B raw32623step1 raw32623step1Labels = mixedMoment B raw32623step2 raw32623step2Labels := by
      have ha : raw32623step2 = -raw32623step1 := by apply Matrix.ext; change ∀ i j, raw32623step2 i j = -(raw32623step1 i j); unfold raw32623step2 raw32623step1; decide +kernel
      have hl : raw32623step2Labels = raw32623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32623step2 raw32623step2Labels = mixedMoment B raw32623step3 raw32623step3Labels := by
      have ha : raw32623step3 = raw32623step2 := by apply Matrix.ext; unfold raw32623step3 raw32623step2; decide +kernel
      have hl : raw32623step2Labels = labelEmbedding1 ∘ raw32623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32623step2 raw32623step2Labels raw32623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

theorem canonical32624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32624 raw32624Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw32624 raw32624Labels = mixedMoment B raw32624step0 raw32624step0Labels := by
      have ha : raw32624step0 = (fun i j => raw32624 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32624step0 raw32624; decide +kernel
      have hl : raw32624step0Labels = raw32624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32624 raw32624Labels permutation184 permutation5
    mixedMoment B raw32624step0 raw32624step0Labels = mixedMoment B raw32624step1 raw32624step1Labels := by
      have ha : raw32624step1 = -raw32624step0 := by apply Matrix.ext; change ∀ i j, raw32624step1 i j = -(raw32624step0 i j); unfold raw32624step1 raw32624step0; decide +kernel
      have hl : raw32624step1Labels = raw32624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32624step1 raw32624step1Labels = mixedMoment B raw32624step2 raw32624step2Labels := by
      have ha : raw32624step2 = raw32624step1 := by apply Matrix.ext; unfold raw32624step2 raw32624step1; decide +kernel
      have hl : raw32624step1Labels = labelEmbedding1 ∘ raw32624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32624step1 raw32624step1Labels raw32624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

theorem canonical32625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32625 raw32625Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32625 raw32625Labels = mixedMoment B raw32625step0 raw32625step0Labels := by
      have hz : ∀ j, raw32625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32625step0 = (fun i j => raw32625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32625step0 raw32625; decide +kernel
      have hl : raw32625step0Labels = raw32625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32625 raw32625Labels permutation346 hz
    mixedMoment B raw32625step0 raw32625step0Labels = mixedMoment B raw32625step1 raw32625step1Labels := by
      have ha : raw32625step1 = (fun i j => raw32625step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32625step1 raw32625step0; decide +kernel
      have hl : raw32625step1Labels = raw32625step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32625step0 raw32625step0Labels permutation40 permutation5
    mixedMoment B raw32625step1 raw32625step1Labels = mixedMoment B raw32625step2 raw32625step2Labels := by
      have ha : raw32625step2 = -raw32625step1 := by apply Matrix.ext; change ∀ i j, raw32625step2 i j = -(raw32625step1 i j); unfold raw32625step2 raw32625step1; decide +kernel
      have hl : raw32625step2Labels = raw32625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32625step2 raw32625step2Labels = mixedMoment B raw32625step3 raw32625step3Labels := by
      have ha : raw32625step3 = raw32625step2 := by apply Matrix.ext; unfold raw32625step3 raw32625step2; decide +kernel
      have hl : raw32625step2Labels = labelEmbedding1 ∘ raw32625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32625step2 raw32625step2Labels raw32625step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical32626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32626 raw32626Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32626 raw32626Labels = mixedMoment B raw32626step0 raw32626step0Labels := by
      have hz : ∀ j, raw32626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32626step0 = (fun i j => raw32626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32626step0 raw32626; decide +kernel
      have hl : raw32626step0Labels = raw32626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32626 raw32626Labels permutation346 hz
    mixedMoment B raw32626step0 raw32626step0Labels = mixedMoment B raw32626step1 raw32626step1Labels := by
      have ha : raw32626step1 = (fun i j => raw32626step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32626step1 raw32626step0; decide +kernel
      have hl : raw32626step1Labels = raw32626step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32626step0 raw32626step0Labels permutation46 permutation5
    mixedMoment B raw32626step1 raw32626step1Labels = mixedMoment B raw32626step2 raw32626step2Labels := by
      have ha : raw32626step2 = -raw32626step1 := by apply Matrix.ext; change ∀ i j, raw32626step2 i j = -(raw32626step1 i j); unfold raw32626step2 raw32626step1; decide +kernel
      have hl : raw32626step2Labels = raw32626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32626step2 raw32626step2Labels = mixedMoment B raw32626step3 raw32626step3Labels := by
      have ha : raw32626step3 = raw32626step2 := by apply Matrix.ext; unfold raw32626step3 raw32626step2; decide +kernel
      have hl : raw32626step2Labels = labelEmbedding1 ∘ raw32626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32626step2 raw32626step2Labels raw32626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical255
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32699 raw32699Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw32699 raw32699Labels = mixedMoment B raw32699step0 raw32699step0Labels := by
      have hz : ∀ j, raw32699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32699step0 = (fun i j => raw32699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32699step0 raw32699; decide +kernel
      have hl : raw32699step0Labels = raw32699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32699 raw32699Labels permutation346 hz
    mixedMoment B raw32699step0 raw32699step0Labels = mixedMoment B raw32699step1 raw32699step1Labels := by
      have ha : raw32699step1 = (fun i j => raw32699step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32699step1 raw32699step0; decide +kernel
      have hl : raw32699step1Labels = raw32699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32699step0 raw32699step0Labels permutation58 permutation7
    mixedMoment B raw32699step1 raw32699step1Labels = mixedMoment B raw32699step2 raw32699step2Labels := by
      have ha : raw32699step2 = -raw32699step1 := by apply Matrix.ext; change ∀ i j, raw32699step2 i j = -(raw32699step1 i j); unfold raw32699step2 raw32699step1; decide +kernel
      have hl : raw32699step2Labels = raw32699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32699step2 raw32699step2Labels = mixedMoment B raw32699step3 raw32699step3Labels := by
      have ha : raw32699step3 = raw32699step2 := by apply Matrix.ext; unfold raw32699step3 raw32699step2; decide +kernel
      have hl : raw32699step2Labels = labelEmbedding1 ∘ raw32699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32699step2 raw32699step2Labels raw32699step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical32700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32700 raw32700Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw32700 raw32700Labels = mixedMoment B raw32700step0 raw32700step0Labels := by
      have ha : raw32700step0 = (fun i j => raw32700 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32700step0 raw32700; decide +kernel
      have hl : raw32700step0Labels = raw32700Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32700 raw32700Labels permutation663 permutation7
    mixedMoment B raw32700step0 raw32700step0Labels = mixedMoment B raw32700step1 raw32700step1Labels := by
      have ha : raw32700step1 = raw32700step0 := by apply Matrix.ext; unfold raw32700step1 raw32700step0; decide +kernel
      have hl : raw32700step0Labels = labelEmbedding1 ∘ raw32700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32700step0 raw32700step0Labels raw32700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical32701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32701 raw32701Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw32701 raw32701Labels = mixedMoment B raw32701step0 raw32701step0Labels := by
      have hz : ∀ j, raw32701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32701step0 = (fun i j => raw32701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32701step0 raw32701; decide +kernel
      have hl : raw32701step0Labels = raw32701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32701 raw32701Labels permutation346 hz
    mixedMoment B raw32701step0 raw32701step0Labels = mixedMoment B raw32701step1 raw32701step1Labels := by
      have ha : raw32701step1 = (fun i j => raw32701step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32701step1 raw32701step0; decide +kernel
      have hl : raw32701step1Labels = raw32701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32701step0 raw32701step0Labels permutation144 permutation7
    mixedMoment B raw32701step1 raw32701step1Labels = mixedMoment B raw32701step2 raw32701step2Labels := by
      have ha : raw32701step2 = raw32701step1 := by apply Matrix.ext; unfold raw32701step2 raw32701step1; decide +kernel
      have hl : raw32701step1Labels = labelEmbedding1 ∘ raw32701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32701step1 raw32701step1Labels raw32701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical32702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32702 raw32702Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw32702 raw32702Labels = mixedMoment B raw32702step0 raw32702step0Labels := by
      have hz : ∀ j, raw32702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32702step0 = (fun i j => raw32702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32702step0 raw32702; decide +kernel
      have hl : raw32702step0Labels = raw32702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32702 raw32702Labels permutation520 hz
    mixedMoment B raw32702step0 raw32702step0Labels = mixedMoment B raw32702step1 raw32702step1Labels := by
      have hz : ∀ j, raw32702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32702step1 = (fun i j => raw32702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32702step1 raw32702step0; decide +kernel
      have hl : raw32702step1Labels = raw32702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32702step0 raw32702step0Labels permutation80 hz
    mixedMoment B raw32702step1 raw32702step1Labels = mixedMoment B raw32702step2 raw32702step2Labels := by
      have ha : raw32702step2 = (fun i j => raw32702step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32702step2 raw32702step1; decide +kernel
      have hl : raw32702step2Labels = raw32702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32702step1 raw32702step1Labels permutation30 permutation7
    mixedMoment B raw32702step2 raw32702step2Labels = mixedMoment B raw32702step3 raw32702step3Labels := by
      have ha : raw32702step3 = raw32702step2 := by apply Matrix.ext; unfold raw32702step3 raw32702step2; decide +kernel
      have hl : raw32702step2Labels = labelEmbedding1 ∘ raw32702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32702step2 raw32702step2Labels raw32702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

theorem canonical32703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32703 raw32703Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw32703 raw32703Labels = mixedMoment B raw32703step0 raw32703step0Labels := by
      have hz : ∀ j, raw32703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32703step0 = (fun i j => raw32703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32703step0 raw32703; decide +kernel
      have hl : raw32703step0Labels = raw32703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32703 raw32703Labels permutation346 hz
    mixedMoment B raw32703step0 raw32703step0Labels = mixedMoment B raw32703step1 raw32703step1Labels := by
      have ha : raw32703step1 = (fun i j => raw32703step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32703step1 raw32703step0; decide +kernel
      have hl : raw32703step1Labels = raw32703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32703step0 raw32703step0Labels permutation58 permutation7
    mixedMoment B raw32703step1 raw32703step1Labels = mixedMoment B raw32703step2 raw32703step2Labels := by
      have ha : raw32703step2 = -raw32703step1 := by apply Matrix.ext; change ∀ i j, raw32703step2 i j = -(raw32703step1 i j); unfold raw32703step2 raw32703step1; decide +kernel
      have hl : raw32703step2Labels = raw32703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32703step2 raw32703step2Labels = mixedMoment B raw32703step3 raw32703step3Labels := by
      have ha : raw32703step3 = raw32703step2 := by apply Matrix.ext; unfold raw32703step3 raw32703step2; decide +kernel
      have hl : raw32703step2Labels = labelEmbedding1 ∘ raw32703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32703step2 raw32703step2Labels raw32703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical32704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32704 raw32704Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw32704 raw32704Labels = mixedMoment B raw32704step0 raw32704step0Labels := by
      have hz : ∀ j, raw32704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32704step0 = (fun i j => raw32704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32704step0 raw32704; decide +kernel
      have hl : raw32704step0Labels = raw32704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32704 raw32704Labels permutation346 hz
    mixedMoment B raw32704step0 raw32704step0Labels = mixedMoment B raw32704step1 raw32704step1Labels := by
      have ha : raw32704step1 = (fun i j => raw32704step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32704step1 raw32704step0; decide +kernel
      have hl : raw32704step1Labels = raw32704step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32704step0 raw32704step0Labels permutation43 permutation5
    mixedMoment B raw32704step1 raw32704step1Labels = mixedMoment B raw32704step2 raw32704step2Labels := by
      have ha : raw32704step2 = -raw32704step1 := by apply Matrix.ext; change ∀ i j, raw32704step2 i j = -(raw32704step1 i j); unfold raw32704step2 raw32704step1; decide +kernel
      have hl : raw32704step2Labels = raw32704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32704step2 raw32704step2Labels = mixedMoment B raw32704step3 raw32704step3Labels := by
      have ha : raw32704step3 = raw32704step2 := by apply Matrix.ext; unfold raw32704step3 raw32704step2; decide +kernel
      have hl : raw32704step2Labels = labelEmbedding1 ∘ raw32704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32704step2 raw32704step2Labels raw32704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical32705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32705 raw32705Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw32705 raw32705Labels = mixedMoment B raw32705step0 raw32705step0Labels := by
      have ha : raw32705step0 = (fun i j => raw32705 (permutation187 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32705step0 raw32705; decide +kernel
      have hl : raw32705step0Labels = raw32705Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32705 raw32705Labels permutation187 permutation5
    mixedMoment B raw32705step0 raw32705step0Labels = mixedMoment B raw32705step1 raw32705step1Labels := by
      have ha : raw32705step1 = -raw32705step0 := by apply Matrix.ext; change ∀ i j, raw32705step1 i j = -(raw32705step0 i j); unfold raw32705step1 raw32705step0; decide +kernel
      have hl : raw32705step1Labels = raw32705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32705step1 raw32705step1Labels = mixedMoment B raw32705step2 raw32705step2Labels := by
      have ha : raw32705step2 = raw32705step1 := by apply Matrix.ext; unfold raw32705step2 raw32705step1; decide +kernel
      have hl : raw32705step1Labels = labelEmbedding1 ∘ raw32705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32705step1 raw32705step1Labels raw32705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical32706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32706 raw32706Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw32706 raw32706Labels = mixedMoment B raw32706step0 raw32706step0Labels := by
      have hz : ∀ j, raw32706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32706step0 = (fun i j => raw32706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32706step0 raw32706; decide +kernel
      have hl : raw32706step0Labels = raw32706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32706 raw32706Labels permutation346 hz
    mixedMoment B raw32706step0 raw32706step0Labels = mixedMoment B raw32706step1 raw32706step1Labels := by
      have ha : raw32706step1 = (fun i j => raw32706step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32706step1 raw32706step0; decide +kernel
      have hl : raw32706step1Labels = raw32706step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32706step0 raw32706step0Labels permutation43 permutation5
    mixedMoment B raw32706step1 raw32706step1Labels = mixedMoment B raw32706step2 raw32706step2Labels := by
      have ha : raw32706step2 = -raw32706step1 := by apply Matrix.ext; change ∀ i j, raw32706step2 i j = -(raw32706step1 i j); unfold raw32706step2 raw32706step1; decide +kernel
      have hl : raw32706step2Labels = raw32706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32706step2 raw32706step2Labels = mixedMoment B raw32706step3 raw32706step3Labels := by
      have ha : raw32706step3 = raw32706step2 := by apply Matrix.ext; unfold raw32706step3 raw32706step2; decide +kernel
      have hl : raw32706step2Labels = labelEmbedding1 ∘ raw32706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32706step2 raw32706step2Labels raw32706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical32707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32707 raw32707Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw32707 raw32707Labels = mixedMoment B raw32707step0 raw32707step0Labels := by
      have hz : ∀ j, raw32707 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32707step0 = (fun i j => raw32707 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32707step0 raw32707; decide +kernel
      have hl : raw32707step0Labels = raw32707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32707 raw32707Labels permutation520 hz
    mixedMoment B raw32707step0 raw32707step0Labels = mixedMoment B raw32707step1 raw32707step1Labels := by
      have hz : ∀ j, raw32707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32707step1 = (fun i j => raw32707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32707step1 raw32707step0; decide +kernel
      have hl : raw32707step1Labels = raw32707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32707step0 raw32707step0Labels permutation80 hz
    mixedMoment B raw32707step1 raw32707step1Labels = mixedMoment B raw32707step2 raw32707step2Labels := by
      have ha : raw32707step2 = (fun i j => raw32707step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32707step2 raw32707step1; decide +kernel
      have hl : raw32707step2Labels = raw32707step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32707step1 raw32707step1Labels permutation11 permutation5
    mixedMoment B raw32707step2 raw32707step2Labels = mixedMoment B raw32707step3 raw32707step3Labels := by
      have ha : raw32707step3 = -raw32707step2 := by apply Matrix.ext; change ∀ i j, raw32707step3 i j = -(raw32707step2 i j); unfold raw32707step3 raw32707step2; decide +kernel
      have hl : raw32707step3Labels = raw32707step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32707step3 raw32707step3Labels = mixedMoment B raw32707step4 raw32707step4Labels := by
      have ha : raw32707step4 = raw32707step3 := by apply Matrix.ext; unfold raw32707step4 raw32707step3; decide +kernel
      have hl : raw32707step3Labels = labelEmbedding1 ∘ raw32707step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32707step3 raw32707step3Labels raw32707step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical32708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32708 raw32708Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw32708 raw32708Labels = mixedMoment B raw32708step0 raw32708step0Labels := by
      have hz : ∀ j, raw32708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32708step0 = (fun i j => raw32708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32708step0 raw32708; decide +kernel
      have hl : raw32708step0Labels = raw32708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32708 raw32708Labels permutation346 hz
    mixedMoment B raw32708step0 raw32708step0Labels = mixedMoment B raw32708step1 raw32708step1Labels := by
      have ha : raw32708step1 = (fun i j => raw32708step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32708step1 raw32708step0; decide +kernel
      have hl : raw32708step1Labels = raw32708step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32708step0 raw32708step0Labels permutation53 permutation5
    mixedMoment B raw32708step1 raw32708step1Labels = mixedMoment B raw32708step2 raw32708step2Labels := by
      have ha : raw32708step2 = -raw32708step1 := by apply Matrix.ext; change ∀ i j, raw32708step2 i j = -(raw32708step1 i j); unfold raw32708step2 raw32708step1; decide +kernel
      have hl : raw32708step2Labels = raw32708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32708step2 raw32708step2Labels = mixedMoment B raw32708step3 raw32708step3Labels := by
      have ha : raw32708step3 = raw32708step2 := by apply Matrix.ext; unfold raw32708step3 raw32708step2; decide +kernel
      have hl : raw32708step2Labels = labelEmbedding1 ∘ raw32708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32708step2 raw32708step2Labels raw32708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical32709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32709 raw32709Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw32709 raw32709Labels = mixedMoment B raw32709step0 raw32709step0Labels := by
      have ha : raw32709step0 = (fun i j => raw32709 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32709step0 raw32709; decide +kernel
      have hl : raw32709step0Labels = raw32709Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32709 raw32709Labels permutation218 permutation5
    mixedMoment B raw32709step0 raw32709step0Labels = mixedMoment B raw32709step1 raw32709step1Labels := by
      have ha : raw32709step1 = -raw32709step0 := by apply Matrix.ext; change ∀ i j, raw32709step1 i j = -(raw32709step0 i j); unfold raw32709step1 raw32709step0; decide +kernel
      have hl : raw32709step1Labels = raw32709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32709step1 raw32709step1Labels = mixedMoment B raw32709step2 raw32709step2Labels := by
      have ha : raw32709step2 = raw32709step1 := by apply Matrix.ext; unfold raw32709step2 raw32709step1; decide +kernel
      have hl : raw32709step1Labels = labelEmbedding1 ∘ raw32709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32709step1 raw32709step1Labels raw32709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical32710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32710 raw32710Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw32710 raw32710Labels = mixedMoment B raw32710step0 raw32710step0Labels := by
      have ha : raw32710step0 = (fun i j => raw32710 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32710step0 raw32710; decide +kernel
      have hl : raw32710step0Labels = raw32710Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32710 raw32710Labels permutation162 permutation5
    mixedMoment B raw32710step0 raw32710step0Labels = mixedMoment B raw32710step1 raw32710step1Labels := by
      have ha : raw32710step1 = -raw32710step0 := by apply Matrix.ext; change ∀ i j, raw32710step1 i j = -(raw32710step0 i j); unfold raw32710step1 raw32710step0; decide +kernel
      have hl : raw32710step1Labels = raw32710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32710step1 raw32710step1Labels = mixedMoment B raw32710step2 raw32710step2Labels := by
      have ha : raw32710step2 = raw32710step1 := by apply Matrix.ext; unfold raw32710step2 raw32710step1; decide +kernel
      have hl : raw32710step1Labels = labelEmbedding1 ∘ raw32710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32710step1 raw32710step1Labels raw32710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

theorem canonical32711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32711 raw32711Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw32711 raw32711Labels = mixedMoment B raw32711step0 raw32711step0Labels := by
      have ha : raw32711step0 = (fun i j => raw32711 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32711step0 raw32711; decide +kernel
      have hl : raw32711step0Labels = raw32711Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32711 raw32711Labels permutation218 permutation5
    mixedMoment B raw32711step0 raw32711step0Labels = mixedMoment B raw32711step1 raw32711step1Labels := by
      have ha : raw32711step1 = -raw32711step0 := by apply Matrix.ext; change ∀ i j, raw32711step1 i j = -(raw32711step0 i j); unfold raw32711step1 raw32711step0; decide +kernel
      have hl : raw32711step1Labels = raw32711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32711step1 raw32711step1Labels = mixedMoment B raw32711step2 raw32711step2Labels := by
      have ha : raw32711step2 = raw32711step1 := by apply Matrix.ext; unfold raw32711step2 raw32711step1; decide +kernel
      have hl : raw32711step1Labels = labelEmbedding1 ∘ raw32711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32711step1 raw32711step1Labels raw32711step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical32712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32712 raw32712Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw32712 raw32712Labels = mixedMoment B raw32712step0 raw32712step0Labels := by
      have hz : ∀ j, raw32712 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32712step0 = (fun i j => raw32712 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32712step0 raw32712; decide +kernel
      have hl : raw32712step0Labels = raw32712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32712 raw32712Labels permutation520 hz
    mixedMoment B raw32712step0 raw32712step0Labels = mixedMoment B raw32712step1 raw32712step1Labels := by
      have ha : raw32712step1 = (fun i j => raw32712step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32712step1 raw32712step0; decide +kernel
      have hl : raw32712step1Labels = raw32712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32712step0 raw32712step0Labels permutation48 permutation5
    mixedMoment B raw32712step1 raw32712step1Labels = mixedMoment B raw32712step2 raw32712step2Labels := by
      have ha : raw32712step2 = -raw32712step1 := by apply Matrix.ext; change ∀ i j, raw32712step2 i j = -(raw32712step1 i j); unfold raw32712step2 raw32712step1; decide +kernel
      have hl : raw32712step2Labels = raw32712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32712step2 raw32712step2Labels = mixedMoment B raw32712step3 raw32712step3Labels := by
      have ha : raw32712step3 = raw32712step2 := by apply Matrix.ext; unfold raw32712step3 raw32712step2; decide +kernel
      have hl : raw32712step2Labels = labelEmbedding1 ∘ raw32712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32712step2 raw32712step2Labels raw32712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

theorem canonical32713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32713 raw32713Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw32713 raw32713Labels = mixedMoment B raw32713step0 raw32713step0Labels := by
      have ha : raw32713step0 = (fun i j => raw32713 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32713step0 raw32713; decide +kernel
      have hl : raw32713step0Labels = raw32713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32713 raw32713Labels permutation257 permutation5
    mixedMoment B raw32713step0 raw32713step0Labels = mixedMoment B raw32713step1 raw32713step1Labels := by
      have ha : raw32713step1 = -raw32713step0 := by apply Matrix.ext; change ∀ i j, raw32713step1 i j = -(raw32713step0 i j); unfold raw32713step1 raw32713step0; decide +kernel
      have hl : raw32713step1Labels = raw32713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32713step1 raw32713step1Labels = mixedMoment B raw32713step2 raw32713step2Labels := by
      have ha : raw32713step2 = raw32713step1 := by apply Matrix.ext; unfold raw32713step2 raw32713step1; decide +kernel
      have hl : raw32713step1Labels = labelEmbedding1 ∘ raw32713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32713step1 raw32713step1Labels raw32713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

theorem canonical32714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32714 raw32714Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw32714 raw32714Labels = mixedMoment B raw32714step0 raw32714step0Labels := by
      have hz : ∀ j, raw32714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32714step0 = (fun i j => raw32714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32714step0 raw32714; decide +kernel
      have hl : raw32714step0Labels = raw32714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32714 raw32714Labels permutation346 hz
    mixedMoment B raw32714step0 raw32714step0Labels = mixedMoment B raw32714step1 raw32714step1Labels := by
      have ha : raw32714step1 = (fun i j => raw32714step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32714step1 raw32714step0; decide +kernel
      have hl : raw32714step1Labels = raw32714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32714step0 raw32714step0Labels permutation51 permutation5
    mixedMoment B raw32714step1 raw32714step1Labels = mixedMoment B raw32714step2 raw32714step2Labels := by
      have ha : raw32714step2 = -raw32714step1 := by apply Matrix.ext; change ∀ i j, raw32714step2 i j = -(raw32714step1 i j); unfold raw32714step2 raw32714step1; decide +kernel
      have hl : raw32714step2Labels = raw32714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32714step2 raw32714step2Labels = mixedMoment B raw32714step3 raw32714step3Labels := by
      have ha : raw32714step3 = raw32714step2 := by apply Matrix.ext; unfold raw32714step3 raw32714step2; decide +kernel
      have hl : raw32714step2Labels = labelEmbedding1 ∘ raw32714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32714step2 raw32714step2Labels raw32714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical32715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32715 raw32715Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw32715 raw32715Labels = mixedMoment B raw32715step0 raw32715step0Labels := by
      have hz : ∀ j, raw32715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32715step0 = (fun i j => raw32715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32715step0 raw32715; decide +kernel
      have hl : raw32715step0Labels = raw32715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32715 raw32715Labels permutation346 hz
    mixedMoment B raw32715step0 raw32715step0Labels = mixedMoment B raw32715step1 raw32715step1Labels := by
      have ha : raw32715step1 = (fun i j => raw32715step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32715step1 raw32715step0; decide +kernel
      have hl : raw32715step1Labels = raw32715step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32715step0 raw32715step0Labels permutation37 permutation5
    mixedMoment B raw32715step1 raw32715step1Labels = mixedMoment B raw32715step2 raw32715step2Labels := by
      have ha : raw32715step2 = -raw32715step1 := by apply Matrix.ext; change ∀ i j, raw32715step2 i j = -(raw32715step1 i j); unfold raw32715step2 raw32715step1; decide +kernel
      have hl : raw32715step2Labels = raw32715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32715step2 raw32715step2Labels = mixedMoment B raw32715step3 raw32715step3Labels := by
      have ha : raw32715step3 = raw32715step2 := by apply Matrix.ext; unfold raw32715step3 raw32715step2; decide +kernel
      have hl : raw32715step2Labels = labelEmbedding1 ∘ raw32715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32715step2 raw32715step2Labels raw32715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical32716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32716 raw32716Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw32716 raw32716Labels = mixedMoment B raw32716step0 raw32716step0Labels := by
      have ha : raw32716step0 = (fun i j => raw32716 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32716step0 raw32716; decide +kernel
      have hl : raw32716step0Labels = raw32716Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32716 raw32716Labels permutation195 permutation5
    mixedMoment B raw32716step0 raw32716step0Labels = mixedMoment B raw32716step1 raw32716step1Labels := by
      have ha : raw32716step1 = -raw32716step0 := by apply Matrix.ext; change ∀ i j, raw32716step1 i j = -(raw32716step0 i j); unfold raw32716step1 raw32716step0; decide +kernel
      have hl : raw32716step1Labels = raw32716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32716step1 raw32716step1Labels = mixedMoment B raw32716step2 raw32716step2Labels := by
      have ha : raw32716step2 = raw32716step1 := by apply Matrix.ext; unfold raw32716step2 raw32716step1; decide +kernel
      have hl : raw32716step1Labels = labelEmbedding1 ∘ raw32716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32716step1 raw32716step1Labels raw32716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

theorem canonical32717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32717 raw32717Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw32717 raw32717Labels = mixedMoment B raw32717step0 raw32717step0Labels := by
      have hz : ∀ j, raw32717 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32717step0 = (fun i j => raw32717 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32717step0 raw32717; decide +kernel
      have hl : raw32717step0Labels = raw32717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32717 raw32717Labels permutation520 hz
    mixedMoment B raw32717step0 raw32717step0Labels = mixedMoment B raw32717step1 raw32717step1Labels := by
      have hz : ∀ j, raw32717step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32717step1 = (fun i j => raw32717step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32717step1 raw32717step0; decide +kernel
      have hl : raw32717step1Labels = raw32717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32717step0 raw32717step0Labels permutation80 hz
    mixedMoment B raw32717step1 raw32717step1Labels = mixedMoment B raw32717step2 raw32717step2Labels := by
      have ha : raw32717step2 = (fun i j => raw32717step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32717step2 raw32717step1; decide +kernel
      have hl : raw32717step2Labels = raw32717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32717step1 raw32717step1Labels permutation12 permutation5
    mixedMoment B raw32717step2 raw32717step2Labels = mixedMoment B raw32717step3 raw32717step3Labels := by
      have ha : raw32717step3 = -raw32717step2 := by apply Matrix.ext; change ∀ i j, raw32717step3 i j = -(raw32717step2 i j); unfold raw32717step3 raw32717step2; decide +kernel
      have hl : raw32717step3Labels = raw32717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32717step3 raw32717step3Labels = mixedMoment B raw32717step4 raw32717step4Labels := by
      have ha : raw32717step4 = raw32717step3 := by apply Matrix.ext; unfold raw32717step4 raw32717step3; decide +kernel
      have hl : raw32717step3Labels = labelEmbedding1 ∘ raw32717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32717step3 raw32717step3Labels raw32717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

theorem canonical32718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32718 raw32718Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw32718 raw32718Labels = mixedMoment B raw32718step0 raw32718step0Labels := by
      have hz : ∀ j, raw32718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32718step0 = (fun i j => raw32718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32718step0 raw32718; decide +kernel
      have hl : raw32718step0Labels = raw32718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32718 raw32718Labels permutation346 hz
    mixedMoment B raw32718step0 raw32718step0Labels = mixedMoment B raw32718step1 raw32718step1Labels := by
      have ha : raw32718step1 = (fun i j => raw32718step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32718step1 raw32718step0; decide +kernel
      have hl : raw32718step1Labels = raw32718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32718step0 raw32718step0Labels permutation51 permutation5
    mixedMoment B raw32718step1 raw32718step1Labels = mixedMoment B raw32718step2 raw32718step2Labels := by
      have ha : raw32718step2 = -raw32718step1 := by apply Matrix.ext; change ∀ i j, raw32718step2 i j = -(raw32718step1 i j); unfold raw32718step2 raw32718step1; decide +kernel
      have hl : raw32718step2Labels = raw32718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32718step2 raw32718step2Labels = mixedMoment B raw32718step3 raw32718step3Labels := by
      have ha : raw32718step3 = raw32718step2 := by apply Matrix.ext; unfold raw32718step3 raw32718step2; decide +kernel
      have hl : raw32718step2Labels = labelEmbedding1 ∘ raw32718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32718step2 raw32718step2Labels raw32718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical32719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32719 raw32719Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw32719 raw32719Labels = mixedMoment B raw32719step0 raw32719step0Labels := by
      have hz : ∀ j, raw32719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32719step0 = (fun i j => raw32719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32719step0 raw32719; decide +kernel
      have hl : raw32719step0Labels = raw32719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32719 raw32719Labels permutation346 hz
    mixedMoment B raw32719step0 raw32719step0Labels = mixedMoment B raw32719step1 raw32719step1Labels := by
      have ha : raw32719step1 = (fun i j => raw32719step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32719step1 raw32719step0; decide +kernel
      have hl : raw32719step1Labels = raw32719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32719step0 raw32719step0Labels permutation42 permutation5
    mixedMoment B raw32719step1 raw32719step1Labels = mixedMoment B raw32719step2 raw32719step2Labels := by
      have ha : raw32719step2 = -raw32719step1 := by apply Matrix.ext; change ∀ i j, raw32719step2 i j = -(raw32719step1 i j); unfold raw32719step2 raw32719step1; decide +kernel
      have hl : raw32719step2Labels = raw32719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32719step2 raw32719step2Labels = mixedMoment B raw32719step3 raw32719step3Labels := by
      have ha : raw32719step3 = raw32719step2 := by apply Matrix.ext; unfold raw32719step3 raw32719step2; decide +kernel
      have hl : raw32719step2Labels = labelEmbedding1 ∘ raw32719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32719step2 raw32719step2Labels raw32719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical32720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32720 raw32720Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw32720 raw32720Labels = mixedMoment B raw32720step0 raw32720step0Labels := by
      have hz : ∀ j, raw32720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32720step0 = (fun i j => raw32720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32720step0 raw32720; decide +kernel
      have hl : raw32720step0Labels = raw32720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32720 raw32720Labels permutation346 hz
    mixedMoment B raw32720step0 raw32720step0Labels = mixedMoment B raw32720step1 raw32720step1Labels := by
      have ha : raw32720step1 = (fun i j => raw32720step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32720step1 raw32720step0; decide +kernel
      have hl : raw32720step1Labels = raw32720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32720step0 raw32720step0Labels permutation33 permutation5
    mixedMoment B raw32720step1 raw32720step1Labels = mixedMoment B raw32720step2 raw32720step2Labels := by
      have ha : raw32720step2 = -raw32720step1 := by apply Matrix.ext; change ∀ i j, raw32720step2 i j = -(raw32720step1 i j); unfold raw32720step2 raw32720step1; decide +kernel
      have hl : raw32720step2Labels = raw32720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32720step2 raw32720step2Labels = mixedMoment B raw32720step3 raw32720step3Labels := by
      have ha : raw32720step3 = raw32720step2 := by apply Matrix.ext; unfold raw32720step3 raw32720step2; decide +kernel
      have hl : raw32720step2Labels = labelEmbedding1 ∘ raw32720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32720step2 raw32720step2Labels raw32720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

theorem canonical32721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32721 raw32721Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw32721 raw32721Labels = mixedMoment B raw32721step0 raw32721step0Labels := by
      have ha : raw32721step0 = (fun i j => raw32721 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32721step0 raw32721; decide +kernel
      have hl : raw32721step0Labels = raw32721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32721 raw32721Labels permutation186 permutation5
    mixedMoment B raw32721step0 raw32721step0Labels = mixedMoment B raw32721step1 raw32721step1Labels := by
      have ha : raw32721step1 = -raw32721step0 := by apply Matrix.ext; change ∀ i j, raw32721step1 i j = -(raw32721step0 i j); unfold raw32721step1 raw32721step0; decide +kernel
      have hl : raw32721step1Labels = raw32721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32721step1 raw32721step1Labels = mixedMoment B raw32721step2 raw32721step2Labels := by
      have ha : raw32721step2 = raw32721step1 := by apply Matrix.ext; unfold raw32721step2 raw32721step1; decide +kernel
      have hl : raw32721step1Labels = labelEmbedding1 ∘ raw32721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32721step1 raw32721step1Labels raw32721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

theorem canonical32722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32722 raw32722Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw32722 raw32722Labels = mixedMoment B raw32722step0 raw32722step0Labels := by
      have hz : ∀ j, raw32722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32722step0 = (fun i j => raw32722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32722step0 raw32722; decide +kernel
      have hl : raw32722step0Labels = raw32722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32722 raw32722Labels permutation346 hz
    mixedMoment B raw32722step0 raw32722step0Labels = mixedMoment B raw32722step1 raw32722step1Labels := by
      have ha : raw32722step1 = (fun i j => raw32722step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32722step1 raw32722step0; decide +kernel
      have hl : raw32722step1Labels = raw32722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32722step0 raw32722step0Labels permutation42 permutation5
    mixedMoment B raw32722step1 raw32722step1Labels = mixedMoment B raw32722step2 raw32722step2Labels := by
      have ha : raw32722step2 = -raw32722step1 := by apply Matrix.ext; change ∀ i j, raw32722step2 i j = -(raw32722step1 i j); unfold raw32722step2 raw32722step1; decide +kernel
      have hl : raw32722step2Labels = raw32722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32722step2 raw32722step2Labels = mixedMoment B raw32722step3 raw32722step3Labels := by
      have ha : raw32722step3 = raw32722step2 := by apply Matrix.ext; unfold raw32722step3 raw32722step2; decide +kernel
      have hl : raw32722step2Labels = labelEmbedding1 ∘ raw32722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32722step2 raw32722step2Labels raw32722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical32723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32723 raw32723Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw32723 raw32723Labels = mixedMoment B raw32723step0 raw32723step0Labels := by
      have hz : ∀ j, raw32723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32723step0 = (fun i j => raw32723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32723step0 raw32723; decide +kernel
      have hl : raw32723step0Labels = raw32723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32723 raw32723Labels permutation346 hz
    mixedMoment B raw32723step0 raw32723step0Labels = mixedMoment B raw32723step1 raw32723step1Labels := by
      have ha : raw32723step1 = (fun i j => raw32723step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32723step1 raw32723step0; decide +kernel
      have hl : raw32723step1Labels = raw32723step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32723step0 raw32723step0Labels permutation52 permutation5
    mixedMoment B raw32723step1 raw32723step1Labels = mixedMoment B raw32723step2 raw32723step2Labels := by
      have ha : raw32723step2 = -raw32723step1 := by apply Matrix.ext; change ∀ i j, raw32723step2 i j = -(raw32723step1 i j); unfold raw32723step2 raw32723step1; decide +kernel
      have hl : raw32723step2Labels = raw32723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32723step2 raw32723step2Labels = mixedMoment B raw32723step3 raw32723step3Labels := by
      have ha : raw32723step3 = raw32723step2 := by apply Matrix.ext; unfold raw32723step3 raw32723step2; decide +kernel
      have hl : raw32723step2Labels = labelEmbedding1 ∘ raw32723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32723step2 raw32723step2Labels raw32723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical32724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32724 raw32724Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw32724 raw32724Labels = mixedMoment B raw32724step0 raw32724step0Labels := by
      have hz : ∀ j, raw32724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32724step0 = (fun i j => raw32724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32724step0 raw32724; decide +kernel
      have hl : raw32724step0Labels = raw32724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32724 raw32724Labels permutation346 hz
    mixedMoment B raw32724step0 raw32724step0Labels = mixedMoment B raw32724step1 raw32724step1Labels := by
      have ha : raw32724step1 = (fun i j => raw32724step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32724step1 raw32724step0; decide +kernel
      have hl : raw32724step1Labels = raw32724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32724step0 raw32724step0Labels permutation38 permutation5
    mixedMoment B raw32724step1 raw32724step1Labels = mixedMoment B raw32724step2 raw32724step2Labels := by
      have ha : raw32724step2 = -raw32724step1 := by apply Matrix.ext; change ∀ i j, raw32724step2 i j = -(raw32724step1 i j); unfold raw32724step2 raw32724step1; decide +kernel
      have hl : raw32724step2Labels = raw32724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32724step2 raw32724step2Labels = mixedMoment B raw32724step3 raw32724step3Labels := by
      have ha : raw32724step3 = raw32724step2 := by apply Matrix.ext; unfold raw32724step3 raw32724step2; decide +kernel
      have hl : raw32724step2Labels = labelEmbedding1 ∘ raw32724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32724step2 raw32724step2Labels raw32724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical32725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32725 raw32725Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw32725 raw32725Labels = mixedMoment B raw32725step0 raw32725step0Labels := by
      have hz : ∀ j, raw32725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32725step0 = (fun i j => raw32725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32725step0 raw32725; decide +kernel
      have hl : raw32725step0Labels = raw32725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32725 raw32725Labels permutation346 hz
    mixedMoment B raw32725step0 raw32725step0Labels = mixedMoment B raw32725step1 raw32725step1Labels := by
      have ha : raw32725step1 = (fun i j => raw32725step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32725step1 raw32725step0; decide +kernel
      have hl : raw32725step1Labels = raw32725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32725step0 raw32725step0Labels permutation144 permutation7
    mixedMoment B raw32725step1 raw32725step1Labels = mixedMoment B raw32725step2 raw32725step2Labels := by
      have ha : raw32725step2 = raw32725step1 := by apply Matrix.ext; unfold raw32725step2 raw32725step1; decide +kernel
      have hl : raw32725step1Labels = labelEmbedding1 ∘ raw32725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32725step1 raw32725step1Labels raw32725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

theorem canonical32726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32726 raw32726Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw32726 raw32726Labels = mixedMoment B raw32726step0 raw32726step0Labels := by
      have ha : raw32726step0 = (fun i j => raw32726 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32726step0 raw32726; decide +kernel
      have hl : raw32726step0Labels = raw32726Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32726 raw32726Labels permutation663 permutation7
    mixedMoment B raw32726step0 raw32726step0Labels = mixedMoment B raw32726step1 raw32726step1Labels := by
      have ha : raw32726step1 = raw32726step0 := by apply Matrix.ext; unfold raw32726step1 raw32726step0; decide +kernel
      have hl : raw32726step0Labels = labelEmbedding1 ∘ raw32726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32726step0 raw32726step0Labels raw32726step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical32727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32727 raw32727Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw32727 raw32727Labels = mixedMoment B raw32727step0 raw32727step0Labels := by
      have hz : ∀ j, raw32727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32727step0 = (fun i j => raw32727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32727step0 raw32727; decide +kernel
      have hl : raw32727step0Labels = raw32727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32727 raw32727Labels permutation346 hz
    mixedMoment B raw32727step0 raw32727step0Labels = mixedMoment B raw32727step1 raw32727step1Labels := by
      have ha : raw32727step1 = (fun i j => raw32727step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32727step1 raw32727step0; decide +kernel
      have hl : raw32727step1Labels = raw32727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32727step0 raw32727step0Labels permutation144 permutation7
    mixedMoment B raw32727step1 raw32727step1Labels = mixedMoment B raw32727step2 raw32727step2Labels := by
      have ha : raw32727step2 = raw32727step1 := by apply Matrix.ext; unfold raw32727step2 raw32727step1; decide +kernel
      have hl : raw32727step1Labels = labelEmbedding1 ∘ raw32727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32727step1 raw32727step1Labels raw32727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical32728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32728 raw32728Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw32728 raw32728Labels = mixedMoment B raw32728step0 raw32728step0Labels := by
      have hz : ∀ j, raw32728 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32728step0 = (fun i j => raw32728 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32728step0 raw32728; decide +kernel
      have hl : raw32728step0Labels = raw32728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32728 raw32728Labels permutation520 hz
    mixedMoment B raw32728step0 raw32728step0Labels = mixedMoment B raw32728step1 raw32728step1Labels := by
      have hz : ∀ j, raw32728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32728step1 = (fun i j => raw32728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32728step1 raw32728step0; decide +kernel
      have hl : raw32728step1Labels = raw32728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32728step0 raw32728step0Labels permutation80 hz
    mixedMoment B raw32728step1 raw32728step1Labels = mixedMoment B raw32728step2 raw32728step2Labels := by
      have ha : raw32728step2 = (fun i j => raw32728step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32728step2 raw32728step1; decide +kernel
      have hl : raw32728step2Labels = raw32728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32728step1 raw32728step1Labels permutation30 permutation7
    mixedMoment B raw32728step2 raw32728step2Labels = mixedMoment B raw32728step3 raw32728step3Labels := by
      have ha : raw32728step3 = raw32728step2 := by apply Matrix.ext; unfold raw32728step3 raw32728step2; decide +kernel
      have hl : raw32728step2Labels = labelEmbedding1 ∘ raw32728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32728step2 raw32728step2Labels raw32728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

theorem canonical32729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32729 raw32729Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw32729 raw32729Labels = mixedMoment B raw32729step0 raw32729step0Labels := by
      have hz : ∀ j, raw32729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32729step0 = (fun i j => raw32729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32729step0 raw32729; decide +kernel
      have hl : raw32729step0Labels = raw32729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32729 raw32729Labels permutation346 hz
    mixedMoment B raw32729step0 raw32729step0Labels = mixedMoment B raw32729step1 raw32729step1Labels := by
      have ha : raw32729step1 = (fun i j => raw32729step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32729step1 raw32729step0; decide +kernel
      have hl : raw32729step1Labels = raw32729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32729step0 raw32729step0Labels permutation144 permutation2
    mixedMoment B raw32729step1 raw32729step1Labels = mixedMoment B raw32729step2 raw32729step2Labels := by
      have ha : raw32729step2 = -raw32729step1 := by apply Matrix.ext; change ∀ i j, raw32729step2 i j = -(raw32729step1 i j); unfold raw32729step2 raw32729step1; decide +kernel
      have hl : raw32729step2Labels = raw32729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

theorem canonical32730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32730 raw32730Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw32730 raw32730Labels = mixedMoment B raw32730step0 raw32730step0Labels := by
      have hz : ∀ j, raw32730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32730step0 = (fun i j => raw32730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32730step0 raw32730; decide +kernel
      have hl : raw32730step0Labels = raw32730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32730 raw32730Labels permutation346 hz
    _ = mixedMoment B node2879 node2879Labels := by rfl

theorem canonical32731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32731 raw32731Labels = mixedMoment B node2806 node2806Labels := by
  calc
    _ = mixedMoment B node2806 node2806Labels := by rfl

theorem canonical32732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32732 raw32732Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw32732 raw32732Labels = mixedMoment B raw32732step0 raw32732step0Labels := by
      have hz : ∀ j, raw32732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32732step0 = (fun i j => raw32732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32732step0 raw32732; decide +kernel
      have hl : raw32732step0Labels = raw32732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32732 raw32732Labels permutation346 hz
    mixedMoment B raw32732step0 raw32732step0Labels = mixedMoment B raw32732step1 raw32732step1Labels := by
      have ha : raw32732step1 = (fun i j => raw32732step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32732step1 raw32732step0; decide +kernel
      have hl : raw32732step1Labels = raw32732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32732step0 raw32732step0Labels permutation34 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

theorem canonical32733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32733 raw32733Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw32733 raw32733Labels = mixedMoment B raw32733step0 raw32733step0Labels := by
      have hz : ∀ j, raw32733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32733step0 = (fun i j => raw32733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32733step0 raw32733; decide +kernel
      have hl : raw32733step0Labels = raw32733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32733 raw32733Labels permutation346 hz
    _ = mixedMoment B node2812 node2812Labels := by rfl

theorem canonical32739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32739 raw32739Labels = mixedMoment B node3067 node3067Labels := by
  calc
    mixedMoment B raw32739 raw32739Labels = mixedMoment B raw32739step0 raw32739step0Labels := by
      have ha : raw32739step0 = (fun i j => raw32739 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32739step0 raw32739; decide +kernel
      have hl : raw32739step0Labels = raw32739Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32739 raw32739Labels permutation314 permutation4
    mixedMoment B raw32739step0 raw32739step0Labels = mixedMoment B raw32739step1 raw32739step1Labels := by
      have ha : raw32739step1 = -raw32739step0 := by apply Matrix.ext; change ∀ i j, raw32739step1 i j = -(raw32739step0 i j); unfold raw32739step1 raw32739step0; decide +kernel
      have hl : raw32739step1Labels = raw32739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3067 node3067Labels := by rfl

theorem canonical32740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32740 raw32740Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw32740 raw32740Labels = mixedMoment B raw32740step0 raw32740step0Labels := by
      have ha : raw32740step0 = (fun i j => raw32740 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32740step0 raw32740; decide +kernel
      have hl : raw32740step0Labels = raw32740Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32740 raw32740Labels permutation176 permutation2
    _ = mixedMoment B node3751 node3751Labels := by rfl

theorem canonical32741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32741 raw32741Labels = mixedMoment B node3866 node3866Labels := by
  calc
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical32742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32742 raw32742Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw32742 raw32742Labels = mixedMoment B raw32742step0 raw32742step0Labels := by
      have ha : raw32742step0 = (fun i j => raw32742 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32742step0 raw32742; decide +kernel
      have hl : raw32742step0Labels = raw32742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32742 raw32742Labels permutation154 permutation2
    _ = mixedMoment B node3866 node3866Labels := by rfl

theorem canonical32743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32743 raw32743Labels = mixedMoment B node3867 node3867Labels := by
  calc
    _ = mixedMoment B node3867 node3867Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32788 raw32788Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw32788 raw32788Labels = mixedMoment B raw32788step0 raw32788step0Labels := by
      have hz : ∀ j, raw32788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32788step0 = (fun i j => raw32788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32788step0 raw32788; decide +kernel
      have hl : raw32788step0Labels = raw32788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32788 raw32788Labels permutation346 hz
    mixedMoment B raw32788step0 raw32788step0Labels = mixedMoment B raw32788step1 raw32788step1Labels := by
      have ha : raw32788step1 = (fun i j => raw32788step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32788step1 raw32788step0; decide +kernel
      have hl : raw32788step1Labels = raw32788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32788step0 raw32788step0Labels permutation34 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical32789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32789 raw32789Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32789 raw32789Labels = mixedMoment B raw32789step0 raw32789step0Labels := by
      have ha : raw32789step0 = (fun i j => raw32789 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32789step0 raw32789; decide +kernel
      have hl : raw32789step0Labels = raw32789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32789 raw32789Labels permutation164 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

theorem canonical32790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32790 raw32790Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw32790 raw32790Labels = mixedMoment B raw32790step0 raw32790step0Labels := by
      have hz : ∀ j, raw32790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32790step0 = (fun i j => raw32790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32790step0 raw32790; decide +kernel
      have hl : raw32790step0Labels = raw32790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32790 raw32790Labels permutation346 hz
    mixedMoment B raw32790step0 raw32790step0Labels = mixedMoment B raw32790step1 raw32790step1Labels := by
      have ha : raw32790step1 = (fun i j => raw32790step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32790step1 raw32790step0; decide +kernel
      have hl : raw32790step1Labels = raw32790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32790step0 raw32790step0Labels permutation34 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

theorem canonical32856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32856 raw32856Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw32856 raw32856Labels = mixedMoment B raw32856step0 raw32856step0Labels := by
      have ha : raw32856step0 = (fun i j => raw32856 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32856step0 raw32856; decide +kernel
      have hl : raw32856step0Labels = raw32856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32856 raw32856Labels permutation176 permutation7
    mixedMoment B raw32856step0 raw32856step0Labels = mixedMoment B raw32856step1 raw32856step1Labels := by
      have ha : raw32856step1 = -raw32856step0 := by apply Matrix.ext; change ∀ i j, raw32856step1 i j = -(raw32856step0 i j); unfold raw32856step1 raw32856step0; decide +kernel
      have hl : raw32856step1Labels = raw32856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32856step1 raw32856step1Labels = mixedMoment B raw32856step2 raw32856step2Labels := by
      have ha : raw32856step2 = raw32856step1 := by apply Matrix.ext; unfold raw32856step2 raw32856step1; decide +kernel
      have hl : raw32856step1Labels = labelEmbedding1 ∘ raw32856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32856step1 raw32856step1Labels raw32856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical32857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32857 raw32857Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw32857 raw32857Labels = mixedMoment B raw32857step0 raw32857step0Labels := by
      have ha : raw32857step0 = (fun i j => raw32857 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32857step0 raw32857; decide +kernel
      have hl : raw32857step0Labels = raw32857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32857 raw32857Labels permutation176 permutation7
    mixedMoment B raw32857step0 raw32857step0Labels = mixedMoment B raw32857step1 raw32857step1Labels := by
      have ha : raw32857step1 = -raw32857step0 := by apply Matrix.ext; change ∀ i j, raw32857step1 i j = -(raw32857step0 i j); unfold raw32857step1 raw32857step0; decide +kernel
      have hl : raw32857step1Labels = raw32857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32857step1 raw32857step1Labels = mixedMoment B raw32857step2 raw32857step2Labels := by
      have ha : raw32857step2 = raw32857step1 := by apply Matrix.ext; unfold raw32857step2 raw32857step1; decide +kernel
      have hl : raw32857step1Labels = labelEmbedding1 ∘ raw32857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32857step1 raw32857step1Labels raw32857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

theorem canonical32858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32858 raw32858Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32858 raw32858Labels = mixedMoment B raw32858step0 raw32858step0Labels := by
      have ha : raw32858step0 = (fun i j => raw32858 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32858step0 raw32858; decide +kernel
      have hl : raw32858step0Labels = raw32858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32858 raw32858Labels permutation176 permutation7
    mixedMoment B raw32858step0 raw32858step0Labels = mixedMoment B raw32858step1 raw32858step1Labels := by
      have ha : raw32858step1 = -raw32858step0 := by apply Matrix.ext; change ∀ i j, raw32858step1 i j = -(raw32858step0 i j); unfold raw32858step1 raw32858step0; decide +kernel
      have hl : raw32858step1Labels = raw32858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32858step1 raw32858step1Labels = mixedMoment B raw32858step2 raw32858step2Labels := by
      have ha : raw32858step2 = raw32858step1 := by apply Matrix.ext; unfold raw32858step2 raw32858step1; decide +kernel
      have hl : raw32858step1Labels = labelEmbedding1 ∘ raw32858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32858step1 raw32858step1Labels raw32858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical32859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32859 raw32859Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32859 raw32859Labels = mixedMoment B raw32859step0 raw32859step0Labels := by
      have ha : raw32859step0 = (fun i j => raw32859 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32859step0 raw32859; decide +kernel
      have hl : raw32859step0Labels = raw32859Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32859 raw32859Labels permutation178 permutation7
    mixedMoment B raw32859step0 raw32859step0Labels = mixedMoment B raw32859step1 raw32859step1Labels := by
      have ha : raw32859step1 = -raw32859step0 := by apply Matrix.ext; change ∀ i j, raw32859step1 i j = -(raw32859step0 i j); unfold raw32859step1 raw32859step0; decide +kernel
      have hl : raw32859step1Labels = raw32859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32859step1 raw32859step1Labels = mixedMoment B raw32859step2 raw32859step2Labels := by
      have ha : raw32859step2 = raw32859step1 := by apply Matrix.ext; unfold raw32859step2 raw32859step1; decide +kernel
      have hl : raw32859step1Labels = labelEmbedding1 ∘ raw32859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32859step1 raw32859step1Labels raw32859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical32860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32860 raw32860Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw32860 raw32860Labels = mixedMoment B raw32860step0 raw32860step0Labels := by
      have ha : raw32860step0 = (fun i j => raw32860 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32860step0 raw32860; decide +kernel
      have hl : raw32860step0Labels = raw32860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32860 raw32860Labels permutation176 permutation7
    mixedMoment B raw32860step0 raw32860step0Labels = mixedMoment B raw32860step1 raw32860step1Labels := by
      have ha : raw32860step1 = -raw32860step0 := by apply Matrix.ext; change ∀ i j, raw32860step1 i j = -(raw32860step0 i j); unfold raw32860step1 raw32860step0; decide +kernel
      have hl : raw32860step1Labels = raw32860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32860step1 raw32860step1Labels = mixedMoment B raw32860step2 raw32860step2Labels := by
      have ha : raw32860step2 = raw32860step1 := by apply Matrix.ext; unfold raw32860step2 raw32860step1; decide +kernel
      have hl : raw32860step1Labels = labelEmbedding1 ∘ raw32860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32860step1 raw32860step1Labels raw32860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

theorem canonical32861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32861 raw32861Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw32861 raw32861Labels = mixedMoment B raw32861step0 raw32861step0Labels := by
      have hz : ∀ j, raw32861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32861step0 = (fun i j => raw32861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32861step0 raw32861; decide +kernel
      have hl : raw32861step0Labels = raw32861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32861 raw32861Labels permutation265 hz
    mixedMoment B raw32861step0 raw32861step0Labels = mixedMoment B raw32861step1 raw32861step1Labels := by
      have ha : raw32861step1 = (fun i j => raw32861step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32861step1 raw32861step0; decide +kernel
      have hl : raw32861step1Labels = raw32861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32861step0 raw32861step0Labels permutation32 permutation7
    mixedMoment B raw32861step1 raw32861step1Labels = mixedMoment B raw32861step2 raw32861step2Labels := by
      have ha : raw32861step2 = -raw32861step1 := by apply Matrix.ext; change ∀ i j, raw32861step2 i j = -(raw32861step1 i j); unfold raw32861step2 raw32861step1; decide +kernel
      have hl : raw32861step2Labels = raw32861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32861step2 raw32861step2Labels = mixedMoment B raw32861step3 raw32861step3Labels := by
      have ha : raw32861step3 = raw32861step2 := by apply Matrix.ext; unfold raw32861step3 raw32861step2; decide +kernel
      have hl : raw32861step2Labels = labelEmbedding1 ∘ raw32861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32861step2 raw32861step2Labels raw32861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical32862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32862 raw32862Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw32862 raw32862Labels = mixedMoment B raw32862step0 raw32862step0Labels := by
      have ha : raw32862step0 = (fun i j => raw32862 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32862step0 raw32862; decide +kernel
      have hl : raw32862step0Labels = raw32862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32862 raw32862Labels permutation176 permutation7
    mixedMoment B raw32862step0 raw32862step0Labels = mixedMoment B raw32862step1 raw32862step1Labels := by
      have ha : raw32862step1 = -raw32862step0 := by apply Matrix.ext; change ∀ i j, raw32862step1 i j = -(raw32862step0 i j); unfold raw32862step1 raw32862step0; decide +kernel
      have hl : raw32862step1Labels = raw32862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32862step1 raw32862step1Labels = mixedMoment B raw32862step2 raw32862step2Labels := by
      have ha : raw32862step2 = raw32862step1 := by apply Matrix.ext; unfold raw32862step2 raw32862step1; decide +kernel
      have hl : raw32862step1Labels = labelEmbedding1 ∘ raw32862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32862step1 raw32862step1Labels raw32862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

theorem canonical32863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32863 raw32863Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32863 raw32863Labels = mixedMoment B raw32863step0 raw32863step0Labels := by
      have ha : raw32863step0 = (fun i j => raw32863 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32863step0 raw32863; decide +kernel
      have hl : raw32863step0Labels = raw32863Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32863 raw32863Labels permutation176 permutation7
    mixedMoment B raw32863step0 raw32863step0Labels = mixedMoment B raw32863step1 raw32863step1Labels := by
      have ha : raw32863step1 = -raw32863step0 := by apply Matrix.ext; change ∀ i j, raw32863step1 i j = -(raw32863step0 i j); unfold raw32863step1 raw32863step0; decide +kernel
      have hl : raw32863step1Labels = raw32863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32863step1 raw32863step1Labels = mixedMoment B raw32863step2 raw32863step2Labels := by
      have ha : raw32863step2 = raw32863step1 := by apply Matrix.ext; unfold raw32863step2 raw32863step1; decide +kernel
      have hl : raw32863step1Labels = labelEmbedding1 ∘ raw32863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32863step1 raw32863step1Labels raw32863step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical32864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32864 raw32864Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32864 raw32864Labels = mixedMoment B raw32864step0 raw32864step0Labels := by
      have ha : raw32864step0 = (fun i j => raw32864 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32864step0 raw32864; decide +kernel
      have hl : raw32864step0Labels = raw32864Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32864 raw32864Labels permutation178 permutation7
    mixedMoment B raw32864step0 raw32864step0Labels = mixedMoment B raw32864step1 raw32864step1Labels := by
      have ha : raw32864step1 = -raw32864step0 := by apply Matrix.ext; change ∀ i j, raw32864step1 i j = -(raw32864step0 i j); unfold raw32864step1 raw32864step0; decide +kernel
      have hl : raw32864step1Labels = raw32864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32864step1 raw32864step1Labels = mixedMoment B raw32864step2 raw32864step2Labels := by
      have ha : raw32864step2 = raw32864step1 := by apply Matrix.ext; unfold raw32864step2 raw32864step1; decide +kernel
      have hl : raw32864step1Labels = labelEmbedding1 ∘ raw32864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32864step1 raw32864step1Labels raw32864step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical32865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32865 raw32865Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw32865 raw32865Labels = mixedMoment B raw32865step0 raw32865step0Labels := by
      have ha : raw32865step0 = (fun i j => raw32865 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32865step0 raw32865; decide +kernel
      have hl : raw32865step0Labels = raw32865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32865 raw32865Labels permutation176 permutation7
    mixedMoment B raw32865step0 raw32865step0Labels = mixedMoment B raw32865step1 raw32865step1Labels := by
      have ha : raw32865step1 = -raw32865step0 := by apply Matrix.ext; change ∀ i j, raw32865step1 i j = -(raw32865step0 i j); unfold raw32865step1 raw32865step0; decide +kernel
      have hl : raw32865step1Labels = raw32865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32865step1 raw32865step1Labels = mixedMoment B raw32865step2 raw32865step2Labels := by
      have ha : raw32865step2 = raw32865step1 := by apply Matrix.ext; unfold raw32865step2 raw32865step1; decide +kernel
      have hl : raw32865step1Labels = labelEmbedding1 ∘ raw32865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32865step1 raw32865step1Labels raw32865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

theorem canonical32866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32866 raw32866Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw32866 raw32866Labels = mixedMoment B raw32866step0 raw32866step0Labels := by
      have ha : raw32866step0 = (fun i j => raw32866 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32866step0 raw32866; decide +kernel
      have hl : raw32866step0Labels = raw32866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32866 raw32866Labels permutation178 permutation7
    mixedMoment B raw32866step0 raw32866step0Labels = mixedMoment B raw32866step1 raw32866step1Labels := by
      have ha : raw32866step1 = -raw32866step0 := by apply Matrix.ext; change ∀ i j, raw32866step1 i j = -(raw32866step0 i j); unfold raw32866step1 raw32866step0; decide +kernel
      have hl : raw32866step1Labels = raw32866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32866step1 raw32866step1Labels = mixedMoment B raw32866step2 raw32866step2Labels := by
      have ha : raw32866step2 = raw32866step1 := by apply Matrix.ext; unfold raw32866step2 raw32866step1; decide +kernel
      have hl : raw32866step1Labels = labelEmbedding1 ∘ raw32866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32866step1 raw32866step1Labels raw32866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical32867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32867 raw32867Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw32867 raw32867Labels = mixedMoment B raw32867step0 raw32867step0Labels := by
      have ha : raw32867step0 = (fun i j => raw32867 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32867step0 raw32867; decide +kernel
      have hl : raw32867step0Labels = raw32867Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32867 raw32867Labels permutation178 permutation7
    mixedMoment B raw32867step0 raw32867step0Labels = mixedMoment B raw32867step1 raw32867step1Labels := by
      have ha : raw32867step1 = -raw32867step0 := by apply Matrix.ext; change ∀ i j, raw32867step1 i j = -(raw32867step0 i j); unfold raw32867step1 raw32867step0; decide +kernel
      have hl : raw32867step1Labels = raw32867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32867step1 raw32867step1Labels = mixedMoment B raw32867step2 raw32867step2Labels := by
      have ha : raw32867step2 = raw32867step1 := by apply Matrix.ext; unfold raw32867step2 raw32867step1; decide +kernel
      have hl : raw32867step1Labels = labelEmbedding1 ∘ raw32867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32867step1 raw32867step1Labels raw32867step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

theorem canonical32868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32868 raw32868Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw32868 raw32868Labels = mixedMoment B raw32868step0 raw32868step0Labels := by
      have ha : raw32868step0 = (fun i j => raw32868 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32868step0 raw32868; decide +kernel
      have hl : raw32868step0Labels = raw32868Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32868 raw32868Labels permutation178 permutation7
    mixedMoment B raw32868step0 raw32868step0Labels = mixedMoment B raw32868step1 raw32868step1Labels := by
      have ha : raw32868step1 = -raw32868step0 := by apply Matrix.ext; change ∀ i j, raw32868step1 i j = -(raw32868step0 i j); unfold raw32868step1 raw32868step0; decide +kernel
      have hl : raw32868step1Labels = raw32868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32868step1 raw32868step1Labels = mixedMoment B raw32868step2 raw32868step2Labels := by
      have ha : raw32868step2 = raw32868step1 := by apply Matrix.ext; unfold raw32868step2 raw32868step1; decide +kernel
      have hl : raw32868step1Labels = labelEmbedding1 ∘ raw32868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32868step1 raw32868step1Labels raw32868step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical32869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32869 raw32869Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw32869 raw32869Labels = mixedMoment B raw32869step0 raw32869step0Labels := by
      have ha : raw32869step0 = (fun i j => raw32869 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32869step0 raw32869; decide +kernel
      have hl : raw32869step0Labels = raw32869Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32869 raw32869Labels permutation179 permutation7
    mixedMoment B raw32869step0 raw32869step0Labels = mixedMoment B raw32869step1 raw32869step1Labels := by
      have ha : raw32869step1 = -raw32869step0 := by apply Matrix.ext; change ∀ i j, raw32869step1 i j = -(raw32869step0 i j); unfold raw32869step1 raw32869step0; decide +kernel
      have hl : raw32869step1Labels = raw32869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32869step1 raw32869step1Labels = mixedMoment B raw32869step2 raw32869step2Labels := by
      have ha : raw32869step2 = raw32869step1 := by apply Matrix.ext; unfold raw32869step2 raw32869step1; decide +kernel
      have hl : raw32869step1Labels = labelEmbedding1 ∘ raw32869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32869step1 raw32869step1Labels raw32869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical32870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32870 raw32870Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw32870 raw32870Labels = mixedMoment B raw32870step0 raw32870step0Labels := by
      have ha : raw32870step0 = (fun i j => raw32870 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32870step0 raw32870; decide +kernel
      have hl : raw32870step0Labels = raw32870Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32870 raw32870Labels permutation176 permutation7
    mixedMoment B raw32870step0 raw32870step0Labels = mixedMoment B raw32870step1 raw32870step1Labels := by
      have ha : raw32870step1 = -raw32870step0 := by apply Matrix.ext; change ∀ i j, raw32870step1 i j = -(raw32870step0 i j); unfold raw32870step1 raw32870step0; decide +kernel
      have hl : raw32870step1Labels = raw32870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32870step1 raw32870step1Labels = mixedMoment B raw32870step2 raw32870step2Labels := by
      have ha : raw32870step2 = raw32870step1 := by apply Matrix.ext; unfold raw32870step2 raw32870step1; decide +kernel
      have hl : raw32870step1Labels = labelEmbedding1 ∘ raw32870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32870step1 raw32870step1Labels raw32870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

theorem canonical32871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32871 raw32871Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw32871 raw32871Labels = mixedMoment B raw32871step0 raw32871step0Labels := by
      have ha : raw32871step0 = (fun i j => raw32871 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32871step0 raw32871; decide +kernel
      have hl : raw32871step0Labels = raw32871Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32871 raw32871Labels permutation176 permutation7
    mixedMoment B raw32871step0 raw32871step0Labels = mixedMoment B raw32871step1 raw32871step1Labels := by
      have ha : raw32871step1 = -raw32871step0 := by apply Matrix.ext; change ∀ i j, raw32871step1 i j = -(raw32871step0 i j); unfold raw32871step1 raw32871step0; decide +kernel
      have hl : raw32871step1Labels = raw32871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32871step1 raw32871step1Labels = mixedMoment B raw32871step2 raw32871step2Labels := by
      have ha : raw32871step2 = raw32871step1 := by apply Matrix.ext; unfold raw32871step2 raw32871step1; decide +kernel
      have hl : raw32871step1Labels = labelEmbedding1 ∘ raw32871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32871step1 raw32871step1Labels raw32871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

theorem canonical32872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32872 raw32872Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw32872 raw32872Labels = mixedMoment B raw32872step0 raw32872step0Labels := by
      have ha : raw32872step0 = (fun i j => raw32872 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32872step0 raw32872; decide +kernel
      have hl : raw32872step0Labels = raw32872Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32872 raw32872Labels permutation176 permutation7
    mixedMoment B raw32872step0 raw32872step0Labels = mixedMoment B raw32872step1 raw32872step1Labels := by
      have ha : raw32872step1 = -raw32872step0 := by apply Matrix.ext; change ∀ i j, raw32872step1 i j = -(raw32872step0 i j); unfold raw32872step1 raw32872step0; decide +kernel
      have hl : raw32872step1Labels = raw32872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32872step1 raw32872step1Labels = mixedMoment B raw32872step2 raw32872step2Labels := by
      have ha : raw32872step2 = raw32872step1 := by apply Matrix.ext; unfold raw32872step2 raw32872step1; decide +kernel
      have hl : raw32872step1Labels = labelEmbedding1 ∘ raw32872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32872step1 raw32872step1Labels raw32872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical32873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32873 raw32873Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw32873 raw32873Labels = mixedMoment B raw32873step0 raw32873step0Labels := by
      have ha : raw32873step0 = (fun i j => raw32873 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32873step0 raw32873; decide +kernel
      have hl : raw32873step0Labels = raw32873Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32873 raw32873Labels permutation177 permutation7
    mixedMoment B raw32873step0 raw32873step0Labels = mixedMoment B raw32873step1 raw32873step1Labels := by
      have ha : raw32873step1 = -raw32873step0 := by apply Matrix.ext; change ∀ i j, raw32873step1 i j = -(raw32873step0 i j); unfold raw32873step1 raw32873step0; decide +kernel
      have hl : raw32873step1Labels = raw32873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32873step1 raw32873step1Labels = mixedMoment B raw32873step2 raw32873step2Labels := by
      have ha : raw32873step2 = raw32873step1 := by apply Matrix.ext; unfold raw32873step2 raw32873step1; decide +kernel
      have hl : raw32873step1Labels = labelEmbedding1 ∘ raw32873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32873step1 raw32873step1Labels raw32873step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical32874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32874 raw32874Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw32874 raw32874Labels = mixedMoment B raw32874step0 raw32874step0Labels := by
      have ha : raw32874step0 = (fun i j => raw32874 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32874step0 raw32874; decide +kernel
      have hl : raw32874step0Labels = raw32874Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32874 raw32874Labels permutation176 permutation7
    mixedMoment B raw32874step0 raw32874step0Labels = mixedMoment B raw32874step1 raw32874step1Labels := by
      have ha : raw32874step1 = -raw32874step0 := by apply Matrix.ext; change ∀ i j, raw32874step1 i j = -(raw32874step0 i j); unfold raw32874step1 raw32874step0; decide +kernel
      have hl : raw32874step1Labels = raw32874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32874step1 raw32874step1Labels = mixedMoment B raw32874step2 raw32874step2Labels := by
      have ha : raw32874step2 = raw32874step1 := by apply Matrix.ext; unfold raw32874step2 raw32874step1; decide +kernel
      have hl : raw32874step1Labels = labelEmbedding1 ∘ raw32874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32874step1 raw32874step1Labels raw32874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

theorem canonical32875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32875 raw32875Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw32875 raw32875Labels = mixedMoment B raw32875step0 raw32875step0Labels := by
      have ha : raw32875step0 = (fun i j => raw32875 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32875step0 raw32875; decide +kernel
      have hl : raw32875step0Labels = raw32875Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32875 raw32875Labels permutation176 permutation7
    mixedMoment B raw32875step0 raw32875step0Labels = mixedMoment B raw32875step1 raw32875step1Labels := by
      have ha : raw32875step1 = -raw32875step0 := by apply Matrix.ext; change ∀ i j, raw32875step1 i j = -(raw32875step0 i j); unfold raw32875step1 raw32875step0; decide +kernel
      have hl : raw32875step1Labels = raw32875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32875step1 raw32875step1Labels = mixedMoment B raw32875step2 raw32875step2Labels := by
      have ha : raw32875step2 = raw32875step1 := by apply Matrix.ext; unfold raw32875step2 raw32875step1; decide +kernel
      have hl : raw32875step1Labels = labelEmbedding1 ∘ raw32875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32875step1 raw32875step1Labels raw32875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical32876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32876 raw32876Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32876 raw32876Labels = mixedMoment B raw32876step0 raw32876step0Labels := by
      have ha : raw32876step0 = (fun i j => raw32876 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32876step0 raw32876; decide +kernel
      have hl : raw32876step0Labels = raw32876Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32876 raw32876Labels permutation646 permutation5
    mixedMoment B raw32876step0 raw32876step0Labels = mixedMoment B raw32876step1 raw32876step1Labels := by
      have ha : raw32876step1 = raw32876step0 := by apply Matrix.ext; unfold raw32876step1 raw32876step0; decide +kernel
      have hl : raw32876step0Labels = labelEmbedding1 ∘ raw32876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32876step0 raw32876step0Labels raw32876step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical32877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32877 raw32877Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32877 raw32877Labels = mixedMoment B raw32877step0 raw32877step0Labels := by
      have ha : raw32877step0 = (fun i j => raw32877 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32877step0 raw32877; decide +kernel
      have hl : raw32877step0Labels = raw32877Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32877 raw32877Labels permutation640 permutation5
    mixedMoment B raw32877step0 raw32877step0Labels = mixedMoment B raw32877step1 raw32877step1Labels := by
      have ha : raw32877step1 = raw32877step0 := by apply Matrix.ext; unfold raw32877step1 raw32877step0; decide +kernel
      have hl : raw32877step0Labels = labelEmbedding1 ∘ raw32877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32877step0 raw32877step0Labels raw32877step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical32878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32878 raw32878Labels = mixedMoment B node3721 node3721Labels := by
  calc
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical32879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32879 raw32879Labels = mixedMoment B node2354 node2354Labels := by
  calc
    _ = mixedMoment B node2354 node2354Labels := by rfl

theorem canonical32880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32880 raw32880Labels = mixedMoment B node2351 node2351Labels := by
  calc
    mixedMoment B raw32880 raw32880Labels = mixedMoment B raw32880step0 raw32880step0Labels := by
      have ha : raw32880step0 = (fun i j => raw32880 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32880step0 raw32880; decide +kernel
      have hl : raw32880step0Labels = raw32880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32880 raw32880Labels permutation154 permutation2
    _ = mixedMoment B node2351 node2351Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32962 raw32962Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw32962 raw32962Labels = mixedMoment B raw32962step0 raw32962step0Labels := by
      have ha : raw32962step0 = (fun i j => raw32962 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32962step0 raw32962; decide +kernel
      have hl : raw32962step0Labels = raw32962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32962 raw32962Labels permutation154 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical32963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32963 raw32963Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32963 raw32963Labels = mixedMoment B raw32963step0 raw32963step0Labels := by
      have ha : raw32963step0 = (fun i j => raw32963 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32963step0 raw32963; decide +kernel
      have hl : raw32963step0Labels = raw32963Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32963 raw32963Labels permutation154 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

theorem canonical32964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32964 raw32964Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw32964 raw32964Labels = mixedMoment B raw32964step0 raw32964step0Labels := by
      have ha : raw32964step0 = (fun i j => raw32964 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32964step0 raw32964; decide +kernel
      have hl : raw32964step0Labels = raw32964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32964 raw32964Labels permutation154 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

theorem canonical32965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32965 raw32965Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw32965 raw32965Labels = mixedMoment B raw32965step0 raw32965step0Labels := by
      have ha : raw32965step0 = (fun i j => raw32965 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32965step0 raw32965; decide +kernel
      have hl : raw32965step0Labels = raw32965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32965 raw32965Labels permutation154 permutation2
    _ = mixedMoment B node2347 node2347Labels := by rfl

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

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

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

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

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

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2347 node2347Labels = Sparse.eval nodeValue2347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2347) = mixedMoment B node2347 node2347Labels := rfl
  simpa [nodeValue2347, Sparse.eval] using hc.symm

theorem sound2348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2348 node2348Labels = Sparse.eval nodeValue2348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2348) = mixedMoment B node2348 node2348Labels := rfl
  simpa [nodeValue2348, Sparse.eval] using hc.symm

theorem sound2349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2349 node2349Labels = Sparse.eval nodeValue2349 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2349) = mixedMoment B node2349 node2349Labels := rfl
  simpa [nodeValue2349, Sparse.eval] using hc.symm

theorem sound2350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2350 node2350Labels = Sparse.eval nodeValue2350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2350) = mixedMoment B node2350 node2350Labels := rfl
  simpa [nodeValue2350, Sparse.eval] using hc.symm

theorem sound2351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2351 node2351Labels = Sparse.eval nodeValue2351 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2351) = mixedMoment B node2351 node2351Labels := rfl
  simpa [nodeValue2351, Sparse.eval] using hc.symm

theorem sound2353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2353 node2353Labels = Sparse.eval nodeValue2353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2353) = mixedMoment B node2353 node2353Labels := rfl
  simpa [nodeValue2353, Sparse.eval] using hc.symm

theorem sound2354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2354 node2354Labels = Sparse.eval nodeValue2354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2354) = mixedMoment B node2354 node2354Labels := rfl
  simpa [nodeValue2354, Sparse.eval] using hc.symm

theorem sound2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2355 node2355Labels = Sparse.eval nodeValue2355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2355) = mixedMoment B node2355 node2355Labels := rfl
  simpa [nodeValue2355, Sparse.eval] using hc.symm

theorem sound2356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2356 node2356Labels = Sparse.eval nodeValue2356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2356) = mixedMoment B node2356 node2356Labels := rfl
  simpa [nodeValue2356, Sparse.eval] using hc.symm

theorem sound2362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2362 node2362Labels = Sparse.eval nodeValue2362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2362) = mixedMoment B node2362 node2362Labels := rfl
  simpa [nodeValue2362, Sparse.eval] using hc.symm

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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2607 node2607Labels = Sparse.eval nodeValue2607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2607) = mixedMoment B node2607 node2607Labels := rfl
  simpa [nodeValue2607, Sparse.eval] using hc.symm

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

theorem sound2806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2806 node2806Labels = Sparse.eval nodeValue2806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2806) = mixedMoment B node2806 node2806Labels := rfl
  simpa [nodeValue2806, Sparse.eval] using hc.symm

theorem sound2812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2812 node2812Labels = Sparse.eval nodeValue2812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2812) = mixedMoment B node2812 node2812Labels := rfl
  simpa [nodeValue2812, Sparse.eval] using hc.symm

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

theorem sound2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2879 node2879Labels = Sparse.eval nodeValue2879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2879) = mixedMoment B node2879 node2879Labels := rfl
  simpa [nodeValue2879, Sparse.eval] using hc.symm

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

theorem sound3067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3067 node3067Labels = Sparse.eval nodeValue3067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3067) = mixedMoment B node3067 node3067Labels := rfl
  simpa [nodeValue3067, Sparse.eval] using hc.symm

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

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

theorem sound3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3261 node3261Labels = Sparse.eval nodeValue3261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3261) = mixedMoment B node3261 node3261Labels := rfl
  simpa [nodeValue3261, Sparse.eval] using hc.symm

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

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

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

theorem sound3456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3456 node3456Labels = Sparse.eval nodeValue3456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3456) = mixedMoment B node3456 node3456Labels := rfl
  simpa [nodeValue3456, Sparse.eval] using hc.symm

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3458 node3458Labels = Sparse.eval nodeValue3458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3458) = mixedMoment B node3458 node3458Labels := rfl
  simpa [nodeValue3458, Sparse.eval] using hc.symm

theorem sound3461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3461 node3461Labels = Sparse.eval nodeValue3461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3461) = mixedMoment B node3461 node3461Labels := rfl
  simpa [nodeValue3461, Sparse.eval] using hc.symm

theorem sound3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3462 node3462Labels = Sparse.eval nodeValue3462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3462) = mixedMoment B node3462 node3462Labels := rfl
  simpa [nodeValue3462, Sparse.eval] using hc.symm

theorem sound3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3464 node3464Labels = Sparse.eval nodeValue3464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3464) = mixedMoment B node3464 node3464Labels := rfl
  simpa [nodeValue3464, Sparse.eval] using hc.symm

theorem sound3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3465 node3465Labels = Sparse.eval nodeValue3465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3465) = mixedMoment B node3465 node3465Labels := rfl
  simpa [nodeValue3465, Sparse.eval] using hc.symm

theorem sound3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3474 node3474Labels = Sparse.eval nodeValue3474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3474) = mixedMoment B node3474 node3474Labels := rfl
  simpa [nodeValue3474, Sparse.eval] using hc.symm

theorem sound3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = Sparse.eval nodeValue3483 (mixedVector B) := by
  simpa only [nodeValue3483, Sparse.eval_nil] using zero3483 B _hB _hF

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

theorem sound3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3510 node3510Labels = Sparse.eval nodeValue3510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3510) = mixedMoment B node3510 node3510Labels := rfl
  simpa [nodeValue3510, Sparse.eval] using hc.symm

theorem sound3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3511 node3511Labels = Sparse.eval nodeValue3511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3511) = mixedMoment B node3511 node3511Labels := rfl
  simpa [nodeValue3511, Sparse.eval] using hc.symm

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

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

theorem zero3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = 0 := by
  exact mixedMoment_alpha B hF node3520 node3520Labels 1 permutation446
    (by decide +kernel)

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
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

theorem sound3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = Sparse.eval nodeValue3520 (mixedVector B) := by
  simpa only [nodeValue3520, Sparse.eval_nil] using zero3520 B _hB _hF

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3554 node3554Labels = Sparse.eval nodeValue3554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3554) = mixedMoment B node3554 node3554Labels := rfl
  simpa [nodeValue3554, Sparse.eval] using hc.symm

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

theorem sound3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3569 node3569Labels = Sparse.eval nodeValue3569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3569) = mixedMoment B node3569 node3569Labels := rfl
  simpa [nodeValue3569, Sparse.eval] using hc.symm

theorem sound3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3570 node3570Labels = Sparse.eval nodeValue3570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3570) = mixedMoment B node3570 node3570Labels := rfl
  simpa [nodeValue3570, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3578 node3578Labels = Sparse.eval nodeValue3578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3578) = mixedMoment B node3578 node3578Labels := rfl
  simpa [nodeValue3578, Sparse.eval] using hc.symm

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

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3590 node3590Labels = Sparse.eval nodeValue3590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3590) = mixedMoment B node3590 node3590Labels := rfl
  simpa [nodeValue3590, Sparse.eval] using hc.symm

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

theorem sound3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3592 node3592Labels = Sparse.eval nodeValue3592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3592) = mixedMoment B node3592 node3592Labels := rfl
  simpa [nodeValue3592, Sparse.eval] using hc.symm

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem zero3766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = 0 := by
  exact mixedMoment_order_one B hB node3766 node3766Labels 1
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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

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

theorem zero3798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = 0 := by
  exact mixedMoment_order_one B hB node3798 node3798Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = 0 := by
  exact mixedMoment_order_one B hB node3817 node3817Labels 1
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

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3798 node3798Labels = Sparse.eval nodeValue3798 (mixedVector B) := by
  simpa only [nodeValue3798, Sparse.eval_nil] using zero3798 B _hB _hF

theorem sound3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3817 node3817Labels = Sparse.eval nodeValue3817 (mixedVector B) := by
  simpa only [nodeValue3817, Sparse.eval_nil] using zero3817 B _hB _hF

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

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

theorem zero3844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = 0 := by
  exact mixedMoment_order_one B hB node3844 node3844Labels 1
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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3844 node3844Labels = Sparse.eval nodeValue3844 (mixedVector B) := by
  simpa only [nodeValue3844, Sparse.eval_nil] using zero3844 B _hB _hF

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3866 node3866Labels = Sparse.eval nodeValue3866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3866) = mixedMoment B node3866 node3866Labels := rfl
  simpa [nodeValue3866, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

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

theorem zero3962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = 0 := by
  exact mixedMoment_order_one B hB node3962 node3962Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3962 node3962Labels = Sparse.eval nodeValue3962 (mixedVector B) := by
  simpa only [nodeValue3962, Sparse.eval_nil] using zero3962 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2383 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 1) (sourceB2383 + difference 1 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 1) (sourceB2383 + difference 1 0) sourceC2383) = raw32597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32597; decide +kernel
    rw [ha]
    exact (canonical32597 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 2) (sourceB2383 + difference 2 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3952) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 2) (sourceB2383 + difference 2 0) sourceC2383) = raw32598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32598; decide +kernel
    rw [ha]
    exact (canonical32598 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 3) (sourceB2383 + difference 3 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 3) (sourceB2383 + difference 3 0) sourceC2383) = raw32599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32599; decide +kernel
    rw [ha]
    exact (canonical32599 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 4) (sourceB2383 + difference 4 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 4) (sourceB2383 + difference 4 0) sourceC2383) = raw32600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32600; decide +kernel
    rw [ha]
    exact (canonical32600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2383 + difference 0 5) (sourceB2383 + difference 5 0) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3962) := by
    have ha : (tripleCharges (sourceA2383 + difference 0 5) (sourceB2383 + difference 5 0) sourceC2383) = raw32601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32601; decide +kernel
    rw [ha]
    exact (canonical32601 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 0) (sourceB2383 + difference 0 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 0) (sourceB2383 + difference 0 1) sourceC2383) = raw32602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32602; decide +kernel
    rw [ha]
    exact (canonical32602 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 2) (sourceB2383 + difference 2 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 2) (sourceB2383 + difference 2 1) sourceC2383) = raw32603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32603; decide +kernel
    rw [ha]
    exact (canonical32603 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 3) (sourceB2383 + difference 3 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 3) (sourceB2383 + difference 3 1) sourceC2383) = raw32604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32604; decide +kernel
    rw [ha]
    exact (canonical32604 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 4) (sourceB2383 + difference 4 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 4) (sourceB2383 + difference 4 1) sourceC2383) = raw32605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32605; decide +kernel
    rw [ha]
    exact (canonical32605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2383 + difference 1 5) (sourceB2383 + difference 5 1) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA2383 + difference 1 5) (sourceB2383 + difference 5 1) sourceC2383) = raw32606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32606; decide +kernel
    rw [ha]
    exact (canonical32606 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 0) (sourceB2383 + difference 0 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 0) (sourceB2383 + difference 0 2) sourceC2383) = raw32607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32607; decide +kernel
    rw [ha]
    exact (canonical32607 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 1) (sourceB2383 + difference 1 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3587) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 1) (sourceB2383 + difference 1 2) sourceC2383) = raw32608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32608; decide +kernel
    rw [ha]
    exact (canonical32608 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 3) (sourceB2383 + difference 3 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 3) (sourceB2383 + difference 3 2) sourceC2383) = raw32609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32609; decide +kernel
    rw [ha]
    exact (canonical32609 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 4) (sourceB2383 + difference 4 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 4) (sourceB2383 + difference 4 2) sourceC2383) = raw32610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32610; decide +kernel
    rw [ha]
    exact (canonical32610 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2383 + difference 2 5) (sourceB2383 + difference 5 2) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3617) := by
    have ha : (tripleCharges (sourceA2383 + difference 2 5) (sourceB2383 + difference 5 2) sourceC2383) = raw32611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32611; decide +kernel
    rw [ha]
    exact (canonical32611 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 0) (sourceB2383 + difference 0 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 0) (sourceB2383 + difference 0 3) sourceC2383) = raw32612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32612; decide +kernel
    rw [ha]
    exact (canonical32612 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 1) (sourceB2383 + difference 1 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 1) (sourceB2383 + difference 1 3) sourceC2383) = raw32613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32613; decide +kernel
    rw [ha]
    exact (canonical32613 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 2) (sourceB2383 + difference 2 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 2) (sourceB2383 + difference 2 3) sourceC2383) = raw32614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32614; decide +kernel
    rw [ha]
    exact (canonical32614 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 4) (sourceB2383 + difference 4 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 4) (sourceB2383 + difference 4 3) sourceC2383) = raw32615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32615; decide +kernel
    rw [ha]
    exact (canonical32615 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2383 + difference 3 5) (sourceB2383 + difference 5 3) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA2383 + difference 3 5) (sourceB2383 + difference 5 3) sourceC2383) = raw32616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32616; decide +kernel
    rw [ha]
    exact (canonical32616 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 0) (sourceB2383 + difference 0 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 0) (sourceB2383 + difference 0 4) sourceC2383) = raw32617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32617; decide +kernel
    rw [ha]
    exact (canonical32617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 1) (sourceB2383 + difference 1 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3592) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 1) (sourceB2383 + difference 1 4) sourceC2383) = raw32618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32618; decide +kernel
    rw [ha]
    exact (canonical32618 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 2) (sourceB2383 + difference 2 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 2) (sourceB2383 + difference 2 4) sourceC2383) = raw32619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32619; decide +kernel
    rw [ha]
    exact (canonical32619 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 3) (sourceB2383 + difference 3 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 3) (sourceB2383 + difference 3 4) sourceC2383) = raw32620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32620; decide +kernel
    rw [ha]
    exact (canonical32620 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2383 + difference 4 5) (sourceB2383 + difference 5 4) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA2383 + difference 4 5) (sourceB2383 + difference 5 4) sourceC2383) = raw32621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32621; decide +kernel
    rw [ha]
    exact (canonical32621 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 0) (sourceB2383 + difference 0 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 0) (sourceB2383 + difference 0 5) sourceC2383) = raw32622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32622; decide +kernel
    rw [ha]
    exact (canonical32622 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 1) (sourceB2383 + difference 1 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 1) (sourceB2383 + difference 1 5) sourceC2383) = raw32623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32623; decide +kernel
    rw [ha]
    exact (canonical32623 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 2) (sourceB2383 + difference 2 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 2) (sourceB2383 + difference 2 5) sourceC2383) = raw32624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32624; decide +kernel
    rw [ha]
    exact (canonical32624 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 3) (sourceB2383 + difference 3 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 3) (sourceB2383 + difference 3 5) sourceC2383) = raw32625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32625; decide +kernel
    rw [ha]
    exact (canonical32625 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2383 + difference 5 4) (sourceB2383 + difference 4 5) sourceC2383) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2383 + difference 5 4) (sourceB2383 + difference 4 5) sourceC2383) = raw32626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2383 sourceB2383 sourceC2383 difference raw32626; decide +kernel
    rw [ha]
    exact (canonical32626 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2383 sourceB2383 sourceC2383
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2383, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 1) (sourceB2387 + difference 1 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 1) (sourceB2387 + difference 1 0) sourceC2387) = raw32699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32699; decide +kernel
    rw [ha]
    exact (canonical32699 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 2) (sourceB2387 + difference 2 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 2) (sourceB2387 + difference 2 0) sourceC2387) = raw32700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32700; decide +kernel
    rw [ha]
    exact (canonical32700 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 3) (sourceB2387 + difference 3 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 3) (sourceB2387 + difference 3 0) sourceC2387) = raw32701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32701; decide +kernel
    rw [ha]
    exact (canonical32701 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 4) (sourceB2387 + difference 4 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 4) (sourceB2387 + difference 4 0) sourceC2387) = raw32702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32702; decide +kernel
    rw [ha]
    exact (canonical32702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2387 + difference 0 5) (sourceB2387 + difference 5 0) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2387 + difference 0 5) (sourceB2387 + difference 5 0) sourceC2387) = raw32703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32703; decide +kernel
    rw [ha]
    exact (canonical32703 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 0) (sourceB2387 + difference 0 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 0) (sourceB2387 + difference 0 1) sourceC2387) = raw32704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32704; decide +kernel
    rw [ha]
    exact (canonical32704 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 2) (sourceB2387 + difference 2 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 2) (sourceB2387 + difference 2 1) sourceC2387) = raw32705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32705; decide +kernel
    rw [ha]
    exact (canonical32705 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 3) (sourceB2387 + difference 3 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 3) (sourceB2387 + difference 3 1) sourceC2387) = raw32706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32706; decide +kernel
    rw [ha]
    exact (canonical32706 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 4) (sourceB2387 + difference 4 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 4) (sourceB2387 + difference 4 1) sourceC2387) = raw32707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32707; decide +kernel
    rw [ha]
    exact (canonical32707 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2387 + difference 1 5) (sourceB2387 + difference 5 1) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA2387 + difference 1 5) (sourceB2387 + difference 5 1) sourceC2387) = raw32708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32708; decide +kernel
    rw [ha]
    exact (canonical32708 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 0) (sourceB2387 + difference 0 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 0) (sourceB2387 + difference 0 2) sourceC2387) = raw32709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32709; decide +kernel
    rw [ha]
    exact (canonical32709 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 1) (sourceB2387 + difference 1 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3590) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 1) (sourceB2387 + difference 1 2) sourceC2387) = raw32710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32710; decide +kernel
    rw [ha]
    exact (canonical32710 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 3) (sourceB2387 + difference 3 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 3) (sourceB2387 + difference 3 2) sourceC2387) = raw32711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32711; decide +kernel
    rw [ha]
    exact (canonical32711 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 4) (sourceB2387 + difference 4 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 4) (sourceB2387 + difference 4 2) sourceC2387) = raw32712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32712; decide +kernel
    rw [ha]
    exact (canonical32712 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2387 + difference 2 5) (sourceB2387 + difference 5 2) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA2387 + difference 2 5) (sourceB2387 + difference 5 2) sourceC2387) = raw32713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32713; decide +kernel
    rw [ha]
    exact (canonical32713 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 0) (sourceB2387 + difference 0 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 0) (sourceB2387 + difference 0 3) sourceC2387) = raw32714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32714; decide +kernel
    rw [ha]
    exact (canonical32714 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 1) (sourceB2387 + difference 1 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 1) (sourceB2387 + difference 1 3) sourceC2387) = raw32715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32715; decide +kernel
    rw [ha]
    exact (canonical32715 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 2) (sourceB2387 + difference 2 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 2) (sourceB2387 + difference 2 3) sourceC2387) = raw32716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32716; decide +kernel
    rw [ha]
    exact (canonical32716 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 4) (sourceB2387 + difference 4 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 4) (sourceB2387 + difference 4 3) sourceC2387) = raw32717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32717; decide +kernel
    rw [ha]
    exact (canonical32717 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2387 + difference 3 5) (sourceB2387 + difference 5 3) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2387 + difference 3 5) (sourceB2387 + difference 5 3) sourceC2387) = raw32718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32718; decide +kernel
    rw [ha]
    exact (canonical32718 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 0) (sourceB2387 + difference 0 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 0) (sourceB2387 + difference 0 4) sourceC2387) = raw32719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32719; decide +kernel
    rw [ha]
    exact (canonical32719 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 1) (sourceB2387 + difference 1 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 1) (sourceB2387 + difference 1 4) sourceC2387) = raw32720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32720; decide +kernel
    rw [ha]
    exact (canonical32720 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 2) (sourceB2387 + difference 2 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 2) (sourceB2387 + difference 2 4) sourceC2387) = raw32721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32721; decide +kernel
    rw [ha]
    exact (canonical32721 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 3) (sourceB2387 + difference 3 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 3) (sourceB2387 + difference 3 4) sourceC2387) = raw32722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32722; decide +kernel
    rw [ha]
    exact (canonical32722 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2387 + difference 4 5) (sourceB2387 + difference 5 4) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2387 + difference 4 5) (sourceB2387 + difference 5 4) sourceC2387) = raw32723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32723; decide +kernel
    rw [ha]
    exact (canonical32723 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 0) (sourceB2387 + difference 0 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 0) (sourceB2387 + difference 0 5) sourceC2387) = raw32724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32724; decide +kernel
    rw [ha]
    exact (canonical32724 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 1) (sourceB2387 + difference 1 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 1) (sourceB2387 + difference 1 5) sourceC2387) = raw32725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32725; decide +kernel
    rw [ha]
    exact (canonical32725 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 2) (sourceB2387 + difference 2 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 2) (sourceB2387 + difference 2 5) sourceC2387) = raw32726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32726; decide +kernel
    rw [ha]
    exact (canonical32726 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 3) (sourceB2387 + difference 3 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 3) (sourceB2387 + difference 3 5) sourceC2387) = raw32727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32727; decide +kernel
    rw [ha]
    exact (canonical32727 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2387 + difference 5 4) (sourceB2387 + difference 4 5) sourceC2387) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2387 + difference 5 4) (sourceB2387 + difference 4 5) sourceC2387) = raw32728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2387 sourceB2387 sourceC2387 difference raw32728; decide +kernel
    rw [ha]
    exact (canonical32728 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2387 sourceB2387 sourceC2387
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2387, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2388 + difference 0 1) (sourceB2388 + difference 1 0) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA2388 + difference 0 1) (sourceB2388 + difference 1 0) sourceC2388) = raw32729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32729; decide +kernel
    rw [ha]
    exact (canonical32729 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2388 + difference 1 1) (sourceB2388 + difference 1 1) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA2388 + difference 1 1) (sourceB2388 + difference 1 1) sourceC2388) = raw32730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32730; decide +kernel
    rw [ha]
    exact (canonical32730 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2388 + difference 2 1) (sourceB2388 + difference 1 2) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2806) := by
    have ha : (tripleCharges (sourceA2388 + difference 2 1) (sourceB2388 + difference 1 2) sourceC2388) = raw32731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32731; decide +kernel
    rw [ha]
    exact (canonical32731 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2388 + difference 3 1) (sourceB2388 + difference 1 3) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2388 + difference 3 1) (sourceB2388 + difference 1 3) sourceC2388) = raw32732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32732; decide +kernel
    rw [ha]
    exact (canonical32732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2388 + difference 4 1) (sourceB2388 + difference 1 4) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2388 + difference 4 1) (sourceB2388 + difference 1 4) sourceC2388) = raw32733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw32733; decide +kernel
    rw [ha]
    exact (canonical32733 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2388 + difference 5 1) (sourceB2388 + difference 1 5) sourceC2388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2388 + difference 5 1) (sourceB2388 + difference 1 5) sourceC2388) = raw28458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2388 sourceB2388 sourceC2388 difference raw28458; decide +kernel
    rw [ha]
    exact (canonical28458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2388 + sourceB2388) sourceC2388) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2388 + sourceB2388) sourceC2388) = raw28461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2388 sourceB2388 sourceC2388 raw28461; decide +kernel
    rw [ha]
    exact (canonical28461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2388 sourceB2388 sourceC2388
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2388, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2390 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 0) (sourceB2390 + difference 0 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 0) (sourceB2390 + difference 0 0) sourceC2390) = raw24061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw24061; decide +kernel
    rw [ha]
    exact (canonical24061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 1) (sourceB2390 + difference 1 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3067) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 1) (sourceB2390 + difference 1 0) sourceC2390) = raw32739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32739; decide +kernel
    rw [ha]
    exact (canonical32739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 2) (sourceB2390 + difference 2 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 2) (sourceB2390 + difference 2 0) sourceC2390) = raw32740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32740; decide +kernel
    rw [ha]
    exact (canonical32740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 3) (sourceB2390 + difference 3 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 3) (sourceB2390 + difference 3 0) sourceC2390) = raw32741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32741; decide +kernel
    rw [ha]
    exact (canonical32741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 4) (sourceB2390 + difference 4 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 4) (sourceB2390 + difference 4 0) sourceC2390) = raw32742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32742; decide +kernel
    rw [ha]
    exact (canonical32742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2390 + difference 0 5) (sourceB2390 + difference 5 0) sourceC2390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA2390 + difference 0 5) (sourceB2390 + difference 5 0) sourceC2390) = raw32743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2390 sourceB2390 sourceC2390 difference raw32743; decide +kernel
    rw [ha]
    exact (canonical32743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2390 + sourceB2390) sourceC2390) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2390 + sourceB2390) sourceC2390) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA2390 sourceB2390 sourceC2390 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2390 sourceB2390 sourceC2390
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2390, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2393 + difference 0 1) (sourceB2393 + difference 1 0) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2393 + difference 0 1) (sourceB2393 + difference 1 0) sourceC2393) = raw32788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32788; decide +kernel
    rw [ha]
    exact (canonical32788 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2393 + difference 1 1) (sourceB2393 + difference 1 1) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2393 + difference 1 1) (sourceB2393 + difference 1 1) sourceC2393) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2393 + difference 2 1) (sourceB2393 + difference 1 2) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2393 + difference 2 1) (sourceB2393 + difference 1 2) sourceC2393) = raw32789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32789; decide +kernel
    rw [ha]
    exact (canonical32789 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2393 + difference 3 1) (sourceB2393 + difference 1 3) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2393 + difference 3 1) (sourceB2393 + difference 1 3) sourceC2393) = raw32790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw32790; decide +kernel
    rw [ha]
    exact (canonical32790 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2393 + difference 4 1) (sourceB2393 + difference 1 4) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2393 + difference 4 1) (sourceB2393 + difference 1 4) sourceC2393) = raw29701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw29701; decide +kernel
    rw [ha]
    exact (canonical29701 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2393 + difference 5 1) (sourceB2393 + difference 1 5) sourceC2393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2393 + difference 5 1) (sourceB2393 + difference 1 5) sourceC2393) = raw27812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2393 sourceB2393 sourceC2393 difference raw27812; decide +kernel
    rw [ha]
    exact (canonical27812 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2393 + sourceB2393) sourceC2393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2393 + sourceB2393) sourceC2393) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA2393 sourceB2393 sourceC2393 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2393 sourceB2393 sourceC2393
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2393, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2398 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 1) (sourceB2398 + difference 1 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3836) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 1) (sourceB2398 + difference 1 0) sourceC2398) = raw32856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32856; decide +kernel
    rw [ha]
    exact (canonical32856 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 2) (sourceB2398 + difference 2 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 2) (sourceB2398 + difference 2 0) sourceC2398) = raw32857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32857; decide +kernel
    rw [ha]
    exact (canonical32857 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 3) (sourceB2398 + difference 3 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 3) (sourceB2398 + difference 3 0) sourceC2398) = raw32858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32858; decide +kernel
    rw [ha]
    exact (canonical32858 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 4) (sourceB2398 + difference 4 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 4) (sourceB2398 + difference 4 0) sourceC2398) = raw32859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32859; decide +kernel
    rw [ha]
    exact (canonical32859 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2398 + difference 0 5) (sourceB2398 + difference 5 0) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3844) := by
    have ha : (tripleCharges (sourceA2398 + difference 0 5) (sourceB2398 + difference 5 0) sourceC2398) = raw32860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32860; decide +kernel
    rw [ha]
    exact (canonical32860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 0) (sourceB2398 + difference 0 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 0) (sourceB2398 + difference 0 1) sourceC2398) = raw32861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32861; decide +kernel
    rw [ha]
    exact (canonical32861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 2) (sourceB2398 + difference 2 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 2) (sourceB2398 + difference 2 1) sourceC2398) = raw24517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24517; decide +kernel
    rw [ha]
    exact (canonical24517 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 3) (sourceB2398 + difference 3 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 3) (sourceB2398 + difference 3 1) sourceC2398) = raw24518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24518; decide +kernel
    rw [ha]
    exact (canonical24518 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 4) (sourceB2398 + difference 4 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 4) (sourceB2398 + difference 4 1) sourceC2398) = raw24519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24519; decide +kernel
    rw [ha]
    exact (canonical24519 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2398 + difference 1 5) (sourceB2398 + difference 5 1) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA2398 + difference 1 5) (sourceB2398 + difference 5 1) sourceC2398) = raw24520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24520; decide +kernel
    rw [ha]
    exact (canonical24520 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 0) (sourceB2398 + difference 0 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 0) (sourceB2398 + difference 0 2) sourceC2398) = raw24527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24527; decide +kernel
    rw [ha]
    exact (canonical24527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 1) (sourceB2398 + difference 1 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3554) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 1) (sourceB2398 + difference 1 2) sourceC2398) = raw32862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32862; decide +kernel
    rw [ha]
    exact (canonical32862 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 3) (sourceB2398 + difference 3 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 3) (sourceB2398 + difference 3 2) sourceC2398) = raw32863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32863; decide +kernel
    rw [ha]
    exact (canonical32863 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 4) (sourceB2398 + difference 4 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 4) (sourceB2398 + difference 4 2) sourceC2398) = raw32864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32864; decide +kernel
    rw [ha]
    exact (canonical32864 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2398 + difference 2 5) (sourceB2398 + difference 5 2) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA2398 + difference 2 5) (sourceB2398 + difference 5 2) sourceC2398) = raw32865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32865; decide +kernel
    rw [ha]
    exact (canonical32865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 0) (sourceB2398 + difference 0 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 0) (sourceB2398 + difference 0 3) sourceC2398) = raw24532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24532; decide +kernel
    rw [ha]
    exact (canonical24532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 1) (sourceB2398 + difference 1 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 1) (sourceB2398 + difference 1 3) sourceC2398) = raw32866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32866; decide +kernel
    rw [ha]
    exact (canonical32866 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 2) (sourceB2398 + difference 2 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 2) (sourceB2398 + difference 2 3) sourceC2398) = raw32867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32867; decide +kernel
    rw [ha]
    exact (canonical32867 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 4) (sourceB2398 + difference 4 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 4) (sourceB2398 + difference 4 3) sourceC2398) = raw32868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32868; decide +kernel
    rw [ha]
    exact (canonical32868 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2398 + difference 3 5) (sourceB2398 + difference 5 3) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2398 + difference 3 5) (sourceB2398 + difference 5 3) sourceC2398) = raw32869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32869; decide +kernel
    rw [ha]
    exact (canonical32869 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 0) (sourceB2398 + difference 0 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 0) (sourceB2398 + difference 0 4) sourceC2398) = raw24537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24537; decide +kernel
    rw [ha]
    exact (canonical24537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 1) (sourceB2398 + difference 1 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 1) (sourceB2398 + difference 1 4) sourceC2398) = raw32870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32870; decide +kernel
    rw [ha]
    exact (canonical32870 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 2) (sourceB2398 + difference 2 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 2) (sourceB2398 + difference 2 4) sourceC2398) = raw32871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32871; decide +kernel
    rw [ha]
    exact (canonical32871 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 3) (sourceB2398 + difference 3 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 3) (sourceB2398 + difference 3 4) sourceC2398) = raw32872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32872; decide +kernel
    rw [ha]
    exact (canonical32872 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2398 + difference 4 5) (sourceB2398 + difference 5 4) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2398 + difference 4 5) (sourceB2398 + difference 5 4) sourceC2398) = raw32873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32873; decide +kernel
    rw [ha]
    exact (canonical32873 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 0) (sourceB2398 + difference 0 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 0) (sourceB2398 + difference 0 5) sourceC2398) = raw24542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw24542; decide +kernel
    rw [ha]
    exact (canonical24542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 1) (sourceB2398 + difference 1 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 1) (sourceB2398 + difference 1 5) sourceC2398) = raw32874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32874; decide +kernel
    rw [ha]
    exact (canonical32874 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 2) (sourceB2398 + difference 2 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 2) (sourceB2398 + difference 2 5) sourceC2398) = raw32875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32875; decide +kernel
    rw [ha]
    exact (canonical32875 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 3) (sourceB2398 + difference 3 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 3) (sourceB2398 + difference 3 5) sourceC2398) = raw32876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32876; decide +kernel
    rw [ha]
    exact (canonical32876 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2398 + difference 5 4) (sourceB2398 + difference 4 5) sourceC2398) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2398 + difference 5 4) (sourceB2398 + difference 4 5) sourceC2398) = raw32877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2398 sourceB2398 sourceC2398 difference raw32877; decide +kernel
    rw [ha]
    exact (canonical32877 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2398 sourceB2398 sourceC2398
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2398, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2399 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2399 + difference 0 1) (sourceB2399 + difference 1 0) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2399 + difference 0 1) (sourceB2399 + difference 1 0) sourceC2399) = raw32878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32878; decide +kernel
    rw [ha]
    exact (canonical32878 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2399 + difference 1 1) (sourceB2399 + difference 1 1) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2399 + difference 1 1) (sourceB2399 + difference 1 1) sourceC2399) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2399 + difference 2 1) (sourceB2399 + difference 1 2) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2354) := by
    have ha : (tripleCharges (sourceA2399 + difference 2 1) (sourceB2399 + difference 1 2) sourceC2399) = raw32879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32879; decide +kernel
    rw [ha]
    exact (canonical32879 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2399 + difference 3 1) (sourceB2399 + difference 1 3) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2399 + difference 3 1) (sourceB2399 + difference 1 3) sourceC2399) = raw32880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw32880; decide +kernel
    rw [ha]
    exact (canonical32880 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2399 + difference 4 1) (sourceB2399 + difference 1 4) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2399 + difference 4 1) (sourceB2399 + difference 1 4) sourceC2399) = raw29487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw29487; decide +kernel
    rw [ha]
    exact (canonical29487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2399 + difference 5 1) (sourceB2399 + difference 1 5) sourceC2399) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA2399 + difference 5 1) (sourceB2399 + difference 1 5) sourceC2399) = raw27531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2399 sourceB2399 sourceC2399 difference raw27531; decide +kernel
    rw [ha]
    exact (canonical27531 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2399 + sourceB2399) sourceC2399) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2399 + sourceB2399) sourceC2399) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2399 sourceB2399 sourceC2399 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2399 sourceB2399 sourceC2399
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2399, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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

theorem sourceEq2404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2404 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2404 + difference 0 1) (sourceB2404 + difference 1 0) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2404 + difference 0 1) (sourceB2404 + difference 1 0) sourceC2404) = raw32962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32962; decide +kernel
    rw [ha]
    exact (canonical32962 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2404 + difference 1 1) (sourceB2404 + difference 1 1) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2404 + difference 1 1) (sourceB2404 + difference 1 1) sourceC2404) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2404 + difference 2 1) (sourceB2404 + difference 1 2) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2404 + difference 2 1) (sourceB2404 + difference 1 2) sourceC2404) = raw32963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32963; decide +kernel
    rw [ha]
    exact (canonical32963 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2404 + difference 3 1) (sourceB2404 + difference 1 3) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2404 + difference 3 1) (sourceB2404 + difference 1 3) sourceC2404) = raw32964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32964; decide +kernel
    rw [ha]
    exact (canonical32964 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2404 + difference 4 1) (sourceB2404 + difference 1 4) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2404 + difference 4 1) (sourceB2404 + difference 1 4) sourceC2404) = raw29460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw29460; decide +kernel
    rw [ha]
    exact (canonical29460 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2404 + difference 5 1) (sourceB2404 + difference 1 5) sourceC2404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2404 + difference 5 1) (sourceB2404 + difference 1 5) sourceC2404) = raw32965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2404 sourceB2404 sourceC2404 difference raw32965; decide +kernel
    rw [ha]
    exact (canonical32965 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2404 + sourceB2404) sourceC2404) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2404 + sourceB2404) sourceC2404) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2404 sourceB2404 sourceC2404 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2404 sourceB2404 sourceC2404
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2404, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1936 : Integer.Sparse.reindex keyMap MixedData.row1936 = numericRow1936 := by decide +kernel

theorem numericCheck1936 (x : Master → ℝ) : Integer.Sparse.eval numericRow1936 x =
    (1 : ℝ) * reducedSource1936 x := by
  norm_num [numericRow1936, reducedSource1936, Integer.Sparse.eval, Sparse.eval, nodeValue1703, nodeValue1704, nodeValue1709, nodeValue1721, nodeValue3458, nodeValue3461, nodeValue3465, nodeValue3529, nodeValue3530, nodeValue3535, nodeValue3542, nodeValue3587, nodeValue3588, nodeValue3592, nodeValue3617, nodeValue3619, nodeValue3621, nodeValue3774, nodeValue3952, nodeValue3961, nodeValue3962]

theorem reindexCheck1938 : Integer.Sparse.reindex keyMap MixedData.row1938 = numericRow1938 := by decide +kernel

theorem numericCheck1938 (x : Master → ℝ) : Integer.Sparse.eval numericRow1938 x =
    (1 : ℝ) * reducedSource1938 x := by
  norm_num [numericRow1938, reducedSource1938, Integer.Sparse.eval, Sparse.eval, nodeValue1711, nodeValue1712, nodeValue1715, nodeValue1720, nodeValue1734, nodeValue3451, nodeValue3457, nodeValue3462, nodeValue3464, nodeValue3474, nodeValue3486, nodeValue3523, nodeValue3537, nodeValue3538, nodeValue3541, nodeValue3569, nodeValue3570, nodeValue3573, nodeValue3578, nodeValue3590, nodeValue3591, nodeValue3595, nodeValue3624, nodeValue3626, nodeValue3631, nodeValue3766, nodeValue3794, nodeValue3817, nodeValue3845, nodeValue3958]

theorem reindexCheck1939 : Integer.Sparse.reindex keyMap MixedData.row1939 = numericRow1939 := by decide +kernel

theorem numericCheck1939 (x : Master → ℝ) : Integer.Sparse.eval numericRow1939 x =
    (1 : ℝ) * reducedSource1939 x := by
  norm_num [numericRow1939, reducedSource1939, Integer.Sparse.eval, Sparse.eval, nodeValue1970, nodeValue2806, nodeValue2812, nodeValue2879, nodeValue3498, nodeValue4084]

theorem reindexCheck1940 : Integer.Sparse.reindex keyMap MixedData.row1940 = numericRow1940 := by decide +kernel

theorem numericCheck1940 (x : Master → ℝ) : Integer.Sparse.eval numericRow1940 x =
    (1 : ℝ) * reducedSource1940 x := by
  norm_num [numericRow1940, reducedSource1940, Integer.Sparse.eval, Sparse.eval, nodeValue2607, nodeValue3067, nodeValue3751, nodeValue3866, nodeValue3867, nodeValue4087]

theorem reindexCheck1943 : Integer.Sparse.reindex keyMap MixedData.row1943 = numericRow1943 := by decide +kernel

theorem numericCheck1943 (x : Master → ℝ) : Integer.Sparse.eval numericRow1943 x =
    (1 : ℝ) * reducedSource1943 x := by
  norm_num [numericRow1943, reducedSource1943, Integer.Sparse.eval, Sparse.eval, nodeValue2353, nodeValue2355, nodeValue2356, nodeValue2362, nodeValue2590, nodeValue3732, nodeValue4092]

theorem reindexCheck1946 : Integer.Sparse.reindex keyMap MixedData.row1946 = numericRow1946 := by decide +kernel

theorem numericCheck1946 (x : Master → ℝ) : Integer.Sparse.eval numericRow1946 x =
    (1 : ℝ) * reducedSource1946 x := by
  norm_num [numericRow1946, reducedSource1946, Integer.Sparse.eval, Sparse.eval, nodeValue3255, nodeValue3257, nodeValue3261, nodeValue3299, nodeValue3455, nodeValue3456, nodeValue3483, nodeValue3510, nodeValue3511, nodeValue3519, nodeValue3520, nodeValue3521, nodeValue3544, nodeValue3546, nodeValue3554, nodeValue3562, nodeValue3563, nodeValue3798, nodeValue3836, nodeValue3843, nodeValue3844]

theorem reindexCheck1947 : Integer.Sparse.reindex keyMap MixedData.row1947 = numericRow1947 := by decide +kernel

theorem numericCheck1947 (x : Master → ℝ) : Integer.Sparse.eval numericRow1947 x =
    (1 : ℝ) * reducedSource1947 x := by
  norm_num [numericRow1947, reducedSource1947, Integer.Sparse.eval, Sparse.eval, nodeValue2349, nodeValue2351, nodeValue2354, nodeValue2556, nodeValue3721, nodeValue4091]

theorem reindexCheck1951 : Integer.Sparse.reindex keyMap MixedData.row1951 = numericRow1951 := by decide +kernel

theorem numericCheck1951 (x : Master → ℝ) : Integer.Sparse.eval numericRow1951 x =
    (1 : ℝ) * reducedSource1951 x := by
  norm_num [numericRow1951, reducedSource1951, Integer.Sparse.eval, Sparse.eval, nodeValue2347, nodeValue2348, nodeValue2350, nodeValue2353, nodeValue2553, nodeValue3719, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1936 (mixedVector B) = 0 := by
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h3458 : mixedVector B (Sum.inr 3458) = Sparse.eval nodeValue3458 (mixedVector B) := by
    change mixedMoment B node3458 node3458Labels = _
    exact sound3458 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3465 : mixedVector B (Sum.inr 3465) = Sparse.eval nodeValue3465 (mixedVector B) := by
    change mixedMoment B node3465 node3465Labels = _
    exact sound3465 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3587 : mixedVector B (Sum.inr 3587) = Sparse.eval nodeValue3587 (mixedVector B) := by
    change mixedMoment B node3587 node3587Labels = _
    exact sound3587 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h3592 : mixedVector B (Sum.inr 3592) = Sparse.eval nodeValue3592 (mixedVector B) := by
    change mixedMoment B node3592 node3592Labels = _
    exact sound3592 B hB hF
  have h3617 : mixedVector B (Sum.inr 3617) = Sparse.eval nodeValue3617 (mixedVector B) := by
    change mixedMoment B node3617 node3617Labels = _
    exact sound3617 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h3621 : mixedVector B (Sum.inr 3621) = Sparse.eval nodeValue3621 (mixedVector B) := by
    change mixedMoment B node3621 node3621Labels = _
    exact sound3621 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3952 : mixedVector B (Sum.inr 3952) = Sparse.eval nodeValue3952 (mixedVector B) := by
    change mixedMoment B node3952 node3952Labels = _
    exact sound3952 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h3962 : mixedVector B (Sum.inr 3962) = Sparse.eval nodeValue3962 (mixedVector B) := by
    change mixedMoment B node3962 node3962Labels = _
    exact sound3962 B hB hF
  simpa only [sourceForm2383, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1703, h1704, h1709, h1721, h3458, h3461, h3465, h3529, h3530, h3535, h3542, h3587, h3588, h3592, h3617, h3619, h3621, h3774, h3952, h3961, h3962, reducedSource1936] using sourceEq2383 B hB

theorem rowSound1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1936 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1936, numericCheck1936, reducedZero1936 B hB hF, mul_zero]

theorem reducedZero1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1938 (mixedVector B) = 0 := by
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3462 : mixedVector B (Sum.inr 3462) = Sparse.eval nodeValue3462 (mixedVector B) := by
    change mixedMoment B node3462 node3462Labels = _
    exact sound3462 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3590 : mixedVector B (Sum.inr 3590) = Sparse.eval nodeValue3590 (mixedVector B) := by
    change mixedMoment B node3590 node3590Labels = _
    exact sound3590 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3794 : mixedVector B (Sum.inr 3794) = Sparse.eval nodeValue3794 (mixedVector B) := by
    change mixedMoment B node3794 node3794Labels = _
    exact sound3794 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  simpa only [sourceForm2387, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1711, h1712, h1715, h1720, h1734, h3451, h3457, h3462, h3464, h3474, h3486, h3523, h3537, h3538, h3541, h3569, h3570, h3573, h3578, h3590, h3591, h3595, h3624, h3626, h3631, h3766, h3794, h3817, h3845, h3958, reducedSource1938] using sourceEq2387 B hB

theorem rowSound1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1938 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1938, numericCheck1938, reducedZero1938 B hB hF, mul_zero]

theorem reducedZero1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1939 (mixedVector B) = 0 := by
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2806 : mixedVector B (Sum.inr 2806) = Sparse.eval nodeValue2806 (mixedVector B) := by
    change mixedMoment B node2806 node2806Labels = _
    exact sound2806 B hB hF
  have h2812 : mixedVector B (Sum.inr 2812) = Sparse.eval nodeValue2812 (mixedVector B) := by
    change mixedMoment B node2812 node2812Labels = _
    exact sound2812 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h3498 : mixedVector B (Sum.inr 3498) = Sparse.eval nodeValue3498 (mixedVector B) := by
    change mixedMoment B node3498 node3498Labels = _
    exact sound3498 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2388, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1970, h2806, h2812, h2879, h3498, h4084, reducedSource1939] using sourceEq2388 B hB

theorem rowSound1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1939 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1939, numericCheck1939, reducedZero1939 B hB hF, mul_zero]

theorem reducedZero1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1940 (mixedVector B) = 0 := by
  have h2607 : mixedVector B (Sum.inr 2607) = Sparse.eval nodeValue2607 (mixedVector B) := by
    change mixedMoment B node2607 node2607Labels = _
    exact sound2607 B hB hF
  have h3067 : mixedVector B (Sum.inr 3067) = Sparse.eval nodeValue3067 (mixedVector B) := by
    change mixedMoment B node3067 node3067Labels = _
    exact sound3067 B hB hF
  have h3751 : mixedVector B (Sum.inr 3751) = Sparse.eval nodeValue3751 (mixedVector B) := by
    change mixedMoment B node3751 node3751Labels = _
    exact sound3751 B hB hF
  have h3866 : mixedVector B (Sum.inr 3866) = Sparse.eval nodeValue3866 (mixedVector B) := by
    change mixedMoment B node3866 node3866Labels = _
    exact sound3866 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm2390, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2607, h3067, h3751, h3866, h3867, h4087, reducedSource1940] using sourceEq2390 B hB

theorem rowSound1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1940 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1940, numericCheck1940, reducedZero1940 B hB hF, mul_zero]

theorem reducedZero1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1943 (mixedVector B) = 0 := by
  have h2353 : mixedVector B (Sum.inr 2353) = Sparse.eval nodeValue2353 (mixedVector B) := by
    change mixedMoment B node2353 node2353Labels = _
    exact sound2353 B hB hF
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2393, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2353, h2355, h2356, h2362, h2590, h3732, h4092, reducedSource1943] using sourceEq2393 B hB

theorem rowSound1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1943 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1943, numericCheck1943, reducedZero1943 B hB hF, mul_zero]

theorem reducedZero1946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1946 (mixedVector B) = 0 := by
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h3456 : mixedVector B (Sum.inr 3456) = Sparse.eval nodeValue3456 (mixedVector B) := by
    change mixedMoment B node3456 node3456Labels = _
    exact sound3456 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3511 : mixedVector B (Sum.inr 3511) = Sparse.eval nodeValue3511 (mixedVector B) := by
    change mixedMoment B node3511 node3511Labels = _
    exact sound3511 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3563 : mixedVector B (Sum.inr 3563) = Sparse.eval nodeValue3563 (mixedVector B) := by
    change mixedMoment B node3563 node3563Labels = _
    exact sound3563 B hB hF
  have h3798 : mixedVector B (Sum.inr 3798) = Sparse.eval nodeValue3798 (mixedVector B) := by
    change mixedMoment B node3798 node3798Labels = _
    exact sound3798 B hB hF
  have h3836 : mixedVector B (Sum.inr 3836) = Sparse.eval nodeValue3836 (mixedVector B) := by
    change mixedMoment B node3836 node3836Labels = _
    exact sound3836 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  simpa only [sourceForm2398, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3255, h3257, h3261, h3299, h3455, h3456, h3483, h3510, h3511, h3519, h3520, h3521, h3544, h3546, h3554, h3562, h3563, h3798, h3836, h3843, h3844, reducedSource1946] using sourceEq2398 B hB

theorem rowSound1946 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1946 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1946, numericCheck1946, reducedZero1946 B hB hF, mul_zero]

theorem reducedZero1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1947 (mixedVector B) = 0 := by
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2351 : mixedVector B (Sum.inr 2351) = Sparse.eval nodeValue2351 (mixedVector B) := by
    change mixedMoment B node2351 node2351Labels = _
    exact sound2351 B hB hF
  have h2354 : mixedVector B (Sum.inr 2354) = Sparse.eval nodeValue2354 (mixedVector B) := by
    change mixedMoment B node2354 node2354Labels = _
    exact sound2354 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2399, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2349, h2351, h2354, h2556, h3721, h4091, reducedSource1947] using sourceEq2399 B hB

theorem rowSound1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1947 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1947, numericCheck1947, reducedZero1947 B hB hF, mul_zero]

theorem reducedZero1951 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1951 (mixedVector B) = 0 := by
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h2353 : mixedVector B (Sum.inr 2353) = Sparse.eval nodeValue2353 (mixedVector B) := by
    change mixedMoment B node2353 node2353Labels = _
    exact sound2353 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2404, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2347, h2348, h2350, h2353, h2553, h3719, h4092, reducedSource1951] using sourceEq2404 B hB

theorem rowSound1951 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1951 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1951, numericCheck1951, reducedZero1951 B hB hF, mul_zero]

theorem sourceRowsAt1936 : MixedData.sourceRows (1936 : Fin 2425) =
    MixedData.row1936 := by decide +kernel

theorem sourceRowsAt1937 : MixedData.sourceRows (1937 : Fin 2425) =
    MixedData.row1937 := by decide +kernel

theorem sourceRowsAt1938 : MixedData.sourceRows (1938 : Fin 2425) =
    MixedData.row1938 := by decide +kernel

theorem sourceRowsAt1939 : MixedData.sourceRows (1939 : Fin 2425) =
    MixedData.row1939 := by decide +kernel

theorem sourceRowsAt1940 : MixedData.sourceRows (1940 : Fin 2425) =
    MixedData.row1940 := by decide +kernel

theorem sourceRowsAt1941 : MixedData.sourceRows (1941 : Fin 2425) =
    MixedData.row1941 := by decide +kernel

theorem sourceRowsAt1942 : MixedData.sourceRows (1942 : Fin 2425) =
    MixedData.row1942 := by decide +kernel

theorem sourceRowsAt1943 : MixedData.sourceRows (1943 : Fin 2425) =
    MixedData.row1943 := by decide +kernel

theorem sourceRowsAt1944 : MixedData.sourceRows (1944 : Fin 2425) =
    MixedData.row1944 := by decide +kernel

theorem sourceRowsAt1945 : MixedData.sourceRows (1945 : Fin 2425) =
    MixedData.row1945 := by decide +kernel

theorem sourceRowsAt1946 : MixedData.sourceRows (1946 : Fin 2425) =
    MixedData.row1946 := by decide +kernel

theorem sourceRowsAt1947 : MixedData.sourceRows (1947 : Fin 2425) =
    MixedData.row1947 := by decide +kernel

theorem sourceRowsAt1948 : MixedData.sourceRows (1948 : Fin 2425) =
    MixedData.row1948 := by decide +kernel

theorem sourceRowsAt1949 : MixedData.sourceRows (1949 : Fin 2425) =
    MixedData.row1949 := by decide +kernel

theorem sourceRowsAt1950 : MixedData.sourceRows (1950 : Fin 2425) =
    MixedData.row1950 := by decide +kernel

theorem sourceRowsAt1951 : MixedData.sourceRows (1951 : Fin 2425) =
    MixedData.row1951 := by decide +kernel

theorem chunkSound121_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 121) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1936 ∨ k.val = 1937 ∨ k.val = 1938 ∨ k.val = 1939 ∨ k.val = 1940 ∨ k.val = 1941 ∨ k.val = 1942 ∨ k.val = 1943 ∨ k.val = 1944 ∨ k.val = 1945 ∨ k.val = 1946 ∨ k.val = 1947 ∨ k.val = 1948 ∨ k.val = 1949 ∨ k.val = 1950 ∨ k.val = 1951 := by omega
  rcases heq with h1936 | h1937 | h1938 | h1939 | h1940 | h1941 | h1942 | h1943 | h1944 | h1945 | h1946 | h1947 | h1948 | h1949 | h1950 | h1951
  · have he : k = (1936 : Fin 2425) := Fin.ext h1936
    subst k
    rw [sourceRowsAt1936]
    exact rowSound1936 B hB hF
  · have he : k = (1937 : Fin 2425) := Fin.ext h1937
    subst k
    rw [sourceRowsAt1937]
    exact rowSound1937_e B hB hF
  · have he : k = (1938 : Fin 2425) := Fin.ext h1938
    subst k
    rw [sourceRowsAt1938]
    exact rowSound1938 B hB hF
  · have he : k = (1939 : Fin 2425) := Fin.ext h1939
    subst k
    rw [sourceRowsAt1939]
    exact rowSound1939 B hB hF
  · have he : k = (1940 : Fin 2425) := Fin.ext h1940
    subst k
    rw [sourceRowsAt1940]
    exact rowSound1940 B hB hF
  · have he : k = (1941 : Fin 2425) := Fin.ext h1941
    subst k
    rw [sourceRowsAt1941]
    exact rowSound1941_e B hB hF
  · have he : k = (1942 : Fin 2425) := Fin.ext h1942
    subst k
    rw [sourceRowsAt1942]
    exact rowSound1942_e B hB hF
  · have he : k = (1943 : Fin 2425) := Fin.ext h1943
    subst k
    rw [sourceRowsAt1943]
    exact rowSound1943 B hB hF
  · have he : k = (1944 : Fin 2425) := Fin.ext h1944
    subst k
    rw [sourceRowsAt1944]
    exact rowSound1944_e B hB hF
  · have he : k = (1945 : Fin 2425) := Fin.ext h1945
    subst k
    rw [sourceRowsAt1945]
    exact rowSound1945_e B hB hF
  · have he : k = (1946 : Fin 2425) := Fin.ext h1946
    subst k
    rw [sourceRowsAt1946]
    exact rowSound1946 B hB hF
  · have he : k = (1947 : Fin 2425) := Fin.ext h1947
    subst k
    rw [sourceRowsAt1947]
    exact rowSound1947 B hB hF
  · have he : k = (1948 : Fin 2425) := Fin.ext h1948
    subst k
    rw [sourceRowsAt1948]
    exact rowSound1948_e B hB hF
  · have he : k = (1949 : Fin 2425) := Fin.ext h1949
    subst k
    rw [sourceRowsAt1949]
    exact rowSound1949_e B hB hF
  · have he : k = (1950 : Fin 2425) := Fin.ext h1950
    subst k
    rw [sourceRowsAt1950]
    exact rowSound1950_e B hB hF
  · have he : k = (1951 : Fin 2425) := Fin.ext h1951
    subst k
    rw [sourceRowsAt1951]
    exact rowSound1951 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e_oai
