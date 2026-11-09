-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:36:00.254585+00:00
-- url     : https://prove2.me/submissions/380e7259-993f-4da6-9ddd-7f26821e0a27

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
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

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15358 raw15358Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw15358 raw15358Labels = mixedMoment B raw15358step0 raw15358step0Labels := by
      have hz : ∀ j, raw15358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15358step0 = (fun i j => raw15358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15358step0 raw15358; decide +kernel
      have hl : raw15358step0Labels = raw15358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15358 raw15358Labels permutation346 hz
    mixedMoment B raw15358step0 raw15358step0Labels = mixedMoment B raw15358step1 raw15358step1Labels := by
      have ha : raw15358step1 = (fun i j => raw15358step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15358step1 raw15358step0; decide +kernel
      have hl : raw15358step1Labels = raw15358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15358step0 raw15358step0Labels permutation33 permutation2
    _ = mixedMoment B node3198 node3198Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15360 raw15360Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw15360 raw15360Labels = mixedMoment B raw15360step0 raw15360step0Labels := by
      have hz : ∀ j, raw15360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15360step0 = (fun i j => raw15360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15360step0 raw15360; decide +kernel
      have hl : raw15360step0Labels = raw15360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360 raw15360Labels permutation346 hz
    mixedMoment B raw15360step0 raw15360step0Labels = mixedMoment B raw15360step1 raw15360step1Labels := by
      have hz : ∀ j, raw15360step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw15360step1 = (fun i j => raw15360step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw15360step1 raw15360step0; decide +kernel
      have hl : raw15360step1Labels = raw15360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360step0 raw15360step0Labels permutation32 hz
    mixedMoment B raw15360step1 raw15360step1Labels = mixedMoment B raw15360step2 raw15360step2Labels := by
      have ha : raw15360step2 = (fun i j => raw15360step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15360step2 raw15360step1; decide +kernel
      have hl : raw15360step2Labels = raw15360step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15360step1 raw15360step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical15376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15376 raw15376Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw15376 raw15376Labels = mixedMoment B raw15376step0 raw15376step0Labels := by
      have hz : ∀ j, raw15376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15376step0 = (fun i j => raw15376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15376step0 raw15376; decide +kernel
      have hl : raw15376step0Labels = raw15376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15376 raw15376Labels permutation346 hz
    mixedMoment B raw15376step0 raw15376step0Labels = mixedMoment B raw15376step1 raw15376step1Labels := by
      have ha : raw15376step1 = (fun i j => raw15376step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15376step1 raw15376step0; decide +kernel
      have hl : raw15376step1Labels = raw15376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15376step0 raw15376step0Labels permutation125 permutation2
    mixedMoment B raw15376step1 raw15376step1Labels = mixedMoment B raw15376step2 raw15376step2Labels := by
      have ha : raw15376step2 = -raw15376step1 := by apply Matrix.ext; change ∀ i j, raw15376step2 i j = -(raw15376step1 i j); unfold raw15376step2 raw15376step1; decide +kernel
      have hl : raw15376step2Labels = raw15376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15639 raw15639Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw15639 raw15639Labels = mixedMoment B raw15639step0 raw15639step0Labels := by
      have hz : ∀ j, raw15639 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw15639step0 = (fun i j => raw15639 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw15639step0 raw15639; decide +kernel
      have hl : raw15639step0Labels = raw15639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15639 raw15639Labels permutation152 hz
    mixedMoment B raw15639step0 raw15639step0Labels = mixedMoment B raw15639step1 raw15639step1Labels := by
      have ha : raw15639step1 = (fun i j => raw15639step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15639step1 raw15639step0; decide +kernel
      have hl : raw15639step1Labels = raw15639step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15639step0 raw15639step0Labels permutation122 permutation0
    mixedMoment B raw15639step1 raw15639step1Labels = mixedMoment B raw15639step2 raw15639step2Labels := by
      have ha : raw15639step2 = -raw15639step1 := by apply Matrix.ext; change ∀ i j, raw15639step2 i j = -(raw15639step1 i j); unfold raw15639step2 raw15639step1; decide +kernel
      have hl : raw15639step2Labels = raw15639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical15643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15643 raw15643Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw15643 raw15643Labels = mixedMoment B raw15643step0 raw15643step0Labels := by
      have ha : raw15643step0 = (fun i j => raw15643 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15643step0 raw15643; decide +kernel
      have hl : raw15643step0Labels = raw15643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15643 raw15643Labels permutation153 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical15657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15657 raw15657Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15657 raw15657Labels = mixedMoment B raw15657step0 raw15657step0Labels := by
      have ha : raw15657step0 = (fun i j => raw15657 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15657step0 raw15657; decide +kernel
      have hl : raw15657step0Labels = raw15657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15657 raw15657Labels permutation587 permutation2
    mixedMoment B raw15657step0 raw15657step0Labels = mixedMoment B raw15657step1 raw15657step1Labels := by
      have ha : raw15657step1 = -raw15657step0 := by apply Matrix.ext; change ∀ i j, raw15657step1 i j = -(raw15657step0 i j); unfold raw15657step1 raw15657step0; decide +kernel
      have hl : raw15657step1Labels = raw15657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16536 raw16536Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw16536 raw16536Labels = mixedMoment B raw16536step0 raw16536step0Labels := by
      have hz : ∀ j, raw16536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16536step0 = (fun i j => raw16536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16536step0 raw16536; decide +kernel
      have hl : raw16536step0Labels = raw16536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16536 raw16536Labels permutation346 hz
    mixedMoment B raw16536step0 raw16536step0Labels = mixedMoment B raw16536step1 raw16536step1Labels := by
      have ha : raw16536step1 = (fun i j => raw16536step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16536step1 raw16536step0; decide +kernel
      have hl : raw16536step1Labels = raw16536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16536step0 raw16536step0Labels permutation33 permutation2
    _ = mixedMoment B node3174 node3174Labels := by rfl

theorem canonical16538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16538 raw16538Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw16538 raw16538Labels = mixedMoment B raw16538step0 raw16538step0Labels := by
      have hz : ∀ j, raw16538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16538step0 = (fun i j => raw16538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16538step0 raw16538; decide +kernel
      have hl : raw16538step0Labels = raw16538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538 raw16538Labels permutation346 hz
    mixedMoment B raw16538step0 raw16538step0Labels = mixedMoment B raw16538step1 raw16538step1Labels := by
      have hz : ∀ j, raw16538step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw16538step1 = (fun i j => raw16538step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw16538step1 raw16538step0; decide +kernel
      have hl : raw16538step1Labels = raw16538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538step0 raw16538step0Labels permutation32 hz
    mixedMoment B raw16538step1 raw16538step1Labels = mixedMoment B raw16538step2 raw16538step2Labels := by
      have ha : raw16538step2 = (fun i j => raw16538step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16538step2 raw16538step1; decide +kernel
      have hl : raw16538step2Labels = raw16538step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16538step1 raw16538step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical16542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16542 raw16542Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw16542 raw16542Labels = mixedMoment B raw16542step0 raw16542step0Labels := by
      have hz : ∀ j, raw16542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16542step0 = (fun i j => raw16542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16542step0 raw16542; decide +kernel
      have hl : raw16542step0Labels = raw16542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16542 raw16542Labels permutation346 hz
    mixedMoment B raw16542step0 raw16542step0Labels = mixedMoment B raw16542step1 raw16542step1Labels := by
      have ha : raw16542step1 = (fun i j => raw16542step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16542step1 raw16542step0; decide +kernel
      have hl : raw16542step1Labels = raw16542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16542step0 raw16542step0Labels permutation126 permutation2
    mixedMoment B raw16542step1 raw16542step1Labels = mixedMoment B raw16542step2 raw16542step2Labels := by
      have ha : raw16542step2 = -raw16542step1 := by apply Matrix.ext; change ∀ i j, raw16542step2 i j = -(raw16542step1 i j); unfold raw16542step2 raw16542step1; decide +kernel
      have hl : raw16542step2Labels = raw16542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18342 raw18342Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw18342 raw18342Labels = mixedMoment B raw18342step0 raw18342step0Labels := by
      have hz : ∀ j, raw18342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18342step0 = (fun i j => raw18342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18342step0 raw18342; decide +kernel
      have hl : raw18342step0Labels = raw18342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342 raw18342Labels permutation434 hz
    mixedMoment B raw18342step0 raw18342step0Labels = mixedMoment B raw18342step1 raw18342step1Labels := by
      have hz : ∀ j, raw18342step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18342step1 = (fun i j => raw18342step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18342step1 raw18342step0; decide +kernel
      have hl : raw18342step1Labels = raw18342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342step0 raw18342step0Labels permutation80 hz
    mixedMoment B raw18342step1 raw18342step1Labels = mixedMoment B raw18342step2 raw18342step2Labels := by
      have hz : ∀ i, raw18342step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18342step2 = (fun i j => raw18342step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18342step2 raw18342step1; decide +kernel
      have hl : raw18342step2Labels = (fun j => raw18342step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18342step1 raw18342step1Labels permutation6 hz
    mixedMoment B raw18342step2 raw18342step2Labels = mixedMoment B raw18342step3 raw18342step3Labels := by
      have ha : raw18342step3 = (fun i j => raw18342step2 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18342step3 raw18342step2; decide +kernel
      have hl : raw18342step3Labels = raw18342step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18342step2 raw18342step2Labels permutation30 permutation0
    mixedMoment B raw18342step3 raw18342step3Labels = mixedMoment B raw18342step4 raw18342step4Labels := by
      have ha : raw18342step4 = -raw18342step3 := by apply Matrix.ext; change ∀ i j, raw18342step4 i j = -(raw18342step3 i j); unfold raw18342step4 raw18342step3; decide +kernel
      have hl : raw18342step4Labels = raw18342step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical18343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18343 raw18343Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw18343 raw18343Labels = mixedMoment B raw18343step0 raw18343step0Labels := by
      have hz : ∀ j, raw18343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18343step0 = (fun i j => raw18343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18343step0 raw18343; decide +kernel
      have hl : raw18343step0Labels = raw18343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18343 raw18343Labels permutation434 hz
    mixedMoment B raw18343step0 raw18343step0Labels = mixedMoment B raw18343step1 raw18343step1Labels := by
      have hz : ∀ i, raw18343step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18343step1 = (fun i j => raw18343step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18343step1 raw18343step0; decide +kernel
      have hl : raw18343step1Labels = (fun j => raw18343step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18343step0 raw18343step0Labels permutation6 hz
    mixedMoment B raw18343step1 raw18343step1Labels = mixedMoment B raw18343step2 raw18343step2Labels := by
      have ha : raw18343step2 = (fun i j => raw18343step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18343step2 raw18343step1; decide +kernel
      have hl : raw18343step2Labels = raw18343step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18343step1 raw18343step1Labels permutation149 permutation0
    mixedMoment B raw18343step2 raw18343step2Labels = mixedMoment B raw18343step3 raw18343step3Labels := by
      have ha : raw18343step3 = -raw18343step2 := by apply Matrix.ext; change ∀ i j, raw18343step3 i j = -(raw18343step2 i j); unfold raw18343step3 raw18343step2; decide +kernel
      have hl : raw18343step3Labels = raw18343step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical18344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18344 raw18344Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw18344 raw18344Labels = mixedMoment B raw18344step0 raw18344step0Labels := by
      have hz : ∀ j, raw18344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18344step0 = (fun i j => raw18344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18344step0 raw18344; decide +kernel
      have hl : raw18344step0Labels = raw18344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18344 raw18344Labels permutation346 hz
    mixedMoment B raw18344step0 raw18344step0Labels = mixedMoment B raw18344step1 raw18344step1Labels := by
      have hz : ∀ i, raw18344step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18344step1 = (fun i j => raw18344step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18344step1 raw18344step0; decide +kernel
      have hl : raw18344step1Labels = (fun j => raw18344step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18344step0 raw18344step0Labels permutation6 hz
    mixedMoment B raw18344step1 raw18344step1Labels = mixedMoment B raw18344step2 raw18344step2Labels := by
      have ha : raw18344step2 = (fun i j => raw18344step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18344step2 raw18344step1; decide +kernel
      have hl : raw18344step2Labels = raw18344step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18344step1 raw18344step1Labels permutation149 permutation0
    mixedMoment B raw18344step2 raw18344step2Labels = mixedMoment B raw18344step3 raw18344step3Labels := by
      have ha : raw18344step3 = -raw18344step2 := by apply Matrix.ext; change ∀ i j, raw18344step3 i j = -(raw18344step2 i j); unfold raw18344step3 raw18344step2; decide +kernel
      have hl : raw18344step3Labels = raw18344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20080 raw20080Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20080 raw20080Labels = mixedMoment B raw20080step0 raw20080step0Labels := by
      have hz : ∀ j, raw20080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20080step0 = (fun i j => raw20080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20080step0 raw20080; decide +kernel
      have hl : raw20080step0Labels = raw20080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080 raw20080Labels permutation434 hz
    mixedMoment B raw20080step0 raw20080step0Labels = mixedMoment B raw20080step1 raw20080step1Labels := by
      have hz : ∀ j, raw20080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20080step1 = (fun i j => raw20080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20080step1 raw20080step0; decide +kernel
      have hl : raw20080step1Labels = raw20080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080step0 raw20080step0Labels permutation80 hz
    mixedMoment B raw20080step1 raw20080step1Labels = mixedMoment B raw20080step2 raw20080step2Labels := by
      have hz : ∀ i, raw20080step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20080step2 = (fun i j => raw20080step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20080step2 raw20080step1; decide +kernel
      have hl : raw20080step2Labels = (fun j => raw20080step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20080step1 raw20080step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

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

theorem canonical20196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20196 raw20196Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw20196 raw20196Labels = mixedMoment B raw20196step0 raw20196step0Labels := by
      have hz : ∀ j, raw20196 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20196step0 = (fun i j => raw20196 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20196step0 raw20196; decide +kernel
      have hl : raw20196step0Labels = raw20196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196 raw20196Labels permutation520 hz
    mixedMoment B raw20196step0 raw20196step0Labels = mixedMoment B raw20196step1 raw20196step1Labels := by
      have hz : ∀ j, raw20196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20196step1 = (fun i j => raw20196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20196step1 raw20196step0; decide +kernel
      have hl : raw20196step1Labels = raw20196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196step0 raw20196step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical22305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22305 raw22305Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22305 raw22305Labels = mixedMoment B raw22305step0 raw22305step0Labels := by
      have hz : ∀ j, raw22305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22305step0 = (fun i j => raw22305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22305step0 raw22305; decide +kernel
      have hl : raw22305step0Labels = raw22305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22305 raw22305Labels permutation434 hz
    mixedMoment B raw22305step0 raw22305step0Labels = mixedMoment B raw22305step1 raw22305step1Labels := by
      have hz : ∀ i, raw22305step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22305step1 = (fun i j => raw22305step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22305step1 raw22305step0; decide +kernel
      have hl : raw22305step1Labels = (fun j => raw22305step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22305step0 raw22305step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

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

theorem canonical22353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22353 raw22353Labels = mixedMoment B node910 node910Labels := by
  calc
    mixedMoment B raw22353 raw22353Labels = mixedMoment B raw22353step0 raw22353step0Labels := by
      have ha : raw22353step0 = (fun i j => raw22353 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22353step0 raw22353; decide +kernel
      have hl : raw22353step0Labels = raw22353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22353 raw22353Labels permutation158 permutation2
    _ = mixedMoment B node910 node910Labels := by rfl

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

theorem canonical25239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25239 raw25239Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25239 raw25239Labels = mixedMoment B raw25239step0 raw25239step0Labels := by
      have hz : ∀ j, raw25239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25239step0 = (fun i j => raw25239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25239step0 raw25239; decide +kernel
      have hl : raw25239step0Labels = raw25239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25239 raw25239Labels permutation346 hz
    _ = mixedMoment B node950 node950Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical27373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27373 raw27373Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw27373 raw27373Labels = mixedMoment B raw27373step0 raw27373step0Labels := by
      have ha : raw27373step0 = (fun i j => raw27373 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27373step0 raw27373; decide +kernel
      have hl : raw27373step0Labels = raw27373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27373 raw27373Labels permutation160 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

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

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical2935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2935 raw2935Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2935 raw2935Labels = mixedMoment B raw2935step0 raw2935step0Labels := by
      have hz : ∀ j, raw2935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2935step0 = (fun i j => raw2935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2935step0 raw2935; decide +kernel
      have hl : raw2935step0Labels = raw2935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935 raw2935Labels permutation520 hz
    mixedMoment B raw2935step0 raw2935step0Labels = mixedMoment B raw2935step1 raw2935step1Labels := by
      have hz : ∀ j, raw2935step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2935step1 = (fun i j => raw2935step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2935step1 raw2935step0; decide +kernel
      have hl : raw2935step1Labels = raw2935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step0 raw2935step0Labels permutation104 hz
    mixedMoment B raw2935step1 raw2935step1Labels = mixedMoment B raw2935step2 raw2935step2Labels := by
      have hz : ∀ j, raw2935step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2935step2 = (fun i j => raw2935step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2935step2 raw2935step1; decide +kernel
      have hl : raw2935step2Labels = raw2935step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step1 raw2935step1Labels permutation20 hz
    mixedMoment B raw2935step2 raw2935step2Labels = mixedMoment B raw2935step3 raw2935step3Labels := by
      have hz : ∀ i, raw2935step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2935step3 = (fun i j => raw2935step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2935step3 raw2935step2; decide +kernel
      have hl : raw2935step3Labels = (fun j => raw2935step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2935step2 raw2935step2Labels permutation6 hz
    mixedMoment B raw2935step3 raw2935step3Labels = mixedMoment B raw2935step4 raw2935step4Labels := by
      have ha : raw2935step4 = (fun i j => raw2935step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2935step4 raw2935step3; decide +kernel
      have hl : raw2935step4Labels = raw2935step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2935step3 raw2935step3Labels permutation7 permutation0
    mixedMoment B raw2935step4 raw2935step4Labels = mixedMoment B raw2935step5 raw2935step5Labels := by
      have ha : raw2935step5 = -raw2935step4 := by apply Matrix.ext; change ∀ i j, raw2935step5 i j = -(raw2935step4 i j); unfold raw2935step5 raw2935step4; decide +kernel
      have hl : raw2935step5Labels = raw2935step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29295 raw29295Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29295 raw29295Labels = mixedMoment B raw29295step0 raw29295step0Labels := by
      have hz : ∀ j, raw29295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29295step0 = (fun i j => raw29295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29295step0 raw29295; decide +kernel
      have hl : raw29295step0Labels = raw29295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29295 raw29295Labels permutation434 hz
    mixedMoment B raw29295step0 raw29295step0Labels = mixedMoment B raw29295step1 raw29295step1Labels := by
      have hz : ∀ i, raw29295step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29295step1 = (fun i j => raw29295step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29295step1 raw29295step0; decide +kernel
      have hl : raw29295step1Labels = (fun j => raw29295step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29295step0 raw29295step0Labels permutation6 hz
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29296 raw29296Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw29296 raw29296Labels = mixedMoment B raw29296step0 raw29296step0Labels := by
      have hz : ∀ i, raw29296 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29296step0 = (fun i j => raw29296 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29296step0 raw29296; decide +kernel
      have hl : raw29296step0Labels = (fun j => raw29296Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29296 raw29296Labels permutation6 hz
    mixedMoment B raw29296step0 raw29296step0Labels = mixedMoment B raw29296step1 raw29296step1Labels := by
      have ha : raw29296step1 = (fun i j => raw29296step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29296step1 raw29296step0; decide +kernel
      have hl : raw29296step1Labels = raw29296step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29296step0 raw29296step0Labels permutation158 permutation0
    _ = mixedMoment B node4077 node4077Labels := by rfl

theorem canonical29297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29297 raw29297Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29297 raw29297Labels = mixedMoment B raw29297step0 raw29297step0Labels := by
      have hz : ∀ j, raw29297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29297step0 = (fun i j => raw29297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29297step0 raw29297; decide +kernel
      have hl : raw29297step0Labels = raw29297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29297 raw29297Labels permutation346 hz
    mixedMoment B raw29297step0 raw29297step0Labels = mixedMoment B raw29297step1 raw29297step1Labels := by
      have hz : ∀ i, raw29297step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29297step1 = (fun i j => raw29297step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29297step1 raw29297step0; decide +kernel
      have hl : raw29297step1Labels = (fun j => raw29297step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29297step0 raw29297step0Labels permutation6 hz
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29298 raw29298Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw29298 raw29298Labels = mixedMoment B raw29298step0 raw29298step0Labels := by
      have hz : ∀ i, raw29298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29298step0 = (fun i j => raw29298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29298step0 raw29298; decide +kernel
      have hl : raw29298step0Labels = (fun j => raw29298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29298 raw29298Labels permutation6 hz
    _ = mixedMoment B node4077 node4077Labels := by rfl

theorem canonical29299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29299 raw29299Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw29299 raw29299Labels = mixedMoment B raw29299step0 raw29299step0Labels := by
      have hz : ∀ j, raw29299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29299step0 = (fun i j => raw29299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29299step0 raw29299; decide +kernel
      have hl : raw29299step0Labels = raw29299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299 raw29299Labels permutation434 hz
    mixedMoment B raw29299step0 raw29299step0Labels = mixedMoment B raw29299step1 raw29299step1Labels := by
      have hz : ∀ j, raw29299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29299step1 = (fun i j => raw29299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29299step1 raw29299step0; decide +kernel
      have hl : raw29299step1Labels = raw29299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299step0 raw29299step0Labels permutation80 hz
    mixedMoment B raw29299step1 raw29299step1Labels = mixedMoment B raw29299step2 raw29299step2Labels := by
      have hz : ∀ i, raw29299step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29299step2 = (fun i j => raw29299step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29299step2 raw29299step1; decide +kernel
      have hl : raw29299step2Labels = (fun j => raw29299step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29299step1 raw29299step1Labels permutation6 hz
    _ = mixedMoment B node4076 node4076Labels := by rfl

theorem canonical29300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29300 raw29300Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29300 raw29300Labels = mixedMoment B raw29300step0 raw29300step0Labels := by
      have hz : ∀ j, raw29300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29300step0 = (fun i j => raw29300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29300step0 raw29300; decide +kernel
      have hl : raw29300step0Labels = raw29300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29300 raw29300Labels permutation434 hz
    mixedMoment B raw29300step0 raw29300step0Labels = mixedMoment B raw29300step1 raw29300step1Labels := by
      have hz : ∀ i, raw29300step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29300step1 = (fun i j => raw29300step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29300step1 raw29300step0; decide +kernel
      have hl : raw29300step1Labels = (fun j => raw29300step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29300step0 raw29300step0Labels permutation6 hz
    mixedMoment B raw29300step1 raw29300step1Labels = mixedMoment B raw29300step2 raw29300step2Labels := by
      have ha : raw29300step2 = (fun i j => raw29300step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29300step2 raw29300step1; decide +kernel
      have hl : raw29300step2Labels = raw29300step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29300step1 raw29300step1Labels permutation149 permutation0
    mixedMoment B raw29300step2 raw29300step2Labels = mixedMoment B raw29300step3 raw29300step3Labels := by
      have ha : raw29300step3 = -raw29300step2 := by apply Matrix.ext; change ∀ i j, raw29300step3 i j = -(raw29300step2 i j); unfold raw29300step3 raw29300step2; decide +kernel
      have hl : raw29300step3Labels = raw29300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29301 raw29301Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29301 raw29301Labels = mixedMoment B raw29301step0 raw29301step0Labels := by
      have hz : ∀ j, raw29301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29301step0 = (fun i j => raw29301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29301step0 raw29301; decide +kernel
      have hl : raw29301step0Labels = raw29301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29301 raw29301Labels permutation346 hz
    mixedMoment B raw29301step0 raw29301step0Labels = mixedMoment B raw29301step1 raw29301step1Labels := by
      have hz : ∀ i, raw29301step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29301step1 = (fun i j => raw29301step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29301step1 raw29301step0; decide +kernel
      have hl : raw29301step1Labels = (fun j => raw29301step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29301step0 raw29301step0Labels permutation6 hz
    mixedMoment B raw29301step1 raw29301step1Labels = mixedMoment B raw29301step2 raw29301step2Labels := by
      have ha : raw29301step2 = (fun i j => raw29301step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29301step2 raw29301step1; decide +kernel
      have hl : raw29301step2Labels = raw29301step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29301step1 raw29301step1Labels permutation149 permutation0
    mixedMoment B raw29301step2 raw29301step2Labels = mixedMoment B raw29301step3 raw29301step3Labels := by
      have ha : raw29301step3 = -raw29301step2 := by apply Matrix.ext; change ∀ i j, raw29301step3 i j = -(raw29301step2 i j); unfold raw29301step3 raw29301step2; decide +kernel
      have hl : raw29301step3Labels = raw29301step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

theorem canonical29302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29302 raw29302Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw29302 raw29302Labels = mixedMoment B raw29302step0 raw29302step0Labels := by
      have hz : ∀ j, raw29302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29302step0 = (fun i j => raw29302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29302step0 raw29302; decide +kernel
      have hl : raw29302step0Labels = raw29302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29302 raw29302Labels permutation434 hz
    mixedMoment B raw29302step0 raw29302step0Labels = mixedMoment B raw29302step1 raw29302step1Labels := by
      have hz : ∀ j, raw29302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29302step1 = (fun i j => raw29302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29302step1 raw29302step0; decide +kernel
      have hl : raw29302step1Labels = raw29302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29302step0 raw29302step0Labels permutation80 hz
    mixedMoment B raw29302step1 raw29302step1Labels = mixedMoment B raw29302step2 raw29302step2Labels := by
      have hz : ∀ i, raw29302step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29302step2 = (fun i j => raw29302step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29302step2 raw29302step1; decide +kernel
      have hl : raw29302step2Labels = (fun j => raw29302step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29302step1 raw29302step1Labels permutation6 hz
    mixedMoment B raw29302step2 raw29302step2Labels = mixedMoment B raw29302step3 raw29302step3Labels := by
      have ha : raw29302step3 = (fun i j => raw29302step2 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29302step3 raw29302step2; decide +kernel
      have hl : raw29302step3Labels = raw29302step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29302step2 raw29302step2Labels permutation31 permutation0
    mixedMoment B raw29302step3 raw29302step3Labels = mixedMoment B raw29302step4 raw29302step4Labels := by
      have ha : raw29302step4 = -raw29302step3 := by apply Matrix.ext; change ∀ i j, raw29302step4 i j = -(raw29302step3 i j); unfold raw29302step4 raw29302step3; decide +kernel
      have hl : raw29302step4Labels = raw29302step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical29303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29303 raw29303Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw29303 raw29303Labels = mixedMoment B raw29303step0 raw29303step0Labels := by
      have hz : ∀ j, raw29303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29303step0 = (fun i j => raw29303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29303step0 raw29303; decide +kernel
      have hl : raw29303step0Labels = raw29303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29303 raw29303Labels permutation434 hz
    mixedMoment B raw29303step0 raw29303step0Labels = mixedMoment B raw29303step1 raw29303step1Labels := by
      have hz : ∀ i, raw29303step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29303step1 = (fun i j => raw29303step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29303step1 raw29303step0; decide +kernel
      have hl : raw29303step1Labels = (fun j => raw29303step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29303step0 raw29303step0Labels permutation6 hz
    mixedMoment B raw29303step1 raw29303step1Labels = mixedMoment B raw29303step2 raw29303step2Labels := by
      have ha : raw29303step2 = (fun i j => raw29303step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29303step2 raw29303step1; decide +kernel
      have hl : raw29303step2Labels = raw29303step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29303step1 raw29303step1Labels permutation149 permutation0
    mixedMoment B raw29303step2 raw29303step2Labels = mixedMoment B raw29303step3 raw29303step3Labels := by
      have ha : raw29303step3 = -raw29303step2 := by apply Matrix.ext; change ∀ i j, raw29303step3 i j = -(raw29303step2 i j); unfold raw29303step3 raw29303step2; decide +kernel
      have hl : raw29303step3Labels = raw29303step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical29304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29304 raw29304Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw29304 raw29304Labels = mixedMoment B raw29304step0 raw29304step0Labels := by
      have hz : ∀ j, raw29304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29304step0 = (fun i j => raw29304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29304step0 raw29304; decide +kernel
      have hl : raw29304step0Labels = raw29304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29304 raw29304Labels permutation346 hz
    mixedMoment B raw29304step0 raw29304step0Labels = mixedMoment B raw29304step1 raw29304step1Labels := by
      have hz : ∀ i, raw29304step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29304step1 = (fun i j => raw29304step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29304step1 raw29304step0; decide +kernel
      have hl : raw29304step1Labels = (fun j => raw29304step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29304step0 raw29304step0Labels permutation6 hz
    mixedMoment B raw29304step1 raw29304step1Labels = mixedMoment B raw29304step2 raw29304step2Labels := by
      have ha : raw29304step2 = (fun i j => raw29304step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29304step2 raw29304step1; decide +kernel
      have hl : raw29304step2Labels = raw29304step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29304step1 raw29304step1Labels permutation149 permutation0
    mixedMoment B raw29304step2 raw29304step2Labels = mixedMoment B raw29304step3 raw29304step3Labels := by
      have ha : raw29304step3 = -raw29304step2 := by apply Matrix.ext; change ∀ i j, raw29304step3 i j = -(raw29304step2 i j); unfold raw29304step3 raw29304step2; decide +kernel
      have hl : raw29304step3Labels = raw29304step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical29309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29309 raw29309Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw29309 raw29309Labels = mixedMoment B raw29309step0 raw29309step0Labels := by
      have hz : ∀ j, raw29309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29309step0 = (fun i j => raw29309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29309step0 raw29309; decide +kernel
      have hl : raw29309step0Labels = raw29309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29309 raw29309Labels permutation346 hz
    mixedMoment B raw29309step0 raw29309step0Labels = mixedMoment B raw29309step1 raw29309step1Labels := by
      have ha : raw29309step1 = (fun i j => raw29309step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29309step1 raw29309step0; decide +kernel
      have hl : raw29309step1Labels = raw29309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29309step0 raw29309step0Labels permutation39 permutation2
    _ = mixedMoment B node3174 node3174Labels := by rfl

theorem canonical29310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29310 raw29310Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw29310 raw29310Labels = mixedMoment B raw29310step0 raw29310step0Labels := by
      have ha : raw29310step0 = (fun i j => raw29310 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29310step0 raw29310; decide +kernel
      have hl : raw29310step0Labels = raw29310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29310 raw29310Labels permutation201 permutation2
    _ = mixedMoment B node3162 node3162Labels := by rfl

theorem canonical29311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29311 raw29311Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw29311 raw29311Labels = mixedMoment B raw29311step0 raw29311step0Labels := by
      have hz : ∀ j, raw29311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29311step0 = (fun i j => raw29311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29311step0 raw29311; decide +kernel
      have hl : raw29311step0Labels = raw29311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29311 raw29311Labels permutation346 hz
    mixedMoment B raw29311step0 raw29311step0Labels = mixedMoment B raw29311step1 raw29311step1Labels := by
      have ha : raw29311step1 = (fun i j => raw29311step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29311step1 raw29311step0; decide +kernel
      have hl : raw29311step1Labels = raw29311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29311step0 raw29311step0Labels permutation125 permutation2
    mixedMoment B raw29311step1 raw29311step1Labels = mixedMoment B raw29311step2 raw29311step2Labels := by
      have ha : raw29311step2 = -raw29311step1 := by apply Matrix.ext; change ∀ i j, raw29311step2 i j = -(raw29311step1 i j); unfold raw29311step2 raw29311step1; decide +kernel
      have hl : raw29311step2Labels = raw29311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

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

theorem canonical29312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29312 raw29312Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw29312 raw29312Labels = mixedMoment B raw29312step0 raw29312step0Labels := by
      have hz : ∀ j, raw29312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29312step0 = (fun i j => raw29312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29312step0 raw29312; decide +kernel
      have hl : raw29312step0Labels = raw29312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29312 raw29312Labels permutation346 hz
    mixedMoment B raw29312step0 raw29312step0Labels = mixedMoment B raw29312step1 raw29312step1Labels := by
      have ha : raw29312step1 = (fun i j => raw29312step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29312step1 raw29312step0; decide +kernel
      have hl : raw29312step1Labels = raw29312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29312step0 raw29312step0Labels permutation149 permutation2
    mixedMoment B raw29312step1 raw29312step1Labels = mixedMoment B raw29312step2 raw29312step2Labels := by
      have ha : raw29312step2 = -raw29312step1 := by apply Matrix.ext; change ∀ i j, raw29312step2 i j = -(raw29312step1 i j); unfold raw29312step2 raw29312step1; decide +kernel
      have hl : raw29312step2Labels = raw29312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2816 node2816Labels := by rfl

theorem canonical29313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29313 raw29313Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29313 raw29313Labels = mixedMoment B raw29313step0 raw29313step0Labels := by
      have hz : ∀ j, raw29313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29313step0 = (fun i j => raw29313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29313step0 raw29313; decide +kernel
      have hl : raw29313step0Labels = raw29313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29313 raw29313Labels permutation346 hz
    mixedMoment B raw29313step0 raw29313step0Labels = mixedMoment B raw29313step1 raw29313step1Labels := by
      have ha : raw29313step1 = (fun i j => raw29313step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29313step1 raw29313step0; decide +kernel
      have hl : raw29313step1Labels = raw29313step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29313step0 raw29313step0Labels permutation34 permutation4
    mixedMoment B raw29313step1 raw29313step1Labels = mixedMoment B raw29313step2 raw29313step2Labels := by
      have ha : raw29313step2 = -raw29313step1 := by apply Matrix.ext; change ∀ i j, raw29313step2 i j = -(raw29313step1 i j); unfold raw29313step2 raw29313step1; decide +kernel
      have hl : raw29313step2Labels = raw29313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical29314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29314 raw29314Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw29314 raw29314Labels = mixedMoment B raw29314step0 raw29314step0Labels := by
      have hz : ∀ j, raw29314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29314step0 = (fun i j => raw29314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29314step0 raw29314; decide +kernel
      have hl : raw29314step0Labels = raw29314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29314 raw29314Labels permutation346 hz
    mixedMoment B raw29314step0 raw29314step0Labels = mixedMoment B raw29314step1 raw29314step1Labels := by
      have ha : raw29314step1 = (fun i j => raw29314step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29314step1 raw29314step0; decide +kernel
      have hl : raw29314step1Labels = raw29314step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29314step0 raw29314step0Labels permutation44 permutation4
    mixedMoment B raw29314step1 raw29314step1Labels = mixedMoment B raw29314step2 raw29314step2Labels := by
      have ha : raw29314step2 = -raw29314step1 := by apply Matrix.ext; change ∀ i j, raw29314step2 i j = -(raw29314step1 i j); unfold raw29314step2 raw29314step1; decide +kernel
      have hl : raw29314step2Labels = raw29314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical29315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29315 raw29315Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw29315 raw29315Labels = mixedMoment B raw29315step0 raw29315step0Labels := by
      have ha : raw29315step0 = (fun i j => raw29315 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29315step0 raw29315; decide +kernel
      have hl : raw29315step0Labels = raw29315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29315 raw29315Labels permutation164 permutation4
    mixedMoment B raw29315step0 raw29315step0Labels = mixedMoment B raw29315step1 raw29315step1Labels := by
      have ha : raw29315step1 = -raw29315step0 := by apply Matrix.ext; change ∀ i j, raw29315step1 i j = -(raw29315step0 i j); unfold raw29315step1 raw29315step0; decide +kernel
      have hl : raw29315step1Labels = raw29315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical29316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29316 raw29316Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw29316 raw29316Labels = mixedMoment B raw29316step0 raw29316step0Labels := by
      have hz : ∀ j, raw29316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29316step0 = (fun i j => raw29316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29316step0 raw29316; decide +kernel
      have hl : raw29316step0Labels = raw29316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29316 raw29316Labels permutation346 hz
    mixedMoment B raw29316step0 raw29316step0Labels = mixedMoment B raw29316step1 raw29316step1Labels := by
      have ha : raw29316step1 = (fun i j => raw29316step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29316step1 raw29316step0; decide +kernel
      have hl : raw29316step1Labels = raw29316step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29316step0 raw29316step0Labels permutation35 permutation4
    mixedMoment B raw29316step1 raw29316step1Labels = mixedMoment B raw29316step2 raw29316step2Labels := by
      have ha : raw29316step2 = -raw29316step1 := by apply Matrix.ext; change ∀ i j, raw29316step2 i j = -(raw29316step1 i j); unfold raw29316step2 raw29316step1; decide +kernel
      have hl : raw29316step2Labels = raw29316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical29317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29317 raw29317Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw29317 raw29317Labels = mixedMoment B raw29317step0 raw29317step0Labels := by
      have hz : ∀ j, raw29317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29317step0 = (fun i j => raw29317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29317step0 raw29317; decide +kernel
      have hl : raw29317step0Labels = raw29317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29317 raw29317Labels permutation346 hz
    mixedMoment B raw29317step0 raw29317step0Labels = mixedMoment B raw29317step1 raw29317step1Labels := by
      have ha : raw29317step1 = (fun i j => raw29317step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29317step1 raw29317step0; decide +kernel
      have hl : raw29317step1Labels = raw29317step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29317step0 raw29317step0Labels permutation32 permutation4
    mixedMoment B raw29317step1 raw29317step1Labels = mixedMoment B raw29317step2 raw29317step2Labels := by
      have ha : raw29317step2 = -raw29317step1 := by apply Matrix.ext; change ∀ i j, raw29317step2 i j = -(raw29317step1 i j); unfold raw29317step2 raw29317step1; decide +kernel
      have hl : raw29317step2Labels = raw29317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical29318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29318 raw29318Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw29318 raw29318Labels = mixedMoment B raw29318step0 raw29318step0Labels := by
      have hz : ∀ j, raw29318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29318step0 = (fun i j => raw29318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29318step0 raw29318; decide +kernel
      have hl : raw29318step0Labels = raw29318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29318 raw29318Labels permutation346 hz
    mixedMoment B raw29318step0 raw29318step0Labels = mixedMoment B raw29318step1 raw29318step1Labels := by
      have ha : raw29318step1 = (fun i j => raw29318step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29318step1 raw29318step0; decide +kernel
      have hl : raw29318step1Labels = raw29318step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29318step0 raw29318step0Labels permutation34 permutation4
    mixedMoment B raw29318step1 raw29318step1Labels = mixedMoment B raw29318step2 raw29318step2Labels := by
      have ha : raw29318step2 = -raw29318step1 := by apply Matrix.ext; change ∀ i j, raw29318step2 i j = -(raw29318step1 i j); unfold raw29318step2 raw29318step1; decide +kernel
      have hl : raw29318step2Labels = raw29318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical29319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29319 raw29319Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29319 raw29319Labels = mixedMoment B raw29319step0 raw29319step0Labels := by
      have hz : ∀ j, raw29319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29319step0 = (fun i j => raw29319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29319step0 raw29319; decide +kernel
      have hl : raw29319step0Labels = raw29319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319 raw29319Labels permutation434 hz
    mixedMoment B raw29319step0 raw29319step0Labels = mixedMoment B raw29319step1 raw29319step1Labels := by
      have hz : ∀ j, raw29319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29319step1 = (fun i j => raw29319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29319step1 raw29319step0; decide +kernel
      have hl : raw29319step1Labels = raw29319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319step0 raw29319step0Labels permutation80 hz
    mixedMoment B raw29319step1 raw29319step1Labels = mixedMoment B raw29319step2 raw29319step2Labels := by
      have ha : raw29319step2 = -raw29319step1 := by apply Matrix.ext; change ∀ i j, raw29319step2 i j = -(raw29319step1 i j); unfold raw29319step2 raw29319step1; decide +kernel
      have hl : raw29319step2Labels = raw29319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical29320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29320 raw29320Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw29320 raw29320Labels = mixedMoment B raw29320step0 raw29320step0Labels := by
      have ha : raw29320step0 = (fun i j => raw29320 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29320step0 raw29320; decide +kernel
      have hl : raw29320step0Labels = raw29320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29320 raw29320Labels permutation158 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

theorem canonical29321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29321 raw29321Labels = mixedMoment B node2012 node2012Labels := by
  calc
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical29322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29322 raw29322Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw29322 raw29322Labels = mixedMoment B raw29322step0 raw29322step0Labels := by
      have ha : raw29322step0 = (fun i j => raw29322 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29322step0 raw29322; decide +kernel
      have hl : raw29322step0Labels = raw29322Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29322 raw29322Labels permutation158 permutation2
    _ = mixedMoment B node1977 node1977Labels := by rfl

theorem canonical29323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29323 raw29323Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw29323 raw29323Labels = mixedMoment B raw29323step0 raw29323step0Labels := by
      have ha : raw29323step0 = (fun i j => raw29323 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29323step0 raw29323; decide +kernel
      have hl : raw29323step0Labels = raw29323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29323 raw29323Labels permutation159 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical29324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29324 raw29324Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw29324 raw29324Labels = mixedMoment B raw29324step0 raw29324step0Labels := by
      have ha : raw29324step0 = (fun i j => raw29324 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29324step0 raw29324; decide +kernel
      have hl : raw29324step0Labels = raw29324Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29324 raw29324Labels permutation177 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical29325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29325 raw29325Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw29325 raw29325Labels = mixedMoment B raw29325step0 raw29325step0Labels := by
      have ha : raw29325step0 = (fun i j => raw29325 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29325step0 raw29325; decide +kernel
      have hl : raw29325step0Labels = raw29325Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29325 raw29325Labels permutation153 permutation2
    _ = mixedMoment B node3189 node3189Labels := by rfl

theorem canonical29326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29326 raw29326Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw29326 raw29326Labels = mixedMoment B raw29326step0 raw29326step0Labels := by
      have ha : raw29326step0 = (fun i j => raw29326 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29326step0 raw29326; decide +kernel
      have hl : raw29326step0Labels = raw29326Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29326 raw29326Labels permutation587 permutation2
    mixedMoment B raw29326step0 raw29326step0Labels = mixedMoment B raw29326step1 raw29326step1Labels := by
      have ha : raw29326step1 = -raw29326step0 := by apply Matrix.ext; change ∀ i j, raw29326step1 i j = -(raw29326step0 i j); unfold raw29326step1 raw29326step0; decide +kernel
      have hl : raw29326step1Labels = raw29326step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

theorem canonical29327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29327 raw29327Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw29327 raw29327Labels = mixedMoment B raw29327step0 raw29327step0Labels := by
      have ha : raw29327step0 = (fun i j => raw29327 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29327step0 raw29327; decide +kernel
      have hl : raw29327step0Labels = raw29327Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29327 raw29327Labels permutation686 permutation2
    mixedMoment B raw29327step0 raw29327step0Labels = mixedMoment B raw29327step1 raw29327step1Labels := by
      have ha : raw29327step1 = -raw29327step0 := by apply Matrix.ext; change ∀ i j, raw29327step1 i j = -(raw29327step0 i j); unfold raw29327step1 raw29327step0; decide +kernel
      have hl : raw29327step1Labels = raw29327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2800 node2800Labels := by rfl

theorem canonical29328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29328 raw29328Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29328 raw29328Labels = mixedMoment B raw29328step0 raw29328step0Labels := by
      have ha : raw29328step0 = (fun i j => raw29328 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29328step0 raw29328; decide +kernel
      have hl : raw29328step0Labels = raw29328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29328 raw29328Labels permutation164 permutation4
    mixedMoment B raw29328step0 raw29328step0Labels = mixedMoment B raw29328step1 raw29328step1Labels := by
      have ha : raw29328step1 = -raw29328step0 := by apply Matrix.ext; change ∀ i j, raw29328step1 i j = -(raw29328step0 i j); unfold raw29328step1 raw29328step0; decide +kernel
      have hl : raw29328step1Labels = raw29328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical29329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29329 raw29329Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29329 raw29329Labels = mixedMoment B raw29329step0 raw29329step0Labels := by
      have hz : ∀ j, raw29329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29329step0 = (fun i j => raw29329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29329step0 raw29329; decide +kernel
      have hl : raw29329step0Labels = raw29329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29329 raw29329Labels permutation434 hz
    mixedMoment B raw29329step0 raw29329step0Labels = mixedMoment B raw29329step1 raw29329step1Labels := by
      have ha : raw29329step1 = (fun i j => raw29329step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29329step1 raw29329step0; decide +kernel
      have hl : raw29329step1Labels = raw29329step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29329step0 raw29329step0Labels permutation34 permutation4
    mixedMoment B raw29329step1 raw29329step1Labels = mixedMoment B raw29329step2 raw29329step2Labels := by
      have ha : raw29329step2 = -raw29329step1 := by apply Matrix.ext; change ∀ i j, raw29329step2 i j = -(raw29329step1 i j); unfold raw29329step2 raw29329step1; decide +kernel
      have hl : raw29329step2Labels = raw29329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical29330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29330 raw29330Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw29330 raw29330Labels = mixedMoment B raw29330step0 raw29330step0Labels := by
      have ha : raw29330step0 = (fun i j => raw29330 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29330step0 raw29330; decide +kernel
      have hl : raw29330step0Labels = raw29330Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29330 raw29330Labels permutation584 permutation2
    _ = mixedMoment B node2396 node2396Labels := by rfl

theorem canonical29331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29331 raw29331Labels = mixedMoment B node3610 node3610Labels := by
  calc
    mixedMoment B raw29331 raw29331Labels = mixedMoment B raw29331step0 raw29331step0Labels := by
      have ha : raw29331step0 = (fun i j => raw29331 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29331step0 raw29331; decide +kernel
      have hl : raw29331step0Labels = raw29331Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29331 raw29331Labels permutation168 permutation4
    mixedMoment B raw29331step0 raw29331step0Labels = mixedMoment B raw29331step1 raw29331step1Labels := by
      have ha : raw29331step1 = -raw29331step0 := by apply Matrix.ext; change ∀ i j, raw29331step1 i j = -(raw29331step0 i j); unfold raw29331step1 raw29331step0; decide +kernel
      have hl : raw29331step1Labels = raw29331step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3610 node3610Labels := by rfl

theorem canonical29336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29336 raw29336Labels = mixedMoment B node3193 node3193Labels := by
  calc
    mixedMoment B raw29336 raw29336Labels = mixedMoment B raw29336step0 raw29336step0Labels := by
      have ha : raw29336step0 = (fun i j => raw29336 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29336step0 raw29336; decide +kernel
      have hl : raw29336step0Labels = raw29336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29336 raw29336Labels permutation158 permutation2
    _ = mixedMoment B node3193 node3193Labels := by rfl

theorem canonical29337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29337 raw29337Labels = mixedMoment B node3648 node3648Labels := by
  calc
    mixedMoment B raw29337 raw29337Labels = mixedMoment B raw29337step0 raw29337step0Labels := by
      have ha : raw29337step0 = (fun i j => raw29337 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29337step0 raw29337; decide +kernel
      have hl : raw29337step0Labels = raw29337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29337 raw29337Labels permutation583 permutation2
    mixedMoment B raw29337step0 raw29337step0Labels = mixedMoment B raw29337step1 raw29337step1Labels := by
      have ha : raw29337step1 = -raw29337step0 := by apply Matrix.ext; change ∀ i j, raw29337step1 i j = -(raw29337step0 i j); unfold raw29337step1 raw29337step0; decide +kernel
      have hl : raw29337step1Labels = raw29337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3648 node3648Labels := by rfl

theorem canonical29338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29338 raw29338Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw29338 raw29338Labels = mixedMoment B raw29338step0 raw29338step0Labels := by
      have ha : raw29338step0 = (fun i j => raw29338 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29338step0 raw29338; decide +kernel
      have hl : raw29338step0Labels = raw29338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29338 raw29338Labels permutation587 permutation2
    mixedMoment B raw29338step0 raw29338step0Labels = mixedMoment B raw29338step1 raw29338step1Labels := by
      have ha : raw29338step1 = -raw29338step0 := by apply Matrix.ext; change ∀ i j, raw29338step1 i j = -(raw29338step0 i j); unfold raw29338step1 raw29338step0; decide +kernel
      have hl : raw29338step1Labels = raw29338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3659 node3659Labels := by rfl

theorem canonical29339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29339 raw29339Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw29339 raw29339Labels = mixedMoment B raw29339step0 raw29339step0Labels := by
      have ha : raw29339step0 = (fun i j => raw29339 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29339step0 raw29339; decide +kernel
      have hl : raw29339step0Labels = raw29339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29339 raw29339Labels permutation582 permutation2
    mixedMoment B raw29339step0 raw29339step0Labels = mixedMoment B raw29339step1 raw29339step1Labels := by
      have ha : raw29339step1 = -raw29339step0 := by apply Matrix.ext; change ∀ i j, raw29339step1 i j = -(raw29339step0 i j); unfold raw29339step1 raw29339step0; decide +kernel
      have hl : raw29339step1Labels = raw29339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

theorem canonical29340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29340 raw29340Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw29340 raw29340Labels = mixedMoment B raw29340step0 raw29340step0Labels := by
      have ha : raw29340step0 = (fun i j => raw29340 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29340step0 raw29340; decide +kernel
      have hl : raw29340step0Labels = raw29340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29340 raw29340Labels permutation682 permutation2
    mixedMoment B raw29340step0 raw29340step0Labels = mixedMoment B raw29340step1 raw29340step1Labels := by
      have ha : raw29340step1 = -raw29340step0 := by apply Matrix.ext; change ∀ i j, raw29340step1 i j = -(raw29340step0 i j); unfold raw29340step1 raw29340step0; decide +kernel
      have hl : raw29340step1Labels = raw29340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical29341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29341 raw29341Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw29341 raw29341Labels = mixedMoment B raw29341step0 raw29341step0Labels := by
      have ha : raw29341step0 = (fun i j => raw29341 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29341step0 raw29341; decide +kernel
      have hl : raw29341step0Labels = raw29341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29341 raw29341Labels permutation584 permutation2
    mixedMoment B raw29341step0 raw29341step0Labels = mixedMoment B raw29341step1 raw29341step1Labels := by
      have ha : raw29341step1 = -raw29341step0 := by apply Matrix.ext; change ∀ i j, raw29341step1 i j = -(raw29341step0 i j); unfold raw29341step1 raw29341step0; decide +kernel
      have hl : raw29341step1Labels = raw29341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical29342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29342 raw29342Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw29342 raw29342Labels = mixedMoment B raw29342step0 raw29342step0Labels := by
      have hz : ∀ j, raw29342 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw29342step0 = (fun i j => raw29342 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw29342step0 raw29342; decide +kernel
      have hl : raw29342step0Labels = raw29342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29342 raw29342Labels permutation152 hz
    mixedMoment B raw29342step0 raw29342step0Labels = mixedMoment B raw29342step1 raw29342step1Labels := by
      have ha : raw29342step1 = (fun i j => raw29342step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29342step1 raw29342step0; decide +kernel
      have hl : raw29342step1Labels = raw29342step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29342step0 raw29342step0Labels permutation122 permutation0
    mixedMoment B raw29342step1 raw29342step1Labels = mixedMoment B raw29342step2 raw29342step2Labels := by
      have ha : raw29342step2 = -raw29342step1 := by apply Matrix.ext; change ∀ i j, raw29342step2 i j = -(raw29342step1 i j); unfold raw29342step2 raw29342step1; decide +kernel
      have hl : raw29342step2Labels = raw29342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

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

theorem canonical29344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29344 raw29344Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw29344 raw29344Labels = mixedMoment B raw29344step0 raw29344step0Labels := by
      have ha : raw29344step0 = (fun i j => raw29344 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29344step0 raw29344; decide +kernel
      have hl : raw29344step0Labels = raw29344Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29344 raw29344Labels permutation176 permutation2
    _ = mixedMoment B node1977 node1977Labels := by rfl

theorem canonical29345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29345 raw29345Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw29345 raw29345Labels = mixedMoment B raw29345step0 raw29345step0Labels := by
      have hz : ∀ j, raw29345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29345step0 = (fun i j => raw29345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29345step0 raw29345; decide +kernel
      have hl : raw29345step0Labels = raw29345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29345 raw29345Labels permutation346 hz
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical29346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29346 raw29346Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw29346 raw29346Labels = mixedMoment B raw29346step0 raw29346step0Labels := by
      have hz : ∀ j, raw29346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29346step0 = (fun i j => raw29346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29346step0 raw29346; decide +kernel
      have hl : raw29346step0Labels = raw29346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29346 raw29346Labels permutation346 hz
    mixedMoment B raw29346step0 raw29346step0Labels = mixedMoment B raw29346step1 raw29346step1Labels := by
      have ha : raw29346step1 = (fun i j => raw29346step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29346step1 raw29346step0; decide +kernel
      have hl : raw29346step1Labels = raw29346step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29346step0 raw29346step0Labels permutation33 permutation2
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical29347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29347 raw29347Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw29347 raw29347Labels = mixedMoment B raw29347step0 raw29347step0Labels := by
      have ha : raw29347step0 = (fun i j => raw29347 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29347step0 raw29347; decide +kernel
      have hl : raw29347step0Labels = raw29347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29347 raw29347Labels permutation159 permutation2
    _ = mixedMoment B node3133 node3133Labels := by rfl

theorem canonical29348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29348 raw29348Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw29348 raw29348Labels = mixedMoment B raw29348step0 raw29348step0Labels := by
      have hz : ∀ j, raw29348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29348step0 = (fun i j => raw29348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29348step0 raw29348; decide +kernel
      have hl : raw29348step0Labels = raw29348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29348 raw29348Labels permutation346 hz
    mixedMoment B raw29348step0 raw29348step0Labels = mixedMoment B raw29348step1 raw29348step1Labels := by
      have ha : raw29348step1 = (fun i j => raw29348step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29348step1 raw29348step0; decide +kernel
      have hl : raw29348step1Labels = raw29348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29348step0 raw29348step0Labels permutation33 permutation2
    _ = mixedMoment B node3138 node3138Labels := by rfl

theorem canonical29349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29349 raw29349Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw29349 raw29349Labels = mixedMoment B raw29349step0 raw29349step0Labels := by
      have hz : ∀ j, raw29349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29349step0 = (fun i j => raw29349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29349step0 raw29349; decide +kernel
      have hl : raw29349step0Labels = raw29349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29349 raw29349Labels permutation346 hz
    mixedMoment B raw29349step0 raw29349step0Labels = mixedMoment B raw29349step1 raw29349step1Labels := by
      have ha : raw29349step1 = (fun i j => raw29349step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29349step1 raw29349step0; decide +kernel
      have hl : raw29349step1Labels = raw29349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29349step0 raw29349step0Labels permutation127 permutation2
    mixedMoment B raw29349step1 raw29349step1Labels = mixedMoment B raw29349step2 raw29349step2Labels := by
      have ha : raw29349step2 = -raw29349step1 := by apply Matrix.ext; change ∀ i j, raw29349step2 i j = -(raw29349step1 i j); unfold raw29349step2 raw29349step1; decide +kernel
      have hl : raw29349step2Labels = raw29349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

theorem canonical29350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29350 raw29350Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw29350 raw29350Labels = mixedMoment B raw29350step0 raw29350step0Labels := by
      have hz : ∀ j, raw29350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29350step0 = (fun i j => raw29350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29350step0 raw29350; decide +kernel
      have hl : raw29350step0Labels = raw29350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29350 raw29350Labels permutation346 hz
    mixedMoment B raw29350step0 raw29350step0Labels = mixedMoment B raw29350step1 raw29350step1Labels := by
      have ha : raw29350step1 = (fun i j => raw29350step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29350step1 raw29350step0; decide +kernel
      have hl : raw29350step1Labels = raw29350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29350step0 raw29350step0Labels permutation151 permutation2
    mixedMoment B raw29350step1 raw29350step1Labels = mixedMoment B raw29350step2 raw29350step2Labels := by
      have ha : raw29350step2 = -raw29350step1 := by apply Matrix.ext; change ∀ i j, raw29350step2 i j = -(raw29350step1 i j); unfold raw29350step2 raw29350step1; decide +kernel
      have hl : raw29350step2Labels = raw29350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2803 node2803Labels := by rfl

theorem canonical29351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29351 raw29351Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw29351 raw29351Labels = mixedMoment B raw29351step0 raw29351step0Labels := by
      have ha : raw29351step0 = (fun i j => raw29351 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29351step0 raw29351; decide +kernel
      have hl : raw29351step0Labels = raw29351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29351 raw29351Labels permutation188 permutation4
    mixedMoment B raw29351step0 raw29351step0Labels = mixedMoment B raw29351step1 raw29351step1Labels := by
      have ha : raw29351step1 = -raw29351step0 := by apply Matrix.ext; change ∀ i j, raw29351step1 i j = -(raw29351step0 i j); unfold raw29351step1 raw29351step0; decide +kernel
      have hl : raw29351step1Labels = raw29351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3536 node3536Labels := by rfl

theorem canonical29352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29352 raw29352Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw29352 raw29352Labels = mixedMoment B raw29352step0 raw29352step0Labels := by
      have hz : ∀ j, raw29352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29352step0 = (fun i j => raw29352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29352step0 raw29352; decide +kernel
      have hl : raw29352step0Labels = raw29352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29352 raw29352Labels permutation434 hz
    mixedMoment B raw29352step0 raw29352step0Labels = mixedMoment B raw29352step1 raw29352step1Labels := by
      have hz : ∀ j, raw29352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29352step1 = (fun i j => raw29352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29352step1 raw29352step0; decide +kernel
      have hl : raw29352step1Labels = raw29352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29352step0 raw29352step0Labels permutation80 hz
    mixedMoment B raw29352step1 raw29352step1Labels = mixedMoment B raw29352step2 raw29352step2Labels := by
      have ha : raw29352step2 = (fun i j => raw29352step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29352step2 raw29352step1; decide +kernel
      have hl : raw29352step2Labels = raw29352step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29352step1 raw29352step1Labels permutation10 permutation4
    mixedMoment B raw29352step2 raw29352step2Labels = mixedMoment B raw29352step3 raw29352step3Labels := by
      have ha : raw29352step3 = -raw29352step2 := by apply Matrix.ext; change ∀ i j, raw29352step3 i j = -(raw29352step2 i j); unfold raw29352step3 raw29352step2; decide +kernel
      have hl : raw29352step3Labels = raw29352step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3631 node3631Labels := by rfl

theorem canonical29353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29353 raw29353Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw29353 raw29353Labels = mixedMoment B raw29353step0 raw29353step0Labels := by
      have hz : ∀ j, raw29353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29353step0 = (fun i j => raw29353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29353step0 raw29353; decide +kernel
      have hl : raw29353step0Labels = raw29353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29353 raw29353Labels permutation346 hz
    mixedMoment B raw29353step0 raw29353step0Labels = mixedMoment B raw29353step1 raw29353step1Labels := by
      have ha : raw29353step1 = (fun i j => raw29353step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29353step1 raw29353step0; decide +kernel
      have hl : raw29353step1Labels = raw29353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29353step0 raw29353step0Labels permutation126 permutation2
    _ = mixedMoment B node2401 node2401Labels := by rfl

theorem canonical29354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29354 raw29354Labels = mixedMoment B node3630 node3630Labels := by
  calc
    mixedMoment B raw29354 raw29354Labels = mixedMoment B raw29354step0 raw29354step0Labels := by
      have hz : ∀ j, raw29354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29354step0 = (fun i j => raw29354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29354step0 raw29354; decide +kernel
      have hl : raw29354step0Labels = raw29354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29354 raw29354Labels permutation346 hz
    mixedMoment B raw29354step0 raw29354step0Labels = mixedMoment B raw29354step1 raw29354step1Labels := by
      have ha : raw29354step1 = (fun i j => raw29354step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29354step1 raw29354step0; decide +kernel
      have hl : raw29354step1Labels = raw29354step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29354step0 raw29354step0Labels permutation48 permutation4
    mixedMoment B raw29354step1 raw29354step1Labels = mixedMoment B raw29354step2 raw29354step2Labels := by
      have ha : raw29354step2 = -raw29354step1 := by apply Matrix.ext; change ∀ i j, raw29354step2 i j = -(raw29354step1 i j); unfold raw29354step2 raw29354step1; decide +kernel
      have hl : raw29354step2Labels = raw29354step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3630 node3630Labels := by rfl

theorem canonical29355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29355 raw29355Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw29355 raw29355Labels = mixedMoment B raw29355step0 raw29355step0Labels := by
      have hz : ∀ j, raw29355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29355step0 = (fun i j => raw29355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29355step0 raw29355; decide +kernel
      have hl : raw29355step0Labels = raw29355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29355 raw29355Labels permutation434 hz
    mixedMoment B raw29355step0 raw29355step0Labels = mixedMoment B raw29355step1 raw29355step1Labels := by
      have hz : ∀ j, raw29355step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29355step1 = (fun i j => raw29355step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29355step1 raw29355step0; decide +kernel
      have hl : raw29355step1Labels = raw29355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29355step0 raw29355step0Labels permutation80 hz
    mixedMoment B raw29355step1 raw29355step1Labels = mixedMoment B raw29355step2 raw29355step2Labels := by
      have ha : raw29355step2 = (fun i j => raw29355step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29355step2 raw29355step1; decide +kernel
      have hl : raw29355step2Labels = raw29355step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29355step1 raw29355step1Labels permutation11 permutation4
    mixedMoment B raw29355step2 raw29355step2Labels = mixedMoment B raw29355step3 raw29355step3Labels := by
      have ha : raw29355step3 = -raw29355step2 := by apply Matrix.ext; change ∀ i j, raw29355step3 i j = -(raw29355step2 i j); unfold raw29355step3 raw29355step2; decide +kernel
      have hl : raw29355step3Labels = raw29355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2280 node2280Labels := by rfl

theorem canonical29356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29356 raw29356Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw29356 raw29356Labels = mixedMoment B raw29356step0 raw29356step0Labels := by
      have hz : ∀ j, raw29356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29356step0 = (fun i j => raw29356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29356step0 raw29356; decide +kernel
      have hl : raw29356step0Labels = raw29356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29356 raw29356Labels permutation434 hz
    mixedMoment B raw29356step0 raw29356step0Labels = mixedMoment B raw29356step1 raw29356step1Labels := by
      have ha : raw29356step1 = (fun i j => raw29356step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29356step1 raw29356step0; decide +kernel
      have hl : raw29356step1Labels = raw29356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29356step0 raw29356step0Labels permutation44 permutation4
    mixedMoment B raw29356step1 raw29356step1Labels = mixedMoment B raw29356step2 raw29356step2Labels := by
      have ha : raw29356step2 = -raw29356step1 := by apply Matrix.ext; change ∀ i j, raw29356step2 i j = -(raw29356step1 i j); unfold raw29356step2 raw29356step1; decide +kernel
      have hl : raw29356step2Labels = raw29356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical29357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29357 raw29357Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw29357 raw29357Labels = mixedMoment B raw29357step0 raw29357step0Labels := by
      have hz : ∀ j, raw29357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29357step0 = (fun i j => raw29357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29357step0 raw29357; decide +kernel
      have hl : raw29357step0Labels = raw29357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29357 raw29357Labels permutation434 hz
    mixedMoment B raw29357step0 raw29357step0Labels = mixedMoment B raw29357step1 raw29357step1Labels := by
      have hz : ∀ j, raw29357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29357step1 = (fun i j => raw29357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29357step1 raw29357step0; decide +kernel
      have hl : raw29357step1Labels = raw29357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29357step0 raw29357step0Labels permutation80 hz
    mixedMoment B raw29357step1 raw29357step1Labels = mixedMoment B raw29357step2 raw29357step2Labels := by
      have ha : raw29357step2 = (fun i j => raw29357step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29357step2 raw29357step1; decide +kernel
      have hl : raw29357step2Labels = raw29357step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29357step1 raw29357step1Labels permutation8 permutation4
    mixedMoment B raw29357step2 raw29357step2Labels = mixedMoment B raw29357step3 raw29357step3Labels := by
      have ha : raw29357step3 = -raw29357step2 := by apply Matrix.ext; change ∀ i j, raw29357step3 i j = -(raw29357step2 i j); unfold raw29357step3 raw29357step2; decide +kernel
      have hl : raw29357step3Labels = raw29357step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical29358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29358 raw29358Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw29358 raw29358Labels = mixedMoment B raw29358step0 raw29358step0Labels := by
      have hz : ∀ j, raw29358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29358step0 = (fun i j => raw29358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29358step0 raw29358; decide +kernel
      have hl : raw29358step0Labels = raw29358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29358 raw29358Labels permutation434 hz
    mixedMoment B raw29358step0 raw29358step0Labels = mixedMoment B raw29358step1 raw29358step1Labels := by
      have hz : ∀ j, raw29358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29358step1 = (fun i j => raw29358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29358step1 raw29358step0; decide +kernel
      have hl : raw29358step1Labels = raw29358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29358step0 raw29358step0Labels permutation80 hz
    mixedMoment B raw29358step1 raw29358step1Labels = mixedMoment B raw29358step2 raw29358step2Labels := by
      have ha : raw29358step2 = (fun i j => raw29358step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29358step2 raw29358step1; decide +kernel
      have hl : raw29358step2Labels = raw29358step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29358step1 raw29358step1Labels permutation10 permutation4
    mixedMoment B raw29358step2 raw29358step2Labels = mixedMoment B raw29358step3 raw29358step3Labels := by
      have ha : raw29358step3 = -raw29358step2 := by apply Matrix.ext; change ∀ i j, raw29358step3 i j = -(raw29358step2 i j); unfold raw29358step3 raw29358step2; decide +kernel
      have hl : raw29358step3Labels = raw29358step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical29359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29359 raw29359Labels = mixedMoment B node3166 node3166Labels := by
  calc
    mixedMoment B raw29359 raw29359Labels = mixedMoment B raw29359step0 raw29359step0Labels := by
      have hz : ∀ j, raw29359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29359step0 = (fun i j => raw29359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29359step0 raw29359; decide +kernel
      have hl : raw29359step0Labels = raw29359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29359 raw29359Labels permutation346 hz
    _ = mixedMoment B node3166 node3166Labels := by rfl

theorem canonical29360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29360 raw29360Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw29360 raw29360Labels = mixedMoment B raw29360step0 raw29360step0Labels := by
      have hz : ∀ j, raw29360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29360step0 = (fun i j => raw29360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29360step0 raw29360; decide +kernel
      have hl : raw29360step0Labels = raw29360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29360 raw29360Labels permutation346 hz
    mixedMoment B raw29360step0 raw29360step0Labels = mixedMoment B raw29360step1 raw29360step1Labels := by
      have ha : raw29360step1 = (fun i j => raw29360step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29360step1 raw29360step0; decide +kernel
      have hl : raw29360step1Labels = raw29360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29360step0 raw29360step0Labels permutation126 permutation2
    mixedMoment B raw29360step1 raw29360step1Labels = mixedMoment B raw29360step2 raw29360step2Labels := by
      have ha : raw29360step2 = -raw29360step1 := by apply Matrix.ext; change ∀ i j, raw29360step2 i j = -(raw29360step1 i j); unfold raw29360step2 raw29360step1; decide +kernel
      have hl : raw29360step2Labels = raw29360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3660 node3660Labels := by rfl

theorem canonical29361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29361 raw29361Labels = mixedMoment B node3658 node3658Labels := by
  calc
    mixedMoment B raw29361 raw29361Labels = mixedMoment B raw29361step0 raw29361step0Labels := by
      have ha : raw29361step0 = (fun i j => raw29361 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29361step0 raw29361; decide +kernel
      have hl : raw29361step0Labels = raw29361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29361 raw29361Labels permutation589 permutation2
    mixedMoment B raw29361step0 raw29361step0Labels = mixedMoment B raw29361step1 raw29361step1Labels := by
      have ha : raw29361step1 = -raw29361step0 := by apply Matrix.ext; change ∀ i j, raw29361step1 i j = -(raw29361step0 i j); unfold raw29361step1 raw29361step0; decide +kernel
      have hl : raw29361step1Labels = raw29361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3658 node3658Labels := by rfl

theorem canonical29362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29362 raw29362Labels = mixedMoment B node3666 node3666Labels := by
  calc
    mixedMoment B raw29362 raw29362Labels = mixedMoment B raw29362step0 raw29362step0Labels := by
      have hz : ∀ j, raw29362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29362step0 = (fun i j => raw29362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29362step0 raw29362; decide +kernel
      have hl : raw29362step0Labels = raw29362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29362 raw29362Labels permutation346 hz
    mixedMoment B raw29362step0 raw29362step0Labels = mixedMoment B raw29362step1 raw29362step1Labels := by
      have ha : raw29362step1 = (fun i j => raw29362step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29362step1 raw29362step0; decide +kernel
      have hl : raw29362step1Labels = raw29362step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29362step0 raw29362step0Labels permutation125 permutation2
    mixedMoment B raw29362step1 raw29362step1Labels = mixedMoment B raw29362step2 raw29362step2Labels := by
      have ha : raw29362step2 = -raw29362step1 := by apply Matrix.ext; change ∀ i j, raw29362step2 i j = -(raw29362step1 i j); unfold raw29362step2 raw29362step1; decide +kernel
      have hl : raw29362step2Labels = raw29362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3666 node3666Labels := by rfl

theorem canonical29363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29363 raw29363Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw29363 raw29363Labels = mixedMoment B raw29363step0 raw29363step0Labels := by
      have hz : ∀ j, raw29363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29363step0 = (fun i j => raw29363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29363step0 raw29363; decide +kernel
      have hl : raw29363step0Labels = raw29363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29363 raw29363Labels permutation346 hz
    mixedMoment B raw29363step0 raw29363step0Labels = mixedMoment B raw29363step1 raw29363step1Labels := by
      have ha : raw29363step1 = (fun i j => raw29363step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29363step1 raw29363step0; decide +kernel
      have hl : raw29363step1Labels = raw29363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29363step0 raw29363step0Labels permutation151 permutation2
    mixedMoment B raw29363step1 raw29363step1Labels = mixedMoment B raw29363step2 raw29363step2Labels := by
      have ha : raw29363step2 = -raw29363step1 := by apply Matrix.ext; change ∀ i j, raw29363step2 i j = -(raw29363step1 i j); unfold raw29363step2 raw29363step1; decide +kernel
      have hl : raw29363step2Labels = raw29363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3772 node3772Labels := by rfl

theorem canonical29364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29364 raw29364Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw29364 raw29364Labels = mixedMoment B raw29364step0 raw29364step0Labels := by
      have hz : ∀ j, raw29364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29364step0 = (fun i j => raw29364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29364step0 raw29364; decide +kernel
      have hl : raw29364step0Labels = raw29364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29364 raw29364Labels permutation346 hz
    mixedMoment B raw29364step0 raw29364step0Labels = mixedMoment B raw29364step1 raw29364step1Labels := by
      have ha : raw29364step1 = (fun i j => raw29364step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29364step1 raw29364step0; decide +kernel
      have hl : raw29364step1Labels = raw29364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29364step0 raw29364step0Labels permutation127 permutation2
    mixedMoment B raw29364step1 raw29364step1Labels = mixedMoment B raw29364step2 raw29364step2Labels := by
      have ha : raw29364step2 = -raw29364step1 := by apply Matrix.ext; change ∀ i j, raw29364step2 i j = -(raw29364step1 i j); unfold raw29364step2 raw29364step1; decide +kernel
      have hl : raw29364step2Labels = raw29364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3772 node3772Labels := by rfl

theorem canonical29365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29365 raw29365Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw29365 raw29365Labels = mixedMoment B raw29365step0 raw29365step0Labels := by
      have hz : ∀ j, raw29365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29365step0 = (fun i j => raw29365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29365step0 raw29365; decide +kernel
      have hl : raw29365step0Labels = raw29365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29365 raw29365Labels permutation346 hz
    mixedMoment B raw29365step0 raw29365step0Labels = mixedMoment B raw29365step1 raw29365step1Labels := by
      have hz : ∀ j, raw29365step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw29365step1 = (fun i j => raw29365step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw29365step1 raw29365step0; decide +kernel
      have hl : raw29365step1Labels = raw29365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29365step0 raw29365step0Labels permutation32 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical29366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29366 raw29366Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw29366 raw29366Labels = mixedMoment B raw29366step0 raw29366step0Labels := by
      have hz : ∀ j, raw29366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29366step0 = (fun i j => raw29366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29366step0 raw29366; decide +kernel
      have hl : raw29366step0Labels = raw29366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29366 raw29366Labels permutation434 hz
    mixedMoment B raw29366step0 raw29366step0Labels = mixedMoment B raw29366step1 raw29366step1Labels := by
      have hz : ∀ j, raw29366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29366step1 = (fun i j => raw29366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29366step1 raw29366step0; decide +kernel
      have hl : raw29366step1Labels = raw29366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29366step0 raw29366step0Labels permutation80 hz
    mixedMoment B raw29366step1 raw29366step1Labels = mixedMoment B raw29366step2 raw29366step2Labels := by
      have ha : raw29366step2 = (fun i j => raw29366step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29366step2 raw29366step1; decide +kernel
      have hl : raw29366step2Labels = raw29366step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29366step1 raw29366step1Labels permutation15 permutation2
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical29367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29367 raw29367Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw29367 raw29367Labels = mixedMoment B raw29367step0 raw29367step0Labels := by
      have hz : ∀ j, raw29367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29367step0 = (fun i j => raw29367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29367step0 raw29367; decide +kernel
      have hl : raw29367step0Labels = raw29367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29367 raw29367Labels permutation434 hz
    mixedMoment B raw29367step0 raw29367step0Labels = mixedMoment B raw29367step1 raw29367step1Labels := by
      have hz : ∀ j, raw29367step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29367step1 = (fun i j => raw29367step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29367step1 raw29367step0; decide +kernel
      have hl : raw29367step1Labels = raw29367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29367step0 raw29367step0Labels permutation80 hz
    mixedMoment B raw29367step1 raw29367step1Labels = mixedMoment B raw29367step2 raw29367step2Labels := by
      have ha : raw29367step2 = (fun i j => raw29367step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29367step2 raw29367step1; decide +kernel
      have hl : raw29367step2Labels = raw29367step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29367step1 raw29367step1Labels permutation9 permutation2
    _ = mixedMoment B node3161 node3161Labels := by rfl

theorem canonical29368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29368 raw29368Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw29368 raw29368Labels = mixedMoment B raw29368step0 raw29368step0Labels := by
      have hz : ∀ j, raw29368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29368step0 = (fun i j => raw29368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29368step0 raw29368; decide +kernel
      have hl : raw29368step0Labels = raw29368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29368 raw29368Labels permutation434 hz
    mixedMoment B raw29368step0 raw29368step0Labels = mixedMoment B raw29368step1 raw29368step1Labels := by
      have ha : raw29368step1 = (fun i j => raw29368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29368step1 raw29368step0; decide +kernel
      have hl : raw29368step1Labels = raw29368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29368step0 raw29368step0Labels permutation33 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

theorem canonical29369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29369 raw29369Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw29369 raw29369Labels = mixedMoment B raw29369step0 raw29369step0Labels := by
      have hz : ∀ j, raw29369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29369step0 = (fun i j => raw29369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29369step0 raw29369; decide +kernel
      have hl : raw29369step0Labels = raw29369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29369 raw29369Labels permutation346 hz
    mixedMoment B raw29369step0 raw29369step0Labels = mixedMoment B raw29369step1 raw29369step1Labels := by
      have ha : raw29369step1 = (fun i j => raw29369step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29369step1 raw29369step0; decide +kernel
      have hl : raw29369step1Labels = raw29369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29369step0 raw29369step0Labels permutation33 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

theorem canonical29370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29370 raw29370Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw29370 raw29370Labels = mixedMoment B raw29370step0 raw29370step0Labels := by
      have hz : ∀ j, raw29370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29370step0 = (fun i j => raw29370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29370step0 raw29370; decide +kernel
      have hl : raw29370step0Labels = raw29370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29370 raw29370Labels permutation434 hz
    mixedMoment B raw29370step0 raw29370step0Labels = mixedMoment B raw29370step1 raw29370step1Labels := by
      have hz : ∀ j, raw29370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29370step1 = (fun i j => raw29370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29370step1 raw29370step0; decide +kernel
      have hl : raw29370step1Labels = raw29370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29370step0 raw29370step0Labels permutation80 hz
    mixedMoment B raw29370step1 raw29370step1Labels = mixedMoment B raw29370step2 raw29370step2Labels := by
      have ha : raw29370step2 = (fun i j => raw29370step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29370step2 raw29370step1; decide +kernel
      have hl : raw29370step2Labels = raw29370step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29370step1 raw29370step1Labels permutation25 permutation2
    mixedMoment B raw29370step2 raw29370step2Labels = mixedMoment B raw29370step3 raw29370step3Labels := by
      have ha : raw29370step3 = -raw29370step2 := by apply Matrix.ext; change ∀ i j, raw29370step3 i j = -(raw29370step2 i j); unfold raw29370step3 raw29370step2; decide +kernel
      have hl : raw29370step3Labels = raw29370step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

theorem canonical29371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29371 raw29371Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw29371 raw29371Labels = mixedMoment B raw29371step0 raw29371step0Labels := by
      have hz : ∀ j, raw29371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29371step0 = (fun i j => raw29371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29371step0 raw29371; decide +kernel
      have hl : raw29371step0Labels = raw29371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29371 raw29371Labels permutation434 hz
    mixedMoment B raw29371step0 raw29371step0Labels = mixedMoment B raw29371step1 raw29371step1Labels := by
      have hz : ∀ j, raw29371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29371step1 = (fun i j => raw29371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29371step1 raw29371step0; decide +kernel
      have hl : raw29371step1Labels = raw29371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29371step0 raw29371step0Labels permutation80 hz
    mixedMoment B raw29371step1 raw29371step1Labels = mixedMoment B raw29371step2 raw29371step2Labels := by
      have ha : raw29371step2 = (fun i j => raw29371step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29371step2 raw29371step1; decide +kernel
      have hl : raw29371step2Labels = raw29371step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29371step1 raw29371step1Labels permutation31 permutation2
    mixedMoment B raw29371step2 raw29371step2Labels = mixedMoment B raw29371step3 raw29371step3Labels := by
      have ha : raw29371step3 = -raw29371step2 := by apply Matrix.ext; change ∀ i j, raw29371step3 i j = -(raw29371step2 i j); unfold raw29371step3 raw29371step2; decide +kernel
      have hl : raw29371step3Labels = raw29371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2821 node2821Labels := by rfl

theorem canonical29372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29372 raw29372Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29372 raw29372Labels = mixedMoment B raw29372step0 raw29372step0Labels := by
      have hz : ∀ j, raw29372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29372step0 = (fun i j => raw29372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29372step0 raw29372; decide +kernel
      have hl : raw29372step0Labels = raw29372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372 raw29372Labels permutation434 hz
    mixedMoment B raw29372step0 raw29372step0Labels = mixedMoment B raw29372step1 raw29372step1Labels := by
      have hz : ∀ j, raw29372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29372step1 = (fun i j => raw29372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29372step1 raw29372step0; decide +kernel
      have hl : raw29372step1Labels = raw29372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372step0 raw29372step0Labels permutation80 hz
    mixedMoment B raw29372step1 raw29372step1Labels = mixedMoment B raw29372step2 raw29372step2Labels := by
      have hz : ∀ j, raw29372step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw29372step2 = (fun i j => raw29372step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw29372step2 raw29372step1; decide +kernel
      have hl : raw29372step2Labels = raw29372step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372step1 raw29372step1Labels permutation8 hz
    mixedMoment B raw29372step2 raw29372step2Labels = mixedMoment B raw29372step3 raw29372step3Labels := by
      have ha : raw29372step3 = (fun i j => raw29372step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29372step3 raw29372step2; decide +kernel
      have hl : raw29372step3Labels = raw29372step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29372step2 raw29372step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical29373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29373 raw29373Labels = mixedMoment B node3147 node3147Labels := by
  calc
    mixedMoment B raw29373 raw29373Labels = mixedMoment B raw29373step0 raw29373step0Labels := by
      have hz : ∀ j, raw29373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29373step0 = (fun i j => raw29373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29373step0 raw29373; decide +kernel
      have hl : raw29373step0Labels = raw29373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29373 raw29373Labels permutation346 hz
    _ = mixedMoment B node3147 node3147Labels := by rfl

theorem canonical29374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29374 raw29374Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw29374 raw29374Labels = mixedMoment B raw29374step0 raw29374step0Labels := by
      have hz : ∀ j, raw29374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29374step0 = (fun i j => raw29374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29374step0 raw29374; decide +kernel
      have hl : raw29374step0Labels = raw29374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29374 raw29374Labels permutation346 hz
    mixedMoment B raw29374step0 raw29374step0Labels = mixedMoment B raw29374step1 raw29374step1Labels := by
      have ha : raw29374step1 = (fun i j => raw29374step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29374step1 raw29374step0; decide +kernel
      have hl : raw29374step1Labels = raw29374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29374step0 raw29374step0Labels permutation56 permutation2
    _ = mixedMoment B node3372 node3372Labels := by rfl

theorem canonical29375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29375 raw29375Labels = mixedMoment B node3473 node3473Labels := by
  calc
    mixedMoment B raw29375 raw29375Labels = mixedMoment B raw29375step0 raw29375step0Labels := by
      have ha : raw29375step0 = (fun i j => raw29375 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29375step0 raw29375; decide +kernel
      have hl : raw29375step0Labels = raw29375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29375 raw29375Labels permutation317 permutation4
    _ = mixedMoment B node3473 node3473Labels := by rfl

theorem canonical29376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29376 raw29376Labels = mixedMoment B node3611 node3611Labels := by
  calc
    mixedMoment B raw29376 raw29376Labels = mixedMoment B raw29376step0 raw29376step0Labels := by
      have hz : ∀ j, raw29376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29376step0 = (fun i j => raw29376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29376step0 raw29376; decide +kernel
      have hl : raw29376step0Labels = raw29376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29376 raw29376Labels permutation346 hz
    mixedMoment B raw29376step0 raw29376step0Labels = mixedMoment B raw29376step1 raw29376step1Labels := by
      have ha : raw29376step1 = (fun i j => raw29376step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29376step1 raw29376step0; decide +kernel
      have hl : raw29376step1Labels = raw29376step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29376step0 raw29376step0Labels permutation65 permutation4
    _ = mixedMoment B node3611 node3611Labels := by rfl

theorem canonical29377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29377 raw29377Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29377 raw29377Labels = mixedMoment B raw29377step0 raw29377step0Labels := by
      have hz : ∀ j, raw29377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29377step0 = (fun i j => raw29377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29377step0 raw29377; decide +kernel
      have hl : raw29377step0Labels = raw29377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29377 raw29377Labels permutation346 hz
    mixedMoment B raw29377step0 raw29377step0Labels = mixedMoment B raw29377step1 raw29377step1Labels := by
      have ha : raw29377step1 = (fun i j => raw29377step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29377step1 raw29377step0; decide +kernel
      have hl : raw29377step1Labels = raw29377step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29377step0 raw29377step0Labels permutation67 permutation4
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical29378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29378 raw29378Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29378 raw29378Labels = mixedMoment B raw29378step0 raw29378step0Labels := by
      have hz : ∀ j, raw29378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29378step0 = (fun i j => raw29378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29378step0 raw29378; decide +kernel
      have hl : raw29378step0Labels = raw29378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29378 raw29378Labels permutation346 hz
    mixedMoment B raw29378step0 raw29378step0Labels = mixedMoment B raw29378step1 raw29378step1Labels := by
      have ha : raw29378step1 = (fun i j => raw29378step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29378step1 raw29378step0; decide +kernel
      have hl : raw29378step1Labels = raw29378step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29378step0 raw29378step0Labels permutation65 permutation4
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical29379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29379 raw29379Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29379 raw29379Labels = mixedMoment B raw29379step0 raw29379step0Labels := by
      have hz : ∀ j, raw29379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29379step0 = (fun i j => raw29379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29379step0 raw29379; decide +kernel
      have hl : raw29379step0Labels = raw29379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29379 raw29379Labels permutation346 hz
    mixedMoment B raw29379step0 raw29379step0Labels = mixedMoment B raw29379step1 raw29379step1Labels := by
      have hz : ∀ j, raw29379step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw29379step1 = (fun i j => raw29379step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw29379step1 raw29379step0; decide +kernel
      have hl : raw29379step1Labels = raw29379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29379step0 raw29379step0Labels permutation32 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical29380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29380 raw29380Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw29380 raw29380Labels = mixedMoment B raw29380step0 raw29380step0Labels := by
      have hz : ∀ j, raw29380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29380step0 = (fun i j => raw29380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29380step0 raw29380; decide +kernel
      have hl : raw29380step0Labels = raw29380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29380 raw29380Labels permutation346 hz
    _ = mixedMoment B node1141 node1141Labels := by rfl

theorem canonical29381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29381 raw29381Labels = mixedMoment B node2343 node2343Labels := by
  calc
    mixedMoment B raw29381 raw29381Labels = mixedMoment B raw29381step0 raw29381step0Labels := by
      have hz : ∀ j, raw29381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29381step0 = (fun i j => raw29381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29381step0 raw29381; decide +kernel
      have hl : raw29381step0Labels = raw29381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29381 raw29381Labels permutation346 hz
    _ = mixedMoment B node2343 node2343Labels := by rfl

theorem canonical29382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29382 raw29382Labels = mixedMoment B node2433 node2433Labels := by
  calc
    _ = mixedMoment B node2433 node2433Labels := by rfl

theorem canonical29383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29383 raw29383Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw29383 raw29383Labels = mixedMoment B raw29383step0 raw29383step0Labels := by
      have hz : ∀ j, raw29383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29383step0 = (fun i j => raw29383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29383step0 raw29383; decide +kernel
      have hl : raw29383step0Labels = raw29383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29383 raw29383Labels permutation346 hz
    mixedMoment B raw29383step0 raw29383step0Labels = mixedMoment B raw29383step1 raw29383step1Labels := by
      have ha : raw29383step1 = (fun i j => raw29383step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29383step1 raw29383step0; decide +kernel
      have hl : raw29383step1Labels = raw29383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29383step0 raw29383step0Labels permutation36 permutation2
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical29384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29384 raw29384Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw29384 raw29384Labels = mixedMoment B raw29384step0 raw29384step0Labels := by
      have hz : ∀ j, raw29384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29384step0 = (fun i j => raw29384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29384step0 raw29384; decide +kernel
      have hl : raw29384step0Labels = raw29384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29384 raw29384Labels permutation346 hz
    mixedMoment B raw29384step0 raw29384step0Labels = mixedMoment B raw29384step1 raw29384step1Labels := by
      have ha : raw29384step1 = (fun i j => raw29384step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29384step1 raw29384step0; decide +kernel
      have hl : raw29384step1Labels = raw29384step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29384step0 raw29384step0Labels permutation125 permutation2
    mixedMoment B raw29384step1 raw29384step1Labels = mixedMoment B raw29384step2 raw29384step2Labels := by
      have ha : raw29384step2 = -raw29384step1 := by apply Matrix.ext; change ∀ i j, raw29384step2 i j = -(raw29384step1 i j); unfold raw29384step2 raw29384step1; decide +kernel
      have hl : raw29384step2Labels = raw29384step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical29385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29385 raw29385Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw29385 raw29385Labels = mixedMoment B raw29385step0 raw29385step0Labels := by
      have ha : raw29385step0 = (fun i j => raw29385 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29385step0 raw29385; decide +kernel
      have hl : raw29385step0Labels = raw29385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29385 raw29385Labels permutation201 permutation2
    _ = mixedMoment B node2846 node2846Labels := by rfl

theorem canonical29386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29386 raw29386Labels = mixedMoment B node2335 node2335Labels := by
  calc
    mixedMoment B raw29386 raw29386Labels = mixedMoment B raw29386step0 raw29386step0Labels := by
      have hz : ∀ j, raw29386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29386step0 = (fun i j => raw29386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29386step0 raw29386; decide +kernel
      have hl : raw29386step0Labels = raw29386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29386 raw29386Labels permutation346 hz
    mixedMoment B raw29386step0 raw29386step0Labels = mixedMoment B raw29386step1 raw29386step1Labels := by
      have ha : raw29386step1 = (fun i j => raw29386step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29386step1 raw29386step0; decide +kernel
      have hl : raw29386step1Labels = raw29386step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29386step0 raw29386step0Labels permutation125 permutation2
    mixedMoment B raw29386step1 raw29386step1Labels = mixedMoment B raw29386step2 raw29386step2Labels := by
      have ha : raw29386step2 = -raw29386step1 := by apply Matrix.ext; change ∀ i j, raw29386step2 i j = -(raw29386step1 i j); unfold raw29386step2 raw29386step1; decide +kernel
      have hl : raw29386step2Labels = raw29386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2335 node2335Labels := by rfl

theorem canonical29387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29387 raw29387Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw29387 raw29387Labels = mixedMoment B raw29387step0 raw29387step0Labels := by
      have hz : ∀ j, raw29387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29387step0 = (fun i j => raw29387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29387step0 raw29387; decide +kernel
      have hl : raw29387step0Labels = raw29387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29387 raw29387Labels permutation346 hz
    mixedMoment B raw29387step0 raw29387step0Labels = mixedMoment B raw29387step1 raw29387step1Labels := by
      have ha : raw29387step1 = (fun i j => raw29387step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29387step1 raw29387step0; decide +kernel
      have hl : raw29387step1Labels = raw29387step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29387step0 raw29387step0Labels permutation149 permutation2
    mixedMoment B raw29387step1 raw29387step1Labels = mixedMoment B raw29387step2 raw29387step2Labels := by
      have ha : raw29387step2 = -raw29387step1 := by apply Matrix.ext; change ∀ i j, raw29387step2 i j = -(raw29387step1 i j); unfold raw29387step2 raw29387step1; decide +kernel
      have hl : raw29387step2Labels = raw29387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2811 node2811Labels := by rfl

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

theorem canonical5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5202 raw5202Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5202 raw5202Labels = mixedMoment B raw5202step0 raw5202step0Labels := by
      have hz : ∀ j, raw5202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5202step0 = (fun i j => raw5202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5202step0 raw5202; decide +kernel
      have hl : raw5202step0Labels = raw5202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202 raw5202Labels permutation520 hz
    mixedMoment B raw5202step0 raw5202step0Labels = mixedMoment B raw5202step1 raw5202step1Labels := by
      have hz : ∀ j, raw5202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5202step1 = (fun i j => raw5202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5202step1 raw5202step0; decide +kernel
      have hl : raw5202step1Labels = raw5202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202step0 raw5202step0Labels permutation104 hz
    mixedMoment B raw5202step1 raw5202step1Labels = mixedMoment B raw5202step2 raw5202step2Labels := by
      have hz : ∀ i, raw5202step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5202step2 = (fun i j => raw5202step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5202step2 raw5202step1; decide +kernel
      have hl : raw5202step2Labels = (fun j => raw5202step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5202step1 raw5202step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5206 raw5206Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5206 raw5206Labels = mixedMoment B raw5206step0 raw5206step0Labels := by
      have hz : ∀ j, raw5206 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5206step0 = (fun i j => raw5206 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5206step0 raw5206; decide +kernel
      have hl : raw5206step0Labels = raw5206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206 raw5206Labels permutation520 hz
    mixedMoment B raw5206step0 raw5206step0Labels = mixedMoment B raw5206step1 raw5206step1Labels := by
      have hz : ∀ j, raw5206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5206step1 = (fun i j => raw5206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5206step1 raw5206step0; decide +kernel
      have hl : raw5206step1Labels = raw5206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206step0 raw5206step0Labels permutation80 hz
    mixedMoment B raw5206step1 raw5206step1Labels = mixedMoment B raw5206step2 raw5206step2Labels := by
      have hz : ∀ i, raw5206step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5206step2 = (fun i j => raw5206step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5206step2 raw5206step1; decide +kernel
      have hl : raw5206step2Labels = (fun j => raw5206step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5206step1 raw5206step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical5211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5211 raw5211Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5211 raw5211Labels = mixedMoment B raw5211step0 raw5211step0Labels := by
      have hz : ∀ j, raw5211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5211step0 = (fun i j => raw5211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5211step0 raw5211; decide +kernel
      have hl : raw5211step0Labels = raw5211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211 raw5211Labels permutation434 hz
    mixedMoment B raw5211step0 raw5211step0Labels = mixedMoment B raw5211step1 raw5211step1Labels := by
      have hz : ∀ j, raw5211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5211step1 = (fun i j => raw5211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5211step1 raw5211step0; decide +kernel
      have hl : raw5211step1Labels = raw5211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211step0 raw5211step0Labels permutation56 hz
    mixedMoment B raw5211step1 raw5211step1Labels = mixedMoment B raw5211step2 raw5211step2Labels := by
      have hz : ∀ i, raw5211step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5211step2 = (fun i j => raw5211step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5211step2 raw5211step1; decide +kernel
      have hl : raw5211step2Labels = (fun j => raw5211step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5211step1 raw5211step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5212 raw5212Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5212 raw5212Labels = mixedMoment B raw5212step0 raw5212step0Labels := by
      have hz : ∀ j, raw5212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5212step0 = (fun i j => raw5212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5212step0 raw5212; decide +kernel
      have hl : raw5212step0Labels = raw5212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212 raw5212Labels permutation346 hz
    mixedMoment B raw5212step0 raw5212step0Labels = mixedMoment B raw5212step1 raw5212step1Labels := by
      have hz : ∀ j, raw5212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5212step1 = (fun i j => raw5212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5212step1 raw5212step0; decide +kernel
      have hl : raw5212step1Labels = raw5212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212step0 raw5212step0Labels permutation56 hz
    mixedMoment B raw5212step1 raw5212step1Labels = mixedMoment B raw5212step2 raw5212step2Labels := by
      have hz : ∀ i, raw5212step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5212step2 = (fun i j => raw5212step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5212step2 raw5212step1; decide +kernel
      have hl : raw5212step2Labels = (fun j => raw5212step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5212step1 raw5212step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5214 raw5214Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5214 raw5214Labels = mixedMoment B raw5214step0 raw5214step0Labels := by
      have hz : ∀ j, raw5214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5214step0 = (fun i j => raw5214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5214step0 raw5214; decide +kernel
      have hl : raw5214step0Labels = raw5214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214 raw5214Labels permutation520 hz
    mixedMoment B raw5214step0 raw5214step0Labels = mixedMoment B raw5214step1 raw5214step1Labels := by
      have hz : ∀ j, raw5214step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5214step1 = (fun i j => raw5214step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5214step1 raw5214step0; decide +kernel
      have hl : raw5214step1Labels = raw5214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step0 raw5214step0Labels permutation104 hz
    mixedMoment B raw5214step1 raw5214step1Labels = mixedMoment B raw5214step2 raw5214step2Labels := by
      have hz : ∀ j, raw5214step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5214step2 = (fun i j => raw5214step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5214step2 raw5214step1; decide +kernel
      have hl : raw5214step2Labels = raw5214step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step1 raw5214step1Labels permutation20 hz
    mixedMoment B raw5214step2 raw5214step2Labels = mixedMoment B raw5214step3 raw5214step3Labels := by
      have hz : ∀ i, raw5214step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5214step3 = (fun i j => raw5214step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5214step3 raw5214step2; decide +kernel
      have hl : raw5214step3Labels = (fun j => raw5214step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5214step2 raw5214step2Labels permutation6 hz
    mixedMoment B raw5214step3 raw5214step3Labels = mixedMoment B raw5214step4 raw5214step4Labels := by
      have ha : raw5214step4 = (fun i j => raw5214step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5214step4 raw5214step3; decide +kernel
      have hl : raw5214step4Labels = raw5214step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5214step3 raw5214step3Labels permutation7 permutation0
    mixedMoment B raw5214step4 raw5214step4Labels = mixedMoment B raw5214step5 raw5214step5Labels := by
      have ha : raw5214step5 = -raw5214step4 := by apply Matrix.ext; change ∀ i j, raw5214step5 i j = -(raw5214step4 i j); unfold raw5214step5 raw5214step4; decide +kernel
      have hl : raw5214step5Labels = raw5214step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6553 raw6553Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6553 raw6553Labels = mixedMoment B raw6553step0 raw6553step0Labels := by
      have hz : ∀ j, raw6553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6553step0 = (fun i j => raw6553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6553step0 raw6553; decide +kernel
      have hl : raw6553step0Labels = raw6553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553 raw6553Labels permutation520 hz
    mixedMoment B raw6553step0 raw6553step0Labels = mixedMoment B raw6553step1 raw6553step1Labels := by
      have hz : ∀ j, raw6553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6553step1 = (fun i j => raw6553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6553step1 raw6553step0; decide +kernel
      have hl : raw6553step1Labels = raw6553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553step0 raw6553step0Labels permutation80 hz
    mixedMoment B raw6553step1 raw6553step1Labels = mixedMoment B raw6553step2 raw6553step2Labels := by
      have ha : raw6553step2 = (fun i j => raw6553step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6553step2 raw6553step1; decide +kernel
      have hl : raw6553step2Labels = raw6553step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6553step1 raw6553step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical6564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6564 raw6564Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw6564 raw6564Labels = mixedMoment B raw6564step0 raw6564step0Labels := by
      have hz : ∀ j, raw6564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6564step0 = (fun i j => raw6564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6564step0 raw6564; decide +kernel
      have hl : raw6564step0Labels = raw6564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6564 raw6564Labels permutation346 hz
    mixedMoment B raw6564step0 raw6564step0Labels = mixedMoment B raw6564step1 raw6564step1Labels := by
      have ha : raw6564step1 = (fun i j => raw6564step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6564step1 raw6564step0; decide +kernel
      have hl : raw6564step1Labels = raw6564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6564step0 raw6564step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical6565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6565 raw6565Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw6565 raw6565Labels = mixedMoment B raw6565step0 raw6565step0Labels := by
      have hz : ∀ j, raw6565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6565step0 = (fun i j => raw6565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6565step0 raw6565; decide +kernel
      have hl : raw6565step0Labels = raw6565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6565 raw6565Labels permutation346 hz
    _ = mixedMoment B node2499 node2499Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8531 raw8531Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8531 raw8531Labels = mixedMoment B raw8531step0 raw8531step0Labels := by
      have hz : ∀ j, raw8531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8531step0 = (fun i j => raw8531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8531step0 raw8531; decide +kernel
      have hl : raw8531step0Labels = raw8531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531 raw8531Labels permutation346 hz
    mixedMoment B raw8531step0 raw8531step0Labels = mixedMoment B raw8531step1 raw8531step1Labels := by
      have hz : ∀ j, raw8531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8531step1 = (fun i j => raw8531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8531step1 raw8531step0; decide +kernel
      have hl : raw8531step1Labels = raw8531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531step0 raw8531step0Labels permutation56 hz
    mixedMoment B raw8531step1 raw8531step1Labels = mixedMoment B raw8531step2 raw8531step2Labels := by
      have ha : raw8531step2 = (fun i j => raw8531step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8531step2 raw8531step1; decide +kernel
      have hl : raw8531step2Labels = raw8531step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8531step1 raw8531step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8543 raw8543Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8543 raw8543Labels = mixedMoment B raw8543step0 raw8543step0Labels := by
      have hz : ∀ j, raw8543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8543step0 = (fun i j => raw8543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8543step0 raw8543; decide +kernel
      have hl : raw8543step0Labels = raw8543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8543 raw8543Labels permutation346 hz
    mixedMoment B raw8543step0 raw8543step0Labels = mixedMoment B raw8543step1 raw8543step1Labels := by
      have ha : raw8543step1 = (fun i j => raw8543step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8543step1 raw8543step0; decide +kernel
      have hl : raw8543step1Labels = raw8543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8543step0 raw8543step0Labels permutation33 permutation2
    _ = mixedMoment B node2979 node2979Labels := by rfl

theorem canonical8546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8546 raw8546Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw8546 raw8546Labels = mixedMoment B raw8546step0 raw8546step0Labels := by
      have hz : ∀ j, raw8546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8546step0 = (fun i j => raw8546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8546step0 raw8546; decide +kernel
      have hl : raw8546step0Labels = raw8546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546 raw8546Labels permutation346 hz
    mixedMoment B raw8546step0 raw8546step0Labels = mixedMoment B raw8546step1 raw8546step1Labels := by
      have hz : ∀ j, raw8546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8546step1 = (fun i j => raw8546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8546step1 raw8546step0; decide +kernel
      have hl : raw8546step1Labels = raw8546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546step0 raw8546step0Labels permutation56 hz
    mixedMoment B raw8546step1 raw8546step1Labels = mixedMoment B raw8546step2 raw8546step2Labels := by
      have ha : raw8546step2 = (fun i j => raw8546step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8546step2 raw8546step1; decide +kernel
      have hl : raw8546step2Labels = raw8546step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8546step1 raw8546step1Labels permutation9 permutation2
    _ = mixedMoment B node2889 node2889Labels := by rfl

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

theorem canonical11535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11535 raw11535Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11535 raw11535Labels = mixedMoment B raw11535step0 raw11535step0Labels := by
      have hz : ∀ j, raw11535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11535step0 = (fun i j => raw11535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11535step0 raw11535; decide +kernel
      have hl : raw11535step0Labels = raw11535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11535 raw11535Labels permutation434 hz
    mixedMoment B raw11535step0 raw11535step0Labels = mixedMoment B raw11535step1 raw11535step1Labels := by
      have hz : ∀ i, raw11535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11535step1 = (fun i j => raw11535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11535step1 raw11535step0; decide +kernel
      have hl : raw11535step1Labels = (fun j => raw11535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11535step0 raw11535step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem sound910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node910 node910Labels = Sparse.eval nodeValue910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 910) = mixedMoment B node910 node910Labels := rfl
  simpa [nodeValue910, Sparse.eval] using hc.symm

theorem sound950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node950 node950Labels = Sparse.eval nodeValue950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 950) = mixedMoment B node950 node950Labels := rfl
  simpa [nodeValue950, Sparse.eval] using hc.symm

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

theorem sound1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1141 node1141Labels = Sparse.eval nodeValue1141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1141) = mixedMoment B node1141 node1141Labels := rfl
  simpa [nodeValue1141, Sparse.eval] using hc.symm

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

theorem sound1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1794 node1794Labels = Sparse.eval nodeValue1794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1794) = mixedMoment B node1794 node1794Labels := rfl
  simpa [nodeValue1794, Sparse.eval] using hc.symm

theorem sound1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1829 node1829Labels = Sparse.eval nodeValue1829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1829) = mixedMoment B node1829 node1829Labels := rfl
  simpa [nodeValue1829, Sparse.eval] using hc.symm

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

theorem sound1977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1977 node1977Labels = Sparse.eval nodeValue1977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1977) = mixedMoment B node1977 node1977Labels := rfl
  simpa [nodeValue1977, Sparse.eval] using hc.symm

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

theorem sound2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2012 node2012Labels = Sparse.eval nodeValue2012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2012) = mixedMoment B node2012 node2012Labels := rfl
  simpa [nodeValue2012, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2094 node2094Labels = Sparse.eval nodeValue2094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2094) = mixedMoment B node2094 node2094Labels := rfl
  simpa [nodeValue2094, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2280 node2280Labels = Sparse.eval nodeValue2280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2280) = mixedMoment B node2280 node2280Labels := rfl
  simpa [nodeValue2280, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

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

theorem sound2323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2323 node2323Labels = Sparse.eval nodeValue2323 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2323) = mixedMoment B node2323 node2323Labels := rfl
  simpa [nodeValue2323, Sparse.eval] using hc.symm

theorem sound2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2327 node2327Labels = Sparse.eval nodeValue2327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2327) = mixedMoment B node2327 node2327Labels := rfl
  simpa [nodeValue2327, Sparse.eval] using hc.symm

theorem sound2335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2335 node2335Labels = Sparse.eval nodeValue2335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2335) = mixedMoment B node2335 node2335Labels := rfl
  simpa [nodeValue2335, Sparse.eval] using hc.symm

theorem sound2340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2340 node2340Labels = Sparse.eval nodeValue2340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2340) = mixedMoment B node2340 node2340Labels := rfl
  simpa [nodeValue2340, Sparse.eval] using hc.symm

theorem sound2343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2343 node2343Labels = Sparse.eval nodeValue2343 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2343) = mixedMoment B node2343 node2343Labels := rfl
  simpa [nodeValue2343, Sparse.eval] using hc.symm

theorem sound2346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2346 node2346Labels = Sparse.eval nodeValue2346 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2346) = mixedMoment B node2346 node2346Labels := rfl
  simpa [nodeValue2346, Sparse.eval] using hc.symm

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

theorem sound2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2396 node2396Labels = Sparse.eval nodeValue2396 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2396) = mixedMoment B node2396 node2396Labels := rfl
  simpa [nodeValue2396, Sparse.eval] using hc.symm

theorem sound2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2401 node2401Labels = Sparse.eval nodeValue2401 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2401) = mixedMoment B node2401 node2401Labels := rfl
  simpa [nodeValue2401, Sparse.eval] using hc.symm

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

theorem sound2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2433 node2433Labels = Sparse.eval nodeValue2433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2433) = mixedMoment B node2433 node2433Labels := rfl
  simpa [nodeValue2433, Sparse.eval] using hc.symm

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

theorem sound2499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2499 node2499Labels = Sparse.eval nodeValue2499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2499) = mixedMoment B node2499 node2499Labels := rfl
  simpa [nodeValue2499, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound2800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2800 node2800Labels = Sparse.eval nodeValue2800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2800) = mixedMoment B node2800 node2800Labels := rfl
  simpa [nodeValue2800, Sparse.eval] using hc.symm

theorem sound2803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2803 node2803Labels = Sparse.eval nodeValue2803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2803) = mixedMoment B node2803 node2803Labels := rfl
  simpa [nodeValue2803, Sparse.eval] using hc.symm

theorem sound2811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2811 node2811Labels = Sparse.eval nodeValue2811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2811) = mixedMoment B node2811 node2811Labels := rfl
  simpa [nodeValue2811, Sparse.eval] using hc.symm

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

theorem sound2821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2821 node2821Labels = Sparse.eval nodeValue2821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2821) = mixedMoment B node2821 node2821Labels := rfl
  simpa [nodeValue2821, Sparse.eval] using hc.symm

theorem sound2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2846 node2846Labels = Sparse.eval nodeValue2846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2846) = mixedMoment B node2846 node2846Labels := rfl
  simpa [nodeValue2846, Sparse.eval] using hc.symm

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

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2979 node2979Labels = Sparse.eval nodeValue2979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2979) = mixedMoment B node2979 node2979Labels := rfl
  simpa [nodeValue2979, Sparse.eval] using hc.symm

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

theorem sound3129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3129 node3129Labels = Sparse.eval nodeValue3129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3129) = mixedMoment B node3129 node3129Labels := rfl
  simpa [nodeValue3129, Sparse.eval] using hc.symm

theorem sound3133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3133 node3133Labels = Sparse.eval nodeValue3133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3133) = mixedMoment B node3133 node3133Labels := rfl
  simpa [nodeValue3133, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3138 node3138Labels = Sparse.eval nodeValue3138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3138) = mixedMoment B node3138 node3138Labels := rfl
  simpa [nodeValue3138, Sparse.eval] using hc.symm

theorem sound3147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3147 node3147Labels = Sparse.eval nodeValue3147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3147) = mixedMoment B node3147 node3147Labels := rfl
  simpa [nodeValue3147, Sparse.eval] using hc.symm

theorem sound3161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3161 node3161Labels = Sparse.eval nodeValue3161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3161) = mixedMoment B node3161 node3161Labels := rfl
  simpa [nodeValue3161, Sparse.eval] using hc.symm

theorem sound3162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3162 node3162Labels = Sparse.eval nodeValue3162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3162) = mixedMoment B node3162 node3162Labels := rfl
  simpa [nodeValue3162, Sparse.eval] using hc.symm

theorem sound3166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3166 node3166Labels = Sparse.eval nodeValue3166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3166) = mixedMoment B node3166 node3166Labels := rfl
  simpa [nodeValue3166, Sparse.eval] using hc.symm

theorem sound3174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3174 node3174Labels = Sparse.eval nodeValue3174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3174) = mixedMoment B node3174 node3174Labels := rfl
  simpa [nodeValue3174, Sparse.eval] using hc.symm

theorem sound3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3189 node3189Labels = Sparse.eval nodeValue3189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3189) = mixedMoment B node3189 node3189Labels := rfl
  simpa [nodeValue3189, Sparse.eval] using hc.symm

theorem sound3193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3193 node3193Labels = Sparse.eval nodeValue3193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3193) = mixedMoment B node3193 node3193Labels := rfl
  simpa [nodeValue3193, Sparse.eval] using hc.symm

theorem sound3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3198 node3198Labels = Sparse.eval nodeValue3198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3198) = mixedMoment B node3198 node3198Labels := rfl
  simpa [nodeValue3198, Sparse.eval] using hc.symm

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3372 node3372Labels = Sparse.eval nodeValue3372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3372) = mixedMoment B node3372 node3372Labels := rfl
  simpa [nodeValue3372, Sparse.eval] using hc.symm

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

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound3473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3473 node3473Labels = Sparse.eval nodeValue3473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3473) = mixedMoment B node3473 node3473Labels := rfl
  simpa [nodeValue3473, Sparse.eval] using hc.symm

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

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

theorem sound3536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3536 node3536Labels = Sparse.eval nodeValue3536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3536) = mixedMoment B node3536 node3536Labels := rfl
  simpa [nodeValue3536, Sparse.eval] using hc.symm

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

theorem sound3610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3610 node3610Labels = Sparse.eval nodeValue3610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3610) = mixedMoment B node3610 node3610Labels := rfl
  simpa [nodeValue3610, Sparse.eval] using hc.symm

theorem sound3611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3611 node3611Labels = Sparse.eval nodeValue3611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3611) = mixedMoment B node3611 node3611Labels := rfl
  simpa [nodeValue3611, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3630 node3630Labels = Sparse.eval nodeValue3630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3630) = mixedMoment B node3630 node3630Labels := rfl
  simpa [nodeValue3630, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem sound3648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3648 node3648Labels = Sparse.eval nodeValue3648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3648) = mixedMoment B node3648 node3648Labels := rfl
  simpa [nodeValue3648, Sparse.eval] using hc.symm

theorem sound3653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3653 node3653Labels = Sparse.eval nodeValue3653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3653) = mixedMoment B node3653 node3653Labels := rfl
  simpa [nodeValue3653, Sparse.eval] using hc.symm

theorem sound3658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3658 node3658Labels = Sparse.eval nodeValue3658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3658) = mixedMoment B node3658 node3658Labels := rfl
  simpa [nodeValue3658, Sparse.eval] using hc.symm

theorem sound3659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3659 node3659Labels = Sparse.eval nodeValue3659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3659) = mixedMoment B node3659 node3659Labels := rfl
  simpa [nodeValue3659, Sparse.eval] using hc.symm

theorem sound3660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3660 node3660Labels = Sparse.eval nodeValue3660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3660) = mixedMoment B node3660 node3660Labels := rfl
  simpa [nodeValue3660, Sparse.eval] using hc.symm

theorem sound3666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3666 node3666Labels = Sparse.eval nodeValue3666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3666) = mixedMoment B node3666 node3666Labels := rfl
  simpa [nodeValue3666, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

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

theorem sound3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3762 node3762Labels = Sparse.eval nodeValue3762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3762) = mixedMoment B node3762 node3762Labels := rfl
  simpa [nodeValue3762, Sparse.eval] using hc.symm

theorem sound3772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3772 node3772Labels = Sparse.eval nodeValue3772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3772) = mixedMoment B node3772 node3772Labels := rfl
  simpa [nodeValue3772, Sparse.eval] using hc.symm

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

theorem sound4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4064 node4064Labels = Sparse.eval nodeValue4064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4064) = mixedMoment B node4064 node4064Labels := rfl
  simpa [nodeValue4064, Sparse.eval] using hc.symm

theorem sound4066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4066 node4066Labels = Sparse.eval nodeValue4066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4066) = mixedMoment B node4066 node4066Labels := rfl
  simpa [nodeValue4066, Sparse.eval] using hc.symm

theorem sound4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4067 node4067Labels = Sparse.eval nodeValue4067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4067) = mixedMoment B node4067 node4067Labels := rfl
  simpa [nodeValue4067, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4074 node4074Labels = Sparse.eval nodeValue4074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4074) = mixedMoment B node4074 node4074Labels := rfl
  simpa [nodeValue4074, Sparse.eval] using hc.symm

theorem sound4076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4076 node4076Labels = Sparse.eval nodeValue4076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4076) = mixedMoment B node4076 node4076Labels := rfl
  simpa [nodeValue4076, Sparse.eval] using hc.symm

theorem sound4077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4077 node4077Labels = Sparse.eval nodeValue4077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4077) = mixedMoment B node4077 node4077Labels := rfl
  simpa [nodeValue4077, Sparse.eval] using hc.symm

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

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2089 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 1) (sourceB2089 + difference 1 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 1) (sourceB2089 + difference 1 0) sourceC2089) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 2) (sourceB2089 + difference 2 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 2) (sourceB2089 + difference 2 0) sourceC2089) = raw18343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18343; decide +kernel
    rw [ha]
    exact (canonical18343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 3) (sourceB2089 + difference 3 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 3) (sourceB2089 + difference 3 0) sourceC2089) = raw18344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18344; decide +kernel
    rw [ha]
    exact (canonical18344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 4) (sourceB2089 + difference 4 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 4) (sourceB2089 + difference 4 0) sourceC2089) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 5) (sourceB2089 + difference 5 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 5) (sourceB2089 + difference 5 0) sourceC2089) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 0) (sourceB2089 + difference 0 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 0) (sourceB2089 + difference 0 1) sourceC2089) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 2) (sourceB2089 + difference 2 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 2) (sourceB2089 + difference 2 1) sourceC2089) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 3) (sourceB2089 + difference 3 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 3) (sourceB2089 + difference 3 1) sourceC2089) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 4) (sourceB2089 + difference 4 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 4) (sourceB2089 + difference 4 1) sourceC2089) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 5) (sourceB2089 + difference 5 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 5) (sourceB2089 + difference 5 1) sourceC2089) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 0) (sourceB2089 + difference 0 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 0) (sourceB2089 + difference 0 2) sourceC2089) = raw22305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22305; decide +kernel
    rw [ha]
    exact (canonical22305 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 1) (sourceB2089 + difference 1 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 1) (sourceB2089 + difference 1 2) sourceC2089) = raw29295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29295; decide +kernel
    rw [ha]
    exact (canonical29295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 3) (sourceB2089 + difference 3 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 3) (sourceB2089 + difference 3 2) sourceC2089) = raw29296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29296; decide +kernel
    rw [ha]
    exact (canonical29296 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 4) (sourceB2089 + difference 4 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 4) (sourceB2089 + difference 4 2) sourceC2089) = raw5202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5202; decide +kernel
    rw [ha]
    exact (canonical5202 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 5) (sourceB2089 + difference 5 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 5) (sourceB2089 + difference 5 2) sourceC2089) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 0) (sourceB2089 + difference 0 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 0) (sourceB2089 + difference 0 3) sourceC2089) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 1) (sourceB2089 + difference 1 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 1) (sourceB2089 + difference 1 3) sourceC2089) = raw29297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29297; decide +kernel
    rw [ha]
    exact (canonical29297 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 2) (sourceB2089 + difference 2 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 2) (sourceB2089 + difference 2 3) sourceC2089) = raw29298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29298; decide +kernel
    rw [ha]
    exact (canonical29298 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 4) (sourceB2089 + difference 4 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 4) (sourceB2089 + difference 4 3) sourceC2089) = raw5206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5206; decide +kernel
    rw [ha]
    exact (canonical5206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 5) (sourceB2089 + difference 5 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 5) (sourceB2089 + difference 5 3) sourceC2089) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 0) (sourceB2089 + difference 0 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 0) (sourceB2089 + difference 0 4) sourceC2089) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 1) (sourceB2089 + difference 1 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 1) (sourceB2089 + difference 1 4) sourceC2089) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 2) (sourceB2089 + difference 2 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 2) (sourceB2089 + difference 2 4) sourceC2089) = raw29300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29300; decide +kernel
    rw [ha]
    exact (canonical29300 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 3) (sourceB2089 + difference 3 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 3) (sourceB2089 + difference 3 4) sourceC2089) = raw29301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29301; decide +kernel
    rw [ha]
    exact (canonical29301 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 5) (sourceB2089 + difference 5 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 5) (sourceB2089 + difference 5 4) sourceC2089) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 0) (sourceB2089 + difference 0 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 0) (sourceB2089 + difference 0 5) sourceC2089) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 1) (sourceB2089 + difference 1 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 1) (sourceB2089 + difference 1 5) sourceC2089) = raw29302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29302; decide +kernel
    rw [ha]
    exact (canonical29302 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 2) (sourceB2089 + difference 2 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 2) (sourceB2089 + difference 2 5) sourceC2089) = raw29303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29303; decide +kernel
    rw [ha]
    exact (canonical29303 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 3) (sourceB2089 + difference 3 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 3) (sourceB2089 + difference 3 5) sourceC2089) = raw29304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29304; decide +kernel
    rw [ha]
    exact (canonical29304 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 4) (sourceB2089 + difference 4 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 4) (sourceB2089 + difference 4 5) sourceC2089) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2089 sourceB2089 sourceC2089
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2089, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2091 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2091 + difference 0 3) (sourceB2091 + difference 3 0) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2091 + difference 0 3) (sourceB2091 + difference 3 0) sourceC2091) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2091 + difference 1 3) (sourceB2091 + difference 3 1) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2091 + difference 1 3) (sourceB2091 + difference 3 1) sourceC2091) = raw29309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29309; decide +kernel
    rw [ha]
    exact (canonical29309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2091 + difference 2 3) (sourceB2091 + difference 3 2) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3162) := by
    have ha : (tripleCharges (sourceA2091 + difference 2 3) (sourceB2091 + difference 3 2) sourceC2091) = raw29310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29310; decide +kernel
    rw [ha]
    exact (canonical29310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2091 + difference 3 3) (sourceB2091 + difference 3 3) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA2091 + difference 3 3) (sourceB2091 + difference 3 3) sourceC2091) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2091 + difference 4 3) (sourceB2091 + difference 3 4) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2091 + difference 4 3) (sourceB2091 + difference 3 4) sourceC2091) = raw29311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29311; decide +kernel
    rw [ha]
    exact (canonical29311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2091 + difference 5 3) (sourceB2091 + difference 3 5) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2091 + difference 5 3) (sourceB2091 + difference 3 5) sourceC2091) = raw29312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29312; decide +kernel
    rw [ha]
    exact (canonical29312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2091 + sourceB2091) sourceC2091) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2091 + sourceB2091) sourceC2091) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA2091 sourceB2091 sourceC2091 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2091 sourceB2091 sourceC2091
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2091, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2092 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2092 + difference 0 3) (sourceB2092 + difference 3 0) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2092 + difference 0 3) (sourceB2092 + difference 3 0) sourceC2092) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2092 + difference 1 3) (sourceB2092 + difference 3 1) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2092 + difference 1 3) (sourceB2092 + difference 3 1) sourceC2092) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2092 + difference 2 3) (sourceB2092 + difference 3 2) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2092 + difference 2 3) (sourceB2092 + difference 3 2) sourceC2092) = raw29315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29315; decide +kernel
    rw [ha]
    exact (canonical29315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2092 + difference 3 3) (sourceB2092 + difference 3 3) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2092 + difference 3 3) (sourceB2092 + difference 3 3) sourceC2092) = raw29316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29316; decide +kernel
    rw [ha]
    exact (canonical29316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2092 + difference 4 3) (sourceB2092 + difference 3 4) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2092 + difference 4 3) (sourceB2092 + difference 3 4) sourceC2092) = raw29317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29317; decide +kernel
    rw [ha]
    exact (canonical29317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2092 + difference 5 3) (sourceB2092 + difference 3 5) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2092 + difference 5 3) (sourceB2092 + difference 3 5) sourceC2092) = raw29318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29318; decide +kernel
    rw [ha]
    exact (canonical29318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2092 + sourceB2092) sourceC2092) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2092 + sourceB2092) sourceC2092) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2092 sourceB2092 sourceC2092 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2092 sourceB2092 sourceC2092
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2092, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2093 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 0) (sourceB2093 + difference 0 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 0) (sourceB2093 + difference 0 2) sourceC2093) = raw22353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw22353; decide +kernel
    rw [ha]
    exact (canonical22353 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 1) (sourceB2093 + difference 1 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 1) (sourceB2093 + difference 1 2) sourceC2093) = raw29320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29320; decide +kernel
    rw [ha]
    exact (canonical29320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 2) (sourceB2093 + difference 2 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 2) (sourceB2093 + difference 2 2) sourceC2093) = raw29321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29321; decide +kernel
    rw [ha]
    exact (canonical29321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 3) (sourceB2093 + difference 3 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1977) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 3) (sourceB2093 + difference 3 2) sourceC2093) = raw29322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29322; decide +kernel
    rw [ha]
    exact (canonical29322 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 4) (sourceB2093 + difference 4 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 4) (sourceB2093 + difference 4 2) sourceC2093) = raw27373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw27373; decide +kernel
    rw [ha]
    exact (canonical27373 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 5) (sourceB2093 + difference 5 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 5) (sourceB2093 + difference 5 2) sourceC2093) = raw29323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29323; decide +kernel
    rw [ha]
    exact (canonical29323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2093 + sourceB2093) sourceC2093) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2093 + sourceB2093) sourceC2093) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA2093 sourceB2093 sourceC2093 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2093 sourceB2093 sourceC2093
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2093, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2094 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2094 + difference 0 2) (sourceB2094 + difference 2 0) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2094 + difference 0 2) (sourceB2094 + difference 2 0) sourceC2094) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2094 + difference 1 2) (sourceB2094 + difference 2 1) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2094 + difference 1 2) (sourceB2094 + difference 2 1) sourceC2094) = raw29324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29324; decide +kernel
    rw [ha]
    exact (canonical29324 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2094 + difference 2 2) (sourceB2094 + difference 2 2) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2094 + difference 2 2) (sourceB2094 + difference 2 2) sourceC2094) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2094 + difference 3 2) (sourceB2094 + difference 2 3) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3189) := by
    have ha : (tripleCharges (sourceA2094 + difference 3 2) (sourceB2094 + difference 2 3) sourceC2094) = raw29325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29325; decide +kernel
    rw [ha]
    exact (canonical29325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2094 + difference 4 2) (sourceB2094 + difference 2 4) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA2094 + difference 4 2) (sourceB2094 + difference 2 4) sourceC2094) = raw29326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29326; decide +kernel
    rw [ha]
    exact (canonical29326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2094 + difference 5 2) (sourceB2094 + difference 2 5) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2094 + difference 5 2) (sourceB2094 + difference 2 5) sourceC2094) = raw29327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29327; decide +kernel
    rw [ha]
    exact (canonical29327 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2094 + sourceB2094) sourceC2094) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2094 + sourceB2094) sourceC2094) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA2094 sourceB2094 sourceC2094 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2094 sourceB2094 sourceC2094
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2094, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2095 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 0) (sourceB2095 + difference 0 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 0) (sourceB2095 + difference 0 0) sourceC2095) = raw29315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29315; decide +kernel
    rw [ha]
    exact (canonical29315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 1) (sourceB2095 + difference 1 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 1) (sourceB2095 + difference 1 0) sourceC2095) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 2) (sourceB2095 + difference 2 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 2) (sourceB2095 + difference 2 0) sourceC2095) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 3) (sourceB2095 + difference 3 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 3) (sourceB2095 + difference 3 0) sourceC2095) = raw29329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29329; decide +kernel
    rw [ha]
    exact (canonical29329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 4) (sourceB2095 + difference 4 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 4) (sourceB2095 + difference 4 0) sourceC2095) = raw29330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29330; decide +kernel
    rw [ha]
    exact (canonical29330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 5) (sourceB2095 + difference 5 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3610) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 5) (sourceB2095 + difference 5 0) sourceC2095) = raw29331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29331; decide +kernel
    rw [ha]
    exact (canonical29331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2095 + sourceB2095) sourceC2095) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2095 + sourceB2095) sourceC2095) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2095 sourceB2095 sourceC2095 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2095 sourceB2095 sourceC2095
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2095, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2097 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 0) (sourceB2097 + difference 0 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3193) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 0) (sourceB2097 + difference 0 0) sourceC2097) = raw29336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29336; decide +kernel
    rw [ha]
    exact (canonical29336 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 1) (sourceB2097 + difference 1 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3648) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 1) (sourceB2097 + difference 1 0) sourceC2097) = raw29337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29337; decide +kernel
    rw [ha]
    exact (canonical29337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 2) (sourceB2097 + difference 2 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3659) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 2) (sourceB2097 + difference 2 0) sourceC2097) = raw29338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29338; decide +kernel
    rw [ha]
    exact (canonical29338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 3) (sourceB2097 + difference 3 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 3) (sourceB2097 + difference 3 0) sourceC2097) = raw29339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29339; decide +kernel
    rw [ha]
    exact (canonical29339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 4) (sourceB2097 + difference 4 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 4) (sourceB2097 + difference 4 0) sourceC2097) = raw29340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29340; decide +kernel
    rw [ha]
    exact (canonical29340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 5) (sourceB2097 + difference 5 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 5) (sourceB2097 + difference 5 0) sourceC2097) = raw29341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29341; decide +kernel
    rw [ha]
    exact (canonical29341 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2097 + sourceB2097) sourceC2097) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2097 + sourceB2097) sourceC2097) = raw29342 := by
      apply Matrix.ext; unfold doubleCharges sourceA2097 sourceB2097 sourceC2097 raw29342; decide +kernel
    rw [ha]
    exact (canonical29342 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2097 sourceB2097 sourceC2097
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2097, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2098 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 0) (sourceB2098 + difference 0 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 0) (sourceB2098 + difference 0 3) sourceC2098) = raw25239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw25239; decide +kernel
    rw [ha]
    exact (canonical25239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 1) (sourceB2098 + difference 1 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 1) (sourceB2098 + difference 1 3) sourceC2098) = raw29343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29343; decide +kernel
    rw [ha]
    exact (canonical29343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 2) (sourceB2098 + difference 2 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1977) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 2) (sourceB2098 + difference 2 3) sourceC2098) = raw29344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29344; decide +kernel
    rw [ha]
    exact (canonical29344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 3) (sourceB2098 + difference 3 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 3) (sourceB2098 + difference 3 3) sourceC2098) = raw29345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29345; decide +kernel
    rw [ha]
    exact (canonical29345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 4) (sourceB2098 + difference 4 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 4) (sourceB2098 + difference 4 3) sourceC2098) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 5) (sourceB2098 + difference 5 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 5) (sourceB2098 + difference 5 3) sourceC2098) = raw29346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29346; decide +kernel
    rw [ha]
    exact (canonical29346 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2098 + sourceB2098) sourceC2098) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2098 + sourceB2098) sourceC2098) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA2098 sourceB2098 sourceC2098 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2098 sourceB2098 sourceC2098
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2098, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2099 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2099 + difference 0 1) (sourceB2099 + difference 1 0) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2099 + difference 0 1) (sourceB2099 + difference 1 0) sourceC2099) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2099 + difference 1 1) (sourceB2099 + difference 1 1) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2099 + difference 1 1) (sourceB2099 + difference 1 1) sourceC2099) = raw16536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw16536; decide +kernel
    rw [ha]
    exact (canonical16536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2099 + difference 2 1) (sourceB2099 + difference 1 2) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2099 + difference 2 1) (sourceB2099 + difference 1 2) sourceC2099) = raw29347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29347; decide +kernel
    rw [ha]
    exact (canonical29347 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2099 + difference 3 1) (sourceB2099 + difference 1 3) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2099 + difference 3 1) (sourceB2099 + difference 1 3) sourceC2099) = raw29348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29348; decide +kernel
    rw [ha]
    exact (canonical29348 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2099 + difference 4 1) (sourceB2099 + difference 1 4) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2099 + difference 4 1) (sourceB2099 + difference 1 4) sourceC2099) = raw29349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29349; decide +kernel
    rw [ha]
    exact (canonical29349 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2099 + difference 5 1) (sourceB2099 + difference 1 5) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2099 + difference 5 1) (sourceB2099 + difference 1 5) sourceC2099) = raw29350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29350; decide +kernel
    rw [ha]
    exact (canonical29350 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2099 + sourceB2099) sourceC2099) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2099 + sourceB2099) sourceC2099) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2099 sourceB2099 sourceC2099 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2099 sourceB2099 sourceC2099
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2099, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2100 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 0) (sourceB2100 + difference 0 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 0) (sourceB2100 + difference 0 0) sourceC2100) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 1) (sourceB2100 + difference 1 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 1) (sourceB2100 + difference 1 0) sourceC2100) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 2) (sourceB2100 + difference 2 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 2) (sourceB2100 + difference 2 0) sourceC2100) = raw29351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29351; decide +kernel
    rw [ha]
    exact (canonical29351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 3) (sourceB2100 + difference 3 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 3) (sourceB2100 + difference 3 0) sourceC2100) = raw29352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29352; decide +kernel
    rw [ha]
    exact (canonical29352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 4) (sourceB2100 + difference 4 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 4) (sourceB2100 + difference 4 0) sourceC2100) = raw29353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29353; decide +kernel
    rw [ha]
    exact (canonical29353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 5) (sourceB2100 + difference 5 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3630) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 5) (sourceB2100 + difference 5 0) sourceC2100) = raw29354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29354; decide +kernel
    rw [ha]
    exact (canonical29354 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2100 + sourceB2100) sourceC2100) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2100 + sourceB2100) sourceC2100) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2100 sourceB2100 sourceC2100 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2100 sourceB2100 sourceC2100
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2100, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2101 + difference 0 3) (sourceB2101 + difference 3 0) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2101 + difference 0 3) (sourceB2101 + difference 3 0) sourceC2101) = raw29352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29352; decide +kernel
    rw [ha]
    exact (canonical29352 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2101 + difference 1 3) (sourceB2101 + difference 3 1) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA2101 + difference 1 3) (sourceB2101 + difference 3 1) sourceC2101) = raw29355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29355; decide +kernel
    rw [ha]
    exact (canonical29355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2101 + difference 2 3) (sourceB2101 + difference 3 2) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2101 + difference 2 3) (sourceB2101 + difference 3 2) sourceC2101) = raw29356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29356; decide +kernel
    rw [ha]
    exact (canonical29356 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2101 + difference 3 3) (sourceB2101 + difference 3 3) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2101 + difference 3 3) (sourceB2101 + difference 3 3) sourceC2101) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2101 + difference 4 3) (sourceB2101 + difference 3 4) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2101 + difference 4 3) (sourceB2101 + difference 3 4) sourceC2101) = raw29357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29357; decide +kernel
    rw [ha]
    exact (canonical29357 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2101 + difference 5 3) (sourceB2101 + difference 3 5) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2101 + difference 5 3) (sourceB2101 + difference 3 5) sourceC2101) = raw29358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29358; decide +kernel
    rw [ha]
    exact (canonical29358 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2101 + sourceB2101) sourceC2101) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2101 + sourceB2101) sourceC2101) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2101 sourceB2101 sourceC2101 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2101 sourceB2101 sourceC2101
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2101, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 0) (sourceB2102 + difference 0 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3166) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 0) (sourceB2102 + difference 0 0) sourceC2102) = raw29359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29359; decide +kernel
    rw [ha]
    exact (canonical29359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 1) (sourceB2102 + difference 1 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 1) (sourceB2102 + difference 1 0) sourceC2102) = raw29360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29360; decide +kernel
    rw [ha]
    exact (canonical29360 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 2) (sourceB2102 + difference 2 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3658) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 2) (sourceB2102 + difference 2 0) sourceC2102) = raw29361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29361; decide +kernel
    rw [ha]
    exact (canonical29361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 3) (sourceB2102 + difference 3 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3666) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 3) (sourceB2102 + difference 3 0) sourceC2102) = raw29362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29362; decide +kernel
    rw [ha]
    exact (canonical29362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 4) (sourceB2102 + difference 4 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 4) (sourceB2102 + difference 4 0) sourceC2102) = raw29363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29363; decide +kernel
    rw [ha]
    exact (canonical29363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 5) (sourceB2102 + difference 5 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 5) (sourceB2102 + difference 5 0) sourceC2102) = raw29364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29364; decide +kernel
    rw [ha]
    exact (canonical29364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2102 + sourceB2102) sourceC2102) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2102 + sourceB2102) sourceC2102) = raw29365 := by
      apply Matrix.ext; unfold doubleCharges sourceA2102 sourceB2102 sourceC2102 raw29365; decide +kernel
    rw [ha]
    exact (canonical29365 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2102 sourceB2102 sourceC2102
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2102, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2103 + difference 0 1) (sourceB2103 + difference 1 0) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2103 + difference 0 1) (sourceB2103 + difference 1 0) sourceC2103) = raw29366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29366; decide +kernel
    rw [ha]
    exact (canonical29366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2103 + difference 1 1) (sourceB2103 + difference 1 1) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA2103 + difference 1 1) (sourceB2103 + difference 1 1) sourceC2103) = raw29367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29367; decide +kernel
    rw [ha]
    exact (canonical29367 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2103 + difference 2 1) (sourceB2103 + difference 1 2) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2103 + difference 2 1) (sourceB2103 + difference 1 2) sourceC2103) = raw29368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29368; decide +kernel
    rw [ha]
    exact (canonical29368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2103 + difference 3 1) (sourceB2103 + difference 1 3) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2103 + difference 3 1) (sourceB2103 + difference 1 3) sourceC2103) = raw29369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29369; decide +kernel
    rw [ha]
    exact (canonical29369 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2103 + difference 4 1) (sourceB2103 + difference 1 4) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA2103 + difference 4 1) (sourceB2103 + difference 1 4) sourceC2103) = raw29370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29370; decide +kernel
    rw [ha]
    exact (canonical29370 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2103 + difference 5 1) (sourceB2103 + difference 1 5) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2103 + difference 5 1) (sourceB2103 + difference 1 5) sourceC2103) = raw29371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29371; decide +kernel
    rw [ha]
    exact (canonical29371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2103 + sourceB2103) sourceC2103) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2103 + sourceB2103) sourceC2103) = raw29372 := by
      apply Matrix.ext; unfold doubleCharges sourceA2103 sourceB2103 sourceC2103 raw29372; decide +kernel
    rw [ha]
    exact (canonical29372 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2103 sourceB2103 sourceC2103
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2103, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2104 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 0) (sourceB2104 + difference 0 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3147) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 0) (sourceB2104 + difference 0 0) sourceC2104) = raw29373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29373; decide +kernel
    rw [ha]
    exact (canonical29373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 1) (sourceB2104 + difference 1 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 1) (sourceB2104 + difference 1 0) sourceC2104) = raw29374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29374; decide +kernel
    rw [ha]
    exact (canonical29374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 2) (sourceB2104 + difference 2 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3473) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 2) (sourceB2104 + difference 2 0) sourceC2104) = raw29375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29375; decide +kernel
    rw [ha]
    exact (canonical29375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 3) (sourceB2104 + difference 3 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3611) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 3) (sourceB2104 + difference 3 0) sourceC2104) = raw29376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29376; decide +kernel
    rw [ha]
    exact (canonical29376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 4) (sourceB2104 + difference 4 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 4) (sourceB2104 + difference 4 0) sourceC2104) = raw29377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29377; decide +kernel
    rw [ha]
    exact (canonical29377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 5) (sourceB2104 + difference 5 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 5) (sourceB2104 + difference 5 0) sourceC2104) = raw29378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29378; decide +kernel
    rw [ha]
    exact (canonical29378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2104 + sourceB2104) sourceC2104) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2104 + sourceB2104) sourceC2104) = raw29379 := by
      apply Matrix.ext; unfold doubleCharges sourceA2104 sourceB2104 sourceC2104 raw29379; decide +kernel
    rw [ha]
    exact (canonical29379 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2104 sourceB2104 sourceC2104
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2104, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2105 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 0) (sourceB2105 + difference 0 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 0) (sourceB2105 + difference 0 3) sourceC2105) = raw29380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29380; decide +kernel
    rw [ha]
    exact (canonical29380 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 1) (sourceB2105 + difference 1 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 1) (sourceB2105 + difference 1 3) sourceC2105) = raw29381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29381; decide +kernel
    rw [ha]
    exact (canonical29381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 2) (sourceB2105 + difference 2 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 2) (sourceB2105 + difference 2 3) sourceC2105) = raw29382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29382; decide +kernel
    rw [ha]
    exact (canonical29382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 3) (sourceB2105 + difference 3 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 3) (sourceB2105 + difference 3 3) sourceC2105) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 4) (sourceB2105 + difference 4 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 4) (sourceB2105 + difference 4 3) sourceC2105) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 5) (sourceB2105 + difference 5 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 5) (sourceB2105 + difference 5 3) sourceC2105) = raw29383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29383; decide +kernel
    rw [ha]
    exact (canonical29383 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2105 + sourceB2105) sourceC2105) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2105 + sourceB2105) sourceC2105) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2105 sourceB2105 sourceC2105 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2105 sourceB2105 sourceC2105
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2105, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2106 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2106 + difference 0 3) (sourceB2106 + difference 3 0) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2106 + difference 0 3) (sourceB2106 + difference 3 0) sourceC2106) = raw29384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29384; decide +kernel
    rw [ha]
    exact (canonical29384 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2106 + difference 1 3) (sourceB2106 + difference 3 1) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2106 + difference 1 3) (sourceB2106 + difference 3 1) sourceC2106) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2106 + difference 2 3) (sourceB2106 + difference 3 2) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2846) := by
    have ha : (tripleCharges (sourceA2106 + difference 2 3) (sourceB2106 + difference 3 2) sourceC2106) = raw29385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29385; decide +kernel
    rw [ha]
    exact (canonical29385 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2106 + difference 3 3) (sourceB2106 + difference 3 3) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA2106 + difference 3 3) (sourceB2106 + difference 3 3) sourceC2106) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2106 + difference 4 3) (sourceB2106 + difference 3 4) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2335) := by
    have ha : (tripleCharges (sourceA2106 + difference 4 3) (sourceB2106 + difference 3 4) sourceC2106) = raw29386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29386; decide +kernel
    rw [ha]
    exact (canonical29386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2106 + difference 5 3) (sourceB2106 + difference 3 5) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA2106 + difference 5 3) (sourceB2106 + difference 3 5) sourceC2106) = raw29387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29387; decide +kernel
    rw [ha]
    exact (canonical29387 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2106 + sourceB2106) sourceC2106) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2106 + sourceB2106) sourceC2106) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA2106 sourceB2106 sourceC2106 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2106 sourceB2106 sourceC2106
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2106, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1744 : Integer.Sparse.reindex keyMap MixedData.row1744 = numericRow1744 := by decide +kernel

theorem numericCheck1744 (x : Master → ℝ) : Integer.Sparse.eval numericRow1744 x =
    (1 : ℝ) * reducedSource1744 x := by
  norm_num [numericRow1744, reducedSource1744, Integer.Sparse.eval, Sparse.eval, nodeValue4064, nodeValue4066, nodeValue4067, nodeValue4070, nodeValue4074, nodeValue4076, nodeValue4077, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4084, nodeValue4085, nodeValue4092]

theorem reindexCheck1745 : Integer.Sparse.reindex keyMap MixedData.row1745 = numericRow1745 := by decide +kernel

theorem numericCheck1745 (x : Master → ℝ) : Integer.Sparse.eval numericRow1745 x =
    (1 : ℝ) * reducedSource1745 x := by
  norm_num [numericRow1745, reducedSource1745, Integer.Sparse.eval, Sparse.eval, nodeValue2340, nodeValue2816, nodeValue3162, nodeValue3174, nodeValue3198, nodeValue3706, nodeValue4092]

theorem reindexCheck1746 : Integer.Sparse.reindex keyMap MixedData.row1746 = numericRow1746 := by decide +kernel

theorem numericCheck1746 (x : Master → ℝ) : Integer.Sparse.eval numericRow1746 x =
    (1 : ℝ) * reducedSource1746 x := by
  norm_num [numericRow1746, reducedSource1746, Integer.Sparse.eval, Sparse.eval, nodeValue2213, nodeValue2215, nodeValue2217, nodeValue2225, nodeValue2274, nodeValue3612, nodeValue4082]

theorem reindexCheck1747 : Integer.Sparse.reindex keyMap MixedData.row1747 = numericRow1747 := by decide +kernel

theorem numericCheck1747 (x : Master → ℝ) : Integer.Sparse.eval numericRow1747 x =
    (1 : ℝ) * reducedSource1747 x := by
  norm_num [numericRow1747, reducedSource1747, Integer.Sparse.eval, Sparse.eval, nodeValue910, nodeValue1794, nodeValue1977, nodeValue2012, nodeValue2020, nodeValue2023, nodeValue4083]

theorem reindexCheck1748 : Integer.Sparse.reindex keyMap MixedData.row1748 = numericRow1748 := by decide +kernel

theorem numericCheck1748 (x : Master → ℝ) : Integer.Sparse.eval numericRow1748 x =
    (1 : ℝ) * reducedSource1748 x := by
  norm_num [numericRow1748, reducedSource1748, Integer.Sparse.eval, Sparse.eval, nodeValue2323, nodeValue2800, nodeValue3189, nodeValue3199, nodeValue3692, nodeValue4091]

theorem reindexCheck1749 : Integer.Sparse.reindex keyMap MixedData.row1749 = numericRow1749 := by decide +kernel

theorem numericCheck1749 (x : Master → ℝ) : Integer.Sparse.eval numericRow1749 x =
    (1 : ℝ) * reducedSource1749 x := by
  norm_num [numericRow1749, reducedSource1749, Integer.Sparse.eval, Sparse.eval, nodeValue2213, nodeValue2396, nodeValue3476, nodeValue3610, nodeValue3612, nodeValue4082]

theorem reindexCheck1750 : Integer.Sparse.reindex keyMap MixedData.row1750 = numericRow1750 := by decide +kernel

theorem numericCheck1750 (x : Master → ℝ) : Integer.Sparse.eval numericRow1750 x =
    (1 : ℝ) * reducedSource1750 x := by
  norm_num [numericRow1750, reducedSource1750, Integer.Sparse.eval, Sparse.eval, nodeValue3193, nodeValue3648, nodeValue3653, nodeValue3659, nodeValue3762, nodeValue4088]

theorem reindexCheck1751 : Integer.Sparse.reindex keyMap MixedData.row1751 = numericRow1751 := by decide +kernel

theorem numericCheck1751 (x : Master → ℝ) : Integer.Sparse.eval numericRow1751 x =
    (1 : ℝ) * reducedSource1751 x := by
  norm_num [numericRow1751, reducedSource1751, Integer.Sparse.eval, Sparse.eval, nodeValue950, nodeValue1829, nodeValue1977, nodeValue2094, nodeValue2107, nodeValue2110, nodeValue4083]

theorem reindexCheck1752 : Integer.Sparse.reindex keyMap MixedData.row1752 = numericRow1752 := by decide +kernel

theorem numericCheck1752 (x : Master → ℝ) : Integer.Sparse.eval numericRow1752 x =
    (1 : ℝ) * reducedSource1752 x := by
  norm_num [numericRow1752, reducedSource1752, Integer.Sparse.eval, Sparse.eval, nodeValue2327, nodeValue2803, nodeValue3133, nodeValue3138, nodeValue3174, nodeValue3693, nodeValue4092]

theorem reindexCheck1753 : Integer.Sparse.reindex keyMap MixedData.row1753 = numericRow1753 := by decide +kernel

theorem numericCheck1753 (x : Master → ℝ) : Integer.Sparse.eval numericRow1753 x =
    (1 : ℝ) * reducedSource1753 x := by
  norm_num [numericRow1753, reducedSource1753, Integer.Sparse.eval, Sparse.eval, nodeValue2274, nodeValue2401, nodeValue3536, nodeValue3612, nodeValue3630, nodeValue3631, nodeValue4082]

theorem reindexCheck1754 : Integer.Sparse.reindex keyMap MixedData.row1754 = numericRow1754 := by decide +kernel

theorem numericCheck1754 (x : Master → ℝ) : Integer.Sparse.eval numericRow1754 x =
    (1 : ℝ) * reducedSource1754 x := by
  norm_num [numericRow1754, reducedSource1754, Integer.Sparse.eval, Sparse.eval, nodeValue2274, nodeValue2276, nodeValue2280, nodeValue2288, nodeValue3631, nodeValue4082]

theorem reindexCheck1755 : Integer.Sparse.reindex keyMap MixedData.row1755 = numericRow1755 := by decide +kernel

theorem numericCheck1755 (x : Master → ℝ) : Integer.Sparse.eval numericRow1755 x =
    (1 : ℝ) * reducedSource1755 x := by
  norm_num [numericRow1755, reducedSource1755, Integer.Sparse.eval, Sparse.eval, nodeValue3166, nodeValue3658, nodeValue3660, nodeValue3666, nodeValue3772, nodeValue4089]

theorem reindexCheck1756 : Integer.Sparse.reindex keyMap MixedData.row1756 = numericRow1756 := by decide +kernel

theorem numericCheck1756 (x : Master → ℝ) : Integer.Sparse.eval numericRow1756 x =
    (1 : ℝ) * reducedSource1756 x := by
  norm_num [numericRow1756, reducedSource1756, Integer.Sparse.eval, Sparse.eval, nodeValue2346, nodeValue2821, nodeValue3129, nodeValue3161, nodeValue3397, nodeValue4084]

theorem reindexCheck1757 : Integer.Sparse.reindex keyMap MixedData.row1757 = numericRow1757 := by decide +kernel

theorem numericCheck1757 (x : Master → ℝ) : Integer.Sparse.eval numericRow1757 x =
    (1 : ℝ) * reducedSource1757 x := by
  norm_num [numericRow1757, reducedSource1757, Integer.Sparse.eval, Sparse.eval, nodeValue3147, nodeValue3372, nodeValue3473, nodeValue3480, nodeValue3611, nodeValue4082]

theorem reindexCheck1758 : Integer.Sparse.reindex keyMap MixedData.row1758 = numericRow1758 := by decide +kernel

theorem numericCheck1758 (x : Master → ℝ) : Integer.Sparse.eval numericRow1758 x =
    (1 : ℝ) * reducedSource1758 x := by
  norm_num [numericRow1758, reducedSource1758, Integer.Sparse.eval, Sparse.eval, nodeValue1141, nodeValue2343, nodeValue2433, nodeValue2499, nodeValue2512, nodeValue2515, nodeValue4092]

theorem reindexCheck1759 : Integer.Sparse.reindex keyMap MixedData.row1759 = numericRow1759 := by decide +kernel

theorem numericCheck1759 (x : Master → ℝ) : Integer.Sparse.eval numericRow1759 x =
    (1 : ℝ) * reducedSource1759 x := by
  norm_num [numericRow1759, reducedSource1759, Integer.Sparse.eval, Sparse.eval, nodeValue2335, nodeValue2811, nodeValue2846, nodeValue2889, nodeValue2979, nodeValue3705, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1744 (mixedVector B) = 0 := by
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2089, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4064, h4066, h4067, h4070, h4074, h4076, h4077, h4080, h4081, h4082, h4084, h4085, h4092, reducedSource1744] using sourceEq2089 B hB

theorem rowSound1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1744 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1744, numericCheck1744, reducedZero1744 B hB hF, mul_zero]

theorem reducedZero1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1745 (mixedVector B) = 0 := by
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h3162 : mixedVector B (Sum.inr 3162) = Sparse.eval nodeValue3162 (mixedVector B) := by
    change mixedMoment B node3162 node3162Labels = _
    exact sound3162 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2091, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2340, h2816, h3162, h3174, h3198, h3706, h4092, reducedSource1745] using sourceEq2091 B hB

theorem rowSound1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1745 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1745, numericCheck1745, reducedZero1745 B hB hF, mul_zero]

theorem reducedZero1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1746 (mixedVector B) = 0 := by
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2092, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2213, h2215, h2217, h2225, h2274, h3612, h4082, reducedSource1746] using sourceEq2092 B hB

theorem rowSound1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1746 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1746, numericCheck1746, reducedZero1746 B hB hF, mul_zero]

theorem reducedZero1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1747 (mixedVector B) = 0 := by
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1977 : mixedVector B (Sum.inr 1977) = Sparse.eval nodeValue1977 (mixedVector B) := by
    change mixedMoment B node1977 node1977Labels = _
    exact sound1977 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2093, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h910, h1794, h1977, h2012, h2020, h2023, h4083, reducedSource1747] using sourceEq2093 B hB

theorem rowSound1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1747 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1747, numericCheck1747, reducedZero1747 B hB hF, mul_zero]

theorem reducedZero1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1748 (mixedVector B) = 0 := by
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h3189 : mixedVector B (Sum.inr 3189) = Sparse.eval nodeValue3189 (mixedVector B) := by
    change mixedMoment B node3189 node3189Labels = _
    exact sound3189 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2094, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2323, h2800, h3189, h3199, h3692, h4091, reducedSource1748] using sourceEq2094 B hB

theorem rowSound1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1748 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1748, numericCheck1748, reducedZero1748 B hB hF, mul_zero]

theorem reducedZero1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1749 (mixedVector B) = 0 := by
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3610 : mixedVector B (Sum.inr 3610) = Sparse.eval nodeValue3610 (mixedVector B) := by
    change mixedMoment B node3610 node3610Labels = _
    exact sound3610 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2095, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2213, h2396, h3476, h3610, h3612, h4082, reducedSource1749] using sourceEq2095 B hB

theorem rowSound1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1749 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1749, numericCheck1749, reducedZero1749 B hB hF, mul_zero]

theorem reducedZero1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1750 (mixedVector B) = 0 := by
  have h3193 : mixedVector B (Sum.inr 3193) = Sparse.eval nodeValue3193 (mixedVector B) := by
    change mixedMoment B node3193 node3193Labels = _
    exact sound3193 B hB hF
  have h3648 : mixedVector B (Sum.inr 3648) = Sparse.eval nodeValue3648 (mixedVector B) := by
    change mixedMoment B node3648 node3648Labels = _
    exact sound3648 B hB hF
  have h3653 : mixedVector B (Sum.inr 3653) = Sparse.eval nodeValue3653 (mixedVector B) := by
    change mixedMoment B node3653 node3653Labels = _
    exact sound3653 B hB hF
  have h3659 : mixedVector B (Sum.inr 3659) = Sparse.eval nodeValue3659 (mixedVector B) := by
    change mixedMoment B node3659 node3659Labels = _
    exact sound3659 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2097, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3193, h3648, h3653, h3659, h3762, h4088, reducedSource1750] using sourceEq2097 B hB

theorem rowSound1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1750 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1750, numericCheck1750, reducedZero1750 B hB hF, mul_zero]

theorem reducedZero1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1751 (mixedVector B) = 0 := by
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1829 : mixedVector B (Sum.inr 1829) = Sparse.eval nodeValue1829 (mixedVector B) := by
    change mixedMoment B node1829 node1829Labels = _
    exact sound1829 B hB hF
  have h1977 : mixedVector B (Sum.inr 1977) = Sparse.eval nodeValue1977 (mixedVector B) := by
    change mixedMoment B node1977 node1977Labels = _
    exact sound1977 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2098, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h950, h1829, h1977, h2094, h2107, h2110, h4083, reducedSource1751] using sourceEq2098 B hB

theorem rowSound1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1751 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1751, numericCheck1751, reducedZero1751 B hB hF, mul_zero]

theorem reducedZero1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1752 (mixedVector B) = 0 := by
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2099, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2327, h2803, h3133, h3138, h3174, h3693, h4092, reducedSource1752] using sourceEq2099 B hB

theorem rowSound1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1752 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1752, numericCheck1752, reducedZero1752 B hB hF, mul_zero]

theorem reducedZero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1753 (mixedVector B) = 0 := by
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h3536 : mixedVector B (Sum.inr 3536) = Sparse.eval nodeValue3536 (mixedVector B) := by
    change mixedMoment B node3536 node3536Labels = _
    exact sound3536 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3630 : mixedVector B (Sum.inr 3630) = Sparse.eval nodeValue3630 (mixedVector B) := by
    change mixedMoment B node3630 node3630Labels = _
    exact sound3630 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2100, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2274, h2401, h3536, h3612, h3630, h3631, h4082, reducedSource1753] using sourceEq2100 B hB

theorem rowSound1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1753 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1753, numericCheck1753, reducedZero1753 B hB hF, mul_zero]

theorem reducedZero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1754 (mixedVector B) = 0 := by
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2101, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2274, h2276, h2280, h2288, h3631, h4082, reducedSource1754] using sourceEq2101 B hB

theorem rowSound1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1754 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1754, numericCheck1754, reducedZero1754 B hB hF, mul_zero]

theorem reducedZero1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1755 (mixedVector B) = 0 := by
  have h3166 : mixedVector B (Sum.inr 3166) = Sparse.eval nodeValue3166 (mixedVector B) := by
    change mixedMoment B node3166 node3166Labels = _
    exact sound3166 B hB hF
  have h3658 : mixedVector B (Sum.inr 3658) = Sparse.eval nodeValue3658 (mixedVector B) := by
    change mixedMoment B node3658 node3658Labels = _
    exact sound3658 B hB hF
  have h3660 : mixedVector B (Sum.inr 3660) = Sparse.eval nodeValue3660 (mixedVector B) := by
    change mixedMoment B node3660 node3660Labels = _
    exact sound3660 B hB hF
  have h3666 : mixedVector B (Sum.inr 3666) = Sparse.eval nodeValue3666 (mixedVector B) := by
    change mixedMoment B node3666 node3666Labels = _
    exact sound3666 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm2102, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3166, h3658, h3660, h3666, h3772, h4089, reducedSource1755] using sourceEq2102 B hB

theorem rowSound1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1755 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1755, numericCheck1755, reducedZero1755 B hB hF, mul_zero]

theorem reducedZero1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1756 (mixedVector B) = 0 := by
  have h2346 : mixedVector B (Sum.inr 2346) = Sparse.eval nodeValue2346 (mixedVector B) := by
    change mixedMoment B node2346 node2346Labels = _
    exact sound2346 B hB hF
  have h2821 : mixedVector B (Sum.inr 2821) = Sparse.eval nodeValue2821 (mixedVector B) := by
    change mixedMoment B node2821 node2821Labels = _
    exact sound2821 B hB hF
  have h3129 : mixedVector B (Sum.inr 3129) = Sparse.eval nodeValue3129 (mixedVector B) := by
    change mixedMoment B node3129 node3129Labels = _
    exact sound3129 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2103, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2346, h2821, h3129, h3161, h3397, h4084, reducedSource1756] using sourceEq2103 B hB

theorem rowSound1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1756 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1756, numericCheck1756, reducedZero1756 B hB hF, mul_zero]

theorem reducedZero1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1757 (mixedVector B) = 0 := by
  have h3147 : mixedVector B (Sum.inr 3147) = Sparse.eval nodeValue3147 (mixedVector B) := by
    change mixedMoment B node3147 node3147Labels = _
    exact sound3147 B hB hF
  have h3372 : mixedVector B (Sum.inr 3372) = Sparse.eval nodeValue3372 (mixedVector B) := by
    change mixedMoment B node3372 node3372Labels = _
    exact sound3372 B hB hF
  have h3473 : mixedVector B (Sum.inr 3473) = Sparse.eval nodeValue3473 (mixedVector B) := by
    change mixedMoment B node3473 node3473Labels = _
    exact sound3473 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3611 : mixedVector B (Sum.inr 3611) = Sparse.eval nodeValue3611 (mixedVector B) := by
    change mixedMoment B node3611 node3611Labels = _
    exact sound3611 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2104, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3147, h3372, h3473, h3480, h3611, h4082, reducedSource1757] using sourceEq2104 B hB

theorem rowSound1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1757 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1757, numericCheck1757, reducedZero1757 B hB hF, mul_zero]

theorem reducedZero1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1758 (mixedVector B) = 0 := by
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h2343 : mixedVector B (Sum.inr 2343) = Sparse.eval nodeValue2343 (mixedVector B) := by
    change mixedMoment B node2343 node2343Labels = _
    exact sound2343 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2105, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1141, h2343, h2433, h2499, h2512, h2515, h4092, reducedSource1758] using sourceEq2105 B hB

theorem rowSound1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1758 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1758, numericCheck1758, reducedZero1758 B hB hF, mul_zero]

theorem reducedZero1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1759 (mixedVector B) = 0 := by
  have h2335 : mixedVector B (Sum.inr 2335) = Sparse.eval nodeValue2335 (mixedVector B) := by
    change mixedMoment B node2335 node2335Labels = _
    exact sound2335 B hB hF
  have h2811 : mixedVector B (Sum.inr 2811) = Sparse.eval nodeValue2811 (mixedVector B) := by
    change mixedMoment B node2811 node2811Labels = _
    exact sound2811 B hB hF
  have h2846 : mixedVector B (Sum.inr 2846) = Sparse.eval nodeValue2846 (mixedVector B) := by
    change mixedMoment B node2846 node2846Labels = _
    exact sound2846 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3705 : mixedVector B (Sum.inr 3705) = Sparse.eval nodeValue3705 (mixedVector B) := by
    change mixedMoment B node3705 node3705Labels = _
    exact sound3705 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2106, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2335, h2811, h2846, h2889, h2979, h3705, h4092, reducedSource1759] using sourceEq2106 B hB

theorem rowSound1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1759 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1759, numericCheck1759, reducedZero1759 B hB hF, mul_zero]

theorem sourceRowsAt1744 : MixedData.sourceRows (1744 : Fin 2425) =
    MixedData.row1744 := by decide +kernel

theorem sourceRowsAt1745 : MixedData.sourceRows (1745 : Fin 2425) =
    MixedData.row1745 := by decide +kernel

theorem sourceRowsAt1746 : MixedData.sourceRows (1746 : Fin 2425) =
    MixedData.row1746 := by decide +kernel

theorem sourceRowsAt1747 : MixedData.sourceRows (1747 : Fin 2425) =
    MixedData.row1747 := by decide +kernel

theorem sourceRowsAt1748 : MixedData.sourceRows (1748 : Fin 2425) =
    MixedData.row1748 := by decide +kernel

theorem sourceRowsAt1749 : MixedData.sourceRows (1749 : Fin 2425) =
    MixedData.row1749 := by decide +kernel

theorem sourceRowsAt1750 : MixedData.sourceRows (1750 : Fin 2425) =
    MixedData.row1750 := by decide +kernel

theorem sourceRowsAt1751 : MixedData.sourceRows (1751 : Fin 2425) =
    MixedData.row1751 := by decide +kernel

theorem sourceRowsAt1752 : MixedData.sourceRows (1752 : Fin 2425) =
    MixedData.row1752 := by decide +kernel

theorem sourceRowsAt1753 : MixedData.sourceRows (1753 : Fin 2425) =
    MixedData.row1753 := by decide +kernel

theorem sourceRowsAt1754 : MixedData.sourceRows (1754 : Fin 2425) =
    MixedData.row1754 := by decide +kernel

theorem sourceRowsAt1755 : MixedData.sourceRows (1755 : Fin 2425) =
    MixedData.row1755 := by decide +kernel

theorem sourceRowsAt1756 : MixedData.sourceRows (1756 : Fin 2425) =
    MixedData.row1756 := by decide +kernel

theorem sourceRowsAt1757 : MixedData.sourceRows (1757 : Fin 2425) =
    MixedData.row1757 := by decide +kernel

theorem sourceRowsAt1758 : MixedData.sourceRows (1758 : Fin 2425) =
    MixedData.row1758 := by decide +kernel

theorem sourceRowsAt1759 : MixedData.sourceRows (1759 : Fin 2425) =
    MixedData.row1759 := by decide +kernel

theorem chunkSound109_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 109) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1744 ∨ k.val = 1745 ∨ k.val = 1746 ∨ k.val = 1747 ∨ k.val = 1748 ∨ k.val = 1749 ∨ k.val = 1750 ∨ k.val = 1751 ∨ k.val = 1752 ∨ k.val = 1753 ∨ k.val = 1754 ∨ k.val = 1755 ∨ k.val = 1756 ∨ k.val = 1757 ∨ k.val = 1758 ∨ k.val = 1759 := by omega
  rcases heq with h1744 | h1745 | h1746 | h1747 | h1748 | h1749 | h1750 | h1751 | h1752 | h1753 | h1754 | h1755 | h1756 | h1757 | h1758 | h1759
  · have he : k = (1744 : Fin 2425) := Fin.ext h1744
    subst k
    rw [sourceRowsAt1744]
    exact rowSound1744 B hB hF
  · have he : k = (1745 : Fin 2425) := Fin.ext h1745
    subst k
    rw [sourceRowsAt1745]
    exact rowSound1745 B hB hF
  · have he : k = (1746 : Fin 2425) := Fin.ext h1746
    subst k
    rw [sourceRowsAt1746]
    exact rowSound1746 B hB hF
  · have he : k = (1747 : Fin 2425) := Fin.ext h1747
    subst k
    rw [sourceRowsAt1747]
    exact rowSound1747 B hB hF
  · have he : k = (1748 : Fin 2425) := Fin.ext h1748
    subst k
    rw [sourceRowsAt1748]
    exact rowSound1748 B hB hF
  · have he : k = (1749 : Fin 2425) := Fin.ext h1749
    subst k
    rw [sourceRowsAt1749]
    exact rowSound1749 B hB hF
  · have he : k = (1750 : Fin 2425) := Fin.ext h1750
    subst k
    rw [sourceRowsAt1750]
    exact rowSound1750 B hB hF
  · have he : k = (1751 : Fin 2425) := Fin.ext h1751
    subst k
    rw [sourceRowsAt1751]
    exact rowSound1751 B hB hF
  · have he : k = (1752 : Fin 2425) := Fin.ext h1752
    subst k
    rw [sourceRowsAt1752]
    exact rowSound1752 B hB hF
  · have he : k = (1753 : Fin 2425) := Fin.ext h1753
    subst k
    rw [sourceRowsAt1753]
    exact rowSound1753 B hB hF
  · have he : k = (1754 : Fin 2425) := Fin.ext h1754
    subst k
    rw [sourceRowsAt1754]
    exact rowSound1754 B hB hF
  · have he : k = (1755 : Fin 2425) := Fin.ext h1755
    subst k
    rw [sourceRowsAt1755]
    exact rowSound1755 B hB hF
  · have he : k = (1756 : Fin 2425) := Fin.ext h1756
    subst k
    rw [sourceRowsAt1756]
    exact rowSound1756 B hB hF
  · have he : k = (1757 : Fin 2425) := Fin.ext h1757
    subst k
    rw [sourceRowsAt1757]
    exact rowSound1757 B hB hF
  · have he : k = (1758 : Fin 2425) := Fin.ext h1758
    subst k
    rw [sourceRowsAt1758]
    exact rowSound1758 B hB hF
  · have he : k = (1759 : Fin 2425) := Fin.ext h1759
    subst k
    rw [sourceRowsAt1759]
    exact rowSound1759 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e_oai
