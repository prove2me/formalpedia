-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:01:44.667572+00:00
-- url     : https://prove2.me/submissions/c09810d8-6332-4d23-9012-dd9a45520606

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2988_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2996_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3089_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3982_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

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

end MUB6.Certificate.MixedSemantics

end

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

theorem canonical11574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11574 raw11574Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw11574 raw11574Labels = mixedMoment B raw11574step0 raw11574step0Labels := by
      have ha : raw11574step0 = (fun i j => raw11574 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11574step0 raw11574; decide +kernel
      have hl : raw11574step0Labels = raw11574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11574 raw11574Labels permutation640 permutation6
    _ = mixedMoment B node3977 node3977Labels := by rfl

theorem canonical11575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11575 raw11575Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw11575 raw11575Labels = mixedMoment B raw11575step0 raw11575step0Labels := by
      have ha : raw11575step0 = (fun i j => raw11575 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11575step0 raw11575; decide +kernel
      have hl : raw11575step0Labels = raw11575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11575 raw11575Labels permutation640 permutation6
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical11576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11576 raw11576Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw11576 raw11576Labels = mixedMoment B raw11576step0 raw11576step0Labels := by
      have hz : ∀ j, raw11576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11576step0 = (fun i j => raw11576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11576step0 raw11576; decide +kernel
      have hl : raw11576step0Labels = raw11576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11576 raw11576Labels permutation434 hz
    mixedMoment B raw11576step0 raw11576step0Labels = mixedMoment B raw11576step1 raw11576step1Labels := by
      have ha : raw11576step1 = (fun i j => raw11576step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11576step1 raw11576step0; decide +kernel
      have hl : raw11576step1Labels = raw11576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11576step0 raw11576step0Labels permutation145 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical11577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11577 raw11577Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw11577 raw11577Labels = mixedMoment B raw11577step0 raw11577step0Labels := by
      have hz : ∀ j, raw11577 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11577step0 = (fun i j => raw11577 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11577step0 raw11577; decide +kernel
      have hl : raw11577step0Labels = raw11577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11577 raw11577Labels permutation520 hz
    mixedMoment B raw11577step0 raw11577step0Labels = mixedMoment B raw11577step1 raw11577step1Labels := by
      have ha : raw11577step1 = (fun i j => raw11577step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11577step1 raw11577step0; decide +kernel
      have hl : raw11577step1Labels = raw11577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11577step0 raw11577step0Labels permutation145 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical11578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11578 raw11578Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11578 raw11578Labels = mixedMoment B raw11578step0 raw11578step0Labels := by
      have ha : raw11578step0 = (fun i j => raw11578 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11578step0 raw11578; decide +kernel
      have hl : raw11578step0Labels = raw11578Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11578 raw11578Labels permutation640 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical11579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11579 raw11579Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw11579 raw11579Labels = mixedMoment B raw11579step0 raw11579step0Labels := by
      have ha : raw11579step0 = (fun i j => raw11579 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11579step0 raw11579; decide +kernel
      have hl : raw11579step0Labels = raw11579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11579 raw11579Labels permutation197 permutation3
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical11580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11580 raw11580Labels = mixedMoment B node2874 node2874Labels := by
  calc
    mixedMoment B raw11580 raw11580Labels = mixedMoment B raw11580step0 raw11580step0Labels := by
      have ha : raw11580step0 = (fun i j => raw11580 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11580step0 raw11580; decide +kernel
      have hl : raw11580step0Labels = raw11580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11580 raw11580Labels permutation197 permutation3
    _ = mixedMoment B node2874 node2874Labels := by rfl

theorem canonical11581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11581 raw11581Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11581 raw11581Labels = mixedMoment B raw11581step0 raw11581step0Labels := by
      have hz : ∀ j, raw11581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11581step0 = (fun i j => raw11581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11581step0 raw11581; decide +kernel
      have hl : raw11581step0Labels = raw11581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11581 raw11581Labels permutation434 hz
    mixedMoment B raw11581step0 raw11581step0Labels = mixedMoment B raw11581step1 raw11581step1Labels := by
      have ha : raw11581step1 = (fun i j => raw11581step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11581step1 raw11581step0; decide +kernel
      have hl : raw11581step1Labels = raw11581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11581step0 raw11581step0Labels permutation43 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical11582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11582 raw11582Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11582 raw11582Labels = mixedMoment B raw11582step0 raw11582step0Labels := by
      have hz : ∀ j, raw11582 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11582step0 = (fun i j => raw11582 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11582step0 raw11582; decide +kernel
      have hl : raw11582step0Labels = raw11582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11582 raw11582Labels permutation520 hz
    mixedMoment B raw11582step0 raw11582step0Labels = mixedMoment B raw11582step1 raw11582step1Labels := by
      have ha : raw11582step1 = (fun i j => raw11582step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11582step1 raw11582step0; decide +kernel
      have hl : raw11582step1Labels = raw11582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11582step0 raw11582step0Labels permutation43 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical11583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11583 raw11583Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw11583 raw11583Labels = mixedMoment B raw11583step0 raw11583step0Labels := by
      have ha : raw11583step0 = (fun i j => raw11583 (permutation255 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11583step0 raw11583; decide +kernel
      have hl : raw11583step0Labels = raw11583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11583 raw11583Labels permutation255 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical11584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11584 raw11584Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw11584 raw11584Labels = mixedMoment B raw11584step0 raw11584step0Labels := by
      have ha : raw11584step0 = (fun i j => raw11584 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11584step0 raw11584; decide +kernel
      have hl : raw11584step0Labels = raw11584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11584 raw11584Labels permutation170 permutation3
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical11585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11585 raw11585Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw11585 raw11585Labels = mixedMoment B raw11585step0 raw11585step0Labels := by
      have ha : raw11585step0 = (fun i j => raw11585 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11585step0 raw11585; decide +kernel
      have hl : raw11585step0Labels = raw11585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11585 raw11585Labels permutation170 permutation3
    _ = mixedMoment B node2996 node2996Labels := by rfl

theorem canonical11586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11586 raw11586Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11586 raw11586Labels = mixedMoment B raw11586step0 raw11586step0Labels := by
      have hz : ∀ j, raw11586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11586step0 = (fun i j => raw11586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11586step0 raw11586; decide +kernel
      have hl : raw11586step0Labels = raw11586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11586 raw11586Labels permutation434 hz
    mixedMoment B raw11586step0 raw11586step0Labels = mixedMoment B raw11586step1 raw11586step1Labels := by
      have ha : raw11586step1 = (fun i j => raw11586step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11586step1 raw11586step0; decide +kernel
      have hl : raw11586step1Labels = raw11586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11586step0 raw11586step0Labels permutation36 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11587 raw11587Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11587 raw11587Labels = mixedMoment B raw11587step0 raw11587step0Labels := by
      have hz : ∀ j, raw11587 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11587step0 = (fun i j => raw11587 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11587step0 raw11587; decide +kernel
      have hl : raw11587step0Labels = raw11587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11587 raw11587Labels permutation520 hz
    mixedMoment B raw11587step0 raw11587step0Labels = mixedMoment B raw11587step1 raw11587step1Labels := by
      have ha : raw11587step1 = (fun i j => raw11587step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11587step1 raw11587step0; decide +kernel
      have hl : raw11587step1Labels = raw11587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11587step0 raw11587step0Labels permutation36 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11588 raw11588Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11588 raw11588Labels = mixedMoment B raw11588step0 raw11588step0Labels := by
      have ha : raw11588step0 = (fun i j => raw11588 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11588step0 raw11588; decide +kernel
      have hl : raw11588step0Labels = raw11588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11588 raw11588Labels permutation246 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11589 raw11589Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw11589 raw11589Labels = mixedMoment B raw11589step0 raw11589step0Labels := by
      have ha : raw11589step0 = (fun i j => raw11589 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11589step0 raw11589; decide +kernel
      have hl : raw11589step0Labels = raw11589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11589 raw11589Labels permutation181 permutation3
    _ = mixedMoment B node1210 node1210Labels := by rfl

theorem canonical11590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11590 raw11590Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw11590 raw11590Labels = mixedMoment B raw11590step0 raw11590step0Labels := by
      have ha : raw11590step0 = (fun i j => raw11590 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11590step0 raw11590; decide +kernel
      have hl : raw11590step0Labels = raw11590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11590 raw11590Labels permutation157 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical11591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11591 raw11591Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw11591 raw11591Labels = mixedMoment B raw11591step0 raw11591step0Labels := by
      have ha : raw11591step0 = (fun i j => raw11591 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11591step0 raw11591; decide +kernel
      have hl : raw11591step0Labels = raw11591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11591 raw11591Labels permutation181 permutation3
    _ = mixedMoment B node2860 node2860Labels := by rfl

theorem canonical11592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11592 raw11592Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw11592 raw11592Labels = mixedMoment B raw11592step0 raw11592step0Labels := by
      have hz : ∀ j, raw11592 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11592step0 = (fun i j => raw11592 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11592step0 raw11592; decide +kernel
      have hl : raw11592step0Labels = raw11592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11592 raw11592Labels permutation520 hz
    mixedMoment B raw11592step0 raw11592step0Labels = mixedMoment B raw11592step1 raw11592step1Labels := by
      have ha : raw11592step1 = (fun i j => raw11592step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11592step1 raw11592step0; decide +kernel
      have hl : raw11592step1Labels = raw11592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11592step0 raw11592step0Labels permutation39 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical11593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11593 raw11593Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11593 raw11593Labels = mixedMoment B raw11593step0 raw11593step0Labels := by
      have ha : raw11593step0 = (fun i j => raw11593 (permutation253 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11593step0 raw11593; decide +kernel
      have hl : raw11593step0Labels = raw11593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11593 raw11593Labels permutation253 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical11594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11594 raw11594Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw11594 raw11594Labels = mixedMoment B raw11594step0 raw11594step0Labels := by
      have ha : raw11594step0 = (fun i j => raw11594 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11594step0 raw11594; decide +kernel
      have hl : raw11594step0Labels = raw11594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11594 raw11594Labels permutation180 permutation3
    _ = mixedMoment B node1210 node1210Labels := by rfl

theorem canonical11595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11595 raw11595Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw11595 raw11595Labels = mixedMoment B raw11595step0 raw11595step0Labels := by
      have ha : raw11595step0 = (fun i j => raw11595 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11595step0 raw11595; decide +kernel
      have hl : raw11595step0Labels = raw11595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11595 raw11595Labels permutation156 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical11596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11596 raw11596Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw11596 raw11596Labels = mixedMoment B raw11596step0 raw11596step0Labels := by
      have ha : raw11596step0 = (fun i j => raw11596 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11596step0 raw11596; decide +kernel
      have hl : raw11596step0Labels = raw11596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11596 raw11596Labels permutation180 permutation3
    _ = mixedMoment B node2860 node2860Labels := by rfl

theorem canonical11597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11597 raw11597Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw11597 raw11597Labels = mixedMoment B raw11597step0 raw11597step0Labels := by
      have hz : ∀ j, raw11597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11597step0 = (fun i j => raw11597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11597step0 raw11597; decide +kernel
      have hl : raw11597step0Labels = raw11597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11597 raw11597Labels permutation434 hz
    mixedMoment B raw11597step0 raw11597step0Labels = mixedMoment B raw11597step1 raw11597step1Labels := by
      have ha : raw11597step1 = (fun i j => raw11597step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11597step1 raw11597step0; decide +kernel
      have hl : raw11597step1Labels = raw11597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11597step0 raw11597step0Labels permutation39 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical11598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11598 raw11598Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11598 raw11598Labels = mixedMoment B raw11598step0 raw11598step0Labels := by
      have ha : raw11598step0 = (fun i j => raw11598 (permutation252 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11598step0 raw11598; decide +kernel
      have hl : raw11598step0Labels = raw11598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11598 raw11598Labels permutation252 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical11599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11599 raw11599Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw11599 raw11599Labels = mixedMoment B raw11599step0 raw11599step0Labels := by
      have ha : raw11599step0 = (fun i j => raw11599 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11599step0 raw11599; decide +kernel
      have hl : raw11599step0Labels = raw11599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11599 raw11599Labels permutation176 permutation3
    _ = mixedMoment B node1216 node1216Labels := by rfl

theorem canonical11600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11600 raw11600Labels = mixedMoment B node2988 node2988Labels := by
  calc
    mixedMoment B raw11600 raw11600Labels = mixedMoment B raw11600step0 raw11600step0Labels := by
      have ha : raw11600step0 = (fun i j => raw11600 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11600step0 raw11600; decide +kernel
      have hl : raw11600step0Labels = raw11600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11600 raw11600Labels permutation152 permutation3
    _ = mixedMoment B node2988 node2988Labels := by rfl

theorem canonical11601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11601 raw11601Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw11601 raw11601Labels = mixedMoment B raw11601step0 raw11601step0Labels := by
      have ha : raw11601step0 = (fun i j => raw11601 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11601step0 raw11601; decide +kernel
      have hl : raw11601step0Labels = raw11601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11601 raw11601Labels permutation176 permutation3
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical11602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11602 raw11602Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw11602 raw11602Labels = mixedMoment B raw11602step0 raw11602step0Labels := by
      have hz : ∀ j, raw11602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11602step0 = (fun i j => raw11602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11602step0 raw11602; decide +kernel
      have hl : raw11602step0Labels = raw11602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11602 raw11602Labels permutation434 hz
    mixedMoment B raw11602step0 raw11602step0Labels = mixedMoment B raw11602step1 raw11602step1Labels := by
      have ha : raw11602step1 = (fun i j => raw11602step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11602step1 raw11602step0; decide +kernel
      have hl : raw11602step1Labels = raw11602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11602step0 raw11602step0Labels permutation38 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

theorem canonical11603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11603 raw11603Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw11603 raw11603Labels = mixedMoment B raw11603step0 raw11603step0Labels := by
      have hz : ∀ j, raw11603 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11603step0 = (fun i j => raw11603 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11603step0 raw11603; decide +kernel
      have hl : raw11603step0Labels = raw11603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11603 raw11603Labels permutation520 hz
    mixedMoment B raw11603step0 raw11603step0Labels = mixedMoment B raw11603step1 raw11603step1Labels := by
      have ha : raw11603step1 = (fun i j => raw11603step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11603step1 raw11603step0; decide +kernel
      have hl : raw11603step1Labels = raw11603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11603step0 raw11603step0Labels permutation38 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

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

theorem sound1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1210 node1210Labels = Sparse.eval nodeValue1210 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1210) = mixedMoment B node1210 node1210Labels := rfl
  simpa [nodeValue1210, Sparse.eval] using hc.symm

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

theorem sound1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1216 node1216Labels = Sparse.eval nodeValue1216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1216) = mixedMoment B node1216 node1216Labels := rfl
  simpa [nodeValue1216, Sparse.eval] using hc.symm

theorem sound1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1228 node1228Labels = Sparse.eval nodeValue1228 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1228) = mixedMoment B node1228 node1228Labels := rfl
  simpa [nodeValue1228, Sparse.eval] using hc.symm

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

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

theorem sound2860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2860 node2860Labels = Sparse.eval nodeValue2860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2860) = mixedMoment B node2860 node2860Labels := rfl
  simpa [nodeValue2860, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

theorem sound2874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2874 node2874Labels = Sparse.eval nodeValue2874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2874) = mixedMoment B node2874 node2874Labels := rfl
  simpa [nodeValue2874, Sparse.eval] using hc.symm

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

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

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

theorem sound3016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3016 node3016Labels = Sparse.eval nodeValue3016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3016) = mixedMoment B node3016 node3016Labels := rfl
  simpa [nodeValue3016, Sparse.eval] using hc.symm

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

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

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

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

theorem sound3954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3954 node3954Labels = Sparse.eval nodeValue3954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3954) = mixedMoment B node3954 node3954Labels := rfl
  simpa [nodeValue3954, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm683 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA683 + difference 0 1) (sourceB683 + difference 1 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA683 + difference 0 1) (sourceB683 + difference 1 0) sourceC683) = raw11574 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11574; decide +kernel
    rw [ha]
    exact (canonical11574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA683 + difference 0 2) (sourceB683 + difference 2 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA683 + difference 0 2) (sourceB683 + difference 2 0) sourceC683) = raw11575 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11575; decide +kernel
    rw [ha]
    exact (canonical11575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA683 + difference 0 3) (sourceB683 + difference 3 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA683 + difference 0 3) (sourceB683 + difference 3 0) sourceC683) = raw11576 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11576; decide +kernel
    rw [ha]
    exact (canonical11576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA683 + difference 0 4) (sourceB683 + difference 4 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA683 + difference 0 4) (sourceB683 + difference 4 0) sourceC683) = raw11577 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11577; decide +kernel
    rw [ha]
    exact (canonical11577 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA683 + difference 0 5) (sourceB683 + difference 5 0) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA683 + difference 0 5) (sourceB683 + difference 5 0) sourceC683) = raw11578 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11578; decide +kernel
    rw [ha]
    exact (canonical11578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA683 + difference 1 0) (sourceB683 + difference 0 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA683 + difference 1 0) (sourceB683 + difference 0 1) sourceC683) = raw11579 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11579; decide +kernel
    rw [ha]
    exact (canonical11579 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA683 + difference 1 2) (sourceB683 + difference 2 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2874) := by
    have ha : (tripleCharges (sourceA683 + difference 1 2) (sourceB683 + difference 2 1) sourceC683) = raw11580 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11580; decide +kernel
    rw [ha]
    exact (canonical11580 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA683 + difference 1 3) (sourceB683 + difference 3 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA683 + difference 1 3) (sourceB683 + difference 3 1) sourceC683) = raw11581 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11581; decide +kernel
    rw [ha]
    exact (canonical11581 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA683 + difference 1 4) (sourceB683 + difference 4 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA683 + difference 1 4) (sourceB683 + difference 4 1) sourceC683) = raw11582 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11582; decide +kernel
    rw [ha]
    exact (canonical11582 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA683 + difference 1 5) (sourceB683 + difference 5 1) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA683 + difference 1 5) (sourceB683 + difference 5 1) sourceC683) = raw11583 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11583; decide +kernel
    rw [ha]
    exact (canonical11583 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA683 + difference 2 0) (sourceB683 + difference 0 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA683 + difference 2 0) (sourceB683 + difference 0 2) sourceC683) = raw11584 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11584; decide +kernel
    rw [ha]
    exact (canonical11584 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA683 + difference 2 1) (sourceB683 + difference 1 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2996) := by
    have ha : (tripleCharges (sourceA683 + difference 2 1) (sourceB683 + difference 1 2) sourceC683) = raw11585 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11585; decide +kernel
    rw [ha]
    exact (canonical11585 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA683 + difference 2 3) (sourceB683 + difference 3 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA683 + difference 2 3) (sourceB683 + difference 3 2) sourceC683) = raw11586 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11586; decide +kernel
    rw [ha]
    exact (canonical11586 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA683 + difference 2 4) (sourceB683 + difference 4 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA683 + difference 2 4) (sourceB683 + difference 4 2) sourceC683) = raw11587 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11587; decide +kernel
    rw [ha]
    exact (canonical11587 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA683 + difference 2 5) (sourceB683 + difference 5 2) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA683 + difference 2 5) (sourceB683 + difference 5 2) sourceC683) = raw11588 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11588; decide +kernel
    rw [ha]
    exact (canonical11588 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA683 + difference 3 0) (sourceB683 + difference 0 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA683 + difference 3 0) (sourceB683 + difference 0 3) sourceC683) = raw11589 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11589; decide +kernel
    rw [ha]
    exact (canonical11589 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA683 + difference 3 1) (sourceB683 + difference 1 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA683 + difference 3 1) (sourceB683 + difference 1 3) sourceC683) = raw11590 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11590; decide +kernel
    rw [ha]
    exact (canonical11590 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA683 + difference 3 2) (sourceB683 + difference 2 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA683 + difference 3 2) (sourceB683 + difference 2 3) sourceC683) = raw11591 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11591; decide +kernel
    rw [ha]
    exact (canonical11591 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA683 + difference 3 4) (sourceB683 + difference 4 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA683 + difference 3 4) (sourceB683 + difference 4 3) sourceC683) = raw11592 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11592; decide +kernel
    rw [ha]
    exact (canonical11592 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA683 + difference 3 5) (sourceB683 + difference 5 3) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA683 + difference 3 5) (sourceB683 + difference 5 3) sourceC683) = raw11593 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11593; decide +kernel
    rw [ha]
    exact (canonical11593 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA683 + difference 4 0) (sourceB683 + difference 0 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA683 + difference 4 0) (sourceB683 + difference 0 4) sourceC683) = raw11594 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11594; decide +kernel
    rw [ha]
    exact (canonical11594 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA683 + difference 4 1) (sourceB683 + difference 1 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA683 + difference 4 1) (sourceB683 + difference 1 4) sourceC683) = raw11595 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11595; decide +kernel
    rw [ha]
    exact (canonical11595 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA683 + difference 4 2) (sourceB683 + difference 2 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA683 + difference 4 2) (sourceB683 + difference 2 4) sourceC683) = raw11596 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11596; decide +kernel
    rw [ha]
    exact (canonical11596 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA683 + difference 4 3) (sourceB683 + difference 3 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA683 + difference 4 3) (sourceB683 + difference 3 4) sourceC683) = raw11597 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11597; decide +kernel
    rw [ha]
    exact (canonical11597 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA683 + difference 4 5) (sourceB683 + difference 5 4) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA683 + difference 4 5) (sourceB683 + difference 5 4) sourceC683) = raw11598 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11598; decide +kernel
    rw [ha]
    exact (canonical11598 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA683 + difference 5 0) (sourceB683 + difference 0 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA683 + difference 5 0) (sourceB683 + difference 0 5) sourceC683) = raw11599 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11599; decide +kernel
    rw [ha]
    exact (canonical11599 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA683 + difference 5 1) (sourceB683 + difference 1 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2988) := by
    have ha : (tripleCharges (sourceA683 + difference 5 1) (sourceB683 + difference 1 5) sourceC683) = raw11600 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11600; decide +kernel
    rw [ha]
    exact (canonical11600 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA683 + difference 5 2) (sourceB683 + difference 2 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA683 + difference 5 2) (sourceB683 + difference 2 5) sourceC683) = raw11601 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11601; decide +kernel
    rw [ha]
    exact (canonical11601 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA683 + difference 5 3) (sourceB683 + difference 3 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA683 + difference 5 3) (sourceB683 + difference 3 5) sourceC683) = raw11602 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11602; decide +kernel
    rw [ha]
    exact (canonical11602 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA683 + difference 5 4) (sourceB683 + difference 4 5) sourceC683) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA683 + difference 5 4) (sourceB683 + difference 4 5) sourceC683) = raw11603 := by
      apply Matrix.ext; unfold tripleCharges sourceA683 sourceB683 sourceC683 difference raw11603; decide +kernel
    rw [ha]
    exact (canonical11603 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA683 sourceB683 sourceC683
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm683, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck591 : Integer.Sparse.reindex keyMap MixedData.row591 = numericRow591 := by decide +kernel

theorem numericCheck591 (x : Master → ℝ) : Integer.Sparse.eval numericRow591 x =
    (8640 : ℝ) * reducedSource591 x := by
  norm_num [numericRow591, reducedSource591, Integer.Sparse.eval, Sparse.eval, nodeValue1210, nodeValue1216, nodeValue1228, nodeValue1260, nodeValue2860, nodeValue2864, nodeValue2874, nodeValue2984, nodeValue2988, nodeValue2996, nodeValue3016, nodeValue3023, nodeValue3037, nodeValue3086, nodeValue3089, nodeValue3097, nodeValue3109, nodeValue3801, nodeValue3954, nodeValue3977, nodeValue3982] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource591 (mixedVector B) = 0 := by
  have h1210 : mixedVector B (Sum.inr 1210) = Sparse.eval nodeValue1210 (mixedVector B) := by
    change mixedMoment B node1210 node1210Labels = _
    exact sound1210 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2860 : mixedVector B (Sum.inr 2860) = Sparse.eval nodeValue2860 (mixedVector B) := by
    change mixedMoment B node2860 node2860Labels = _
    exact sound2860 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h2874 : mixedVector B (Sum.inr 2874) = Sparse.eval nodeValue2874 (mixedVector B) := by
    change mixedMoment B node2874 node2874Labels = _
    exact sound2874 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h2988 : mixedVector B (Sum.inr 2988) = Sparse.eval nodeValue2988 (mixedVector B) := by
    change mixedMoment B node2988 node2988Labels = _
    exact sound2988_e B hB hF
  have h2996 : mixedVector B (Sum.inr 2996) = Sparse.eval nodeValue2996 (mixedVector B) := by
    change mixedMoment B node2996 node2996Labels = _
    exact sound2996_e B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089_e B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109_e B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977_e B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982_e B hB hF
  simpa only [sourceForm683, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1210, h1216, h1228, h1260, h2860, h2864, h2874, h2984, h2988, h2996, h3016, h3023, h3037, h3086, h3089, h3097, h3109, h3801, h3954, h3977, h3982, reducedSource591] using sourceEq683 B hB

theorem rowSound591_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row591 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck591, numericCheck591, reducedZero591 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e_oai
