-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:03:24.765195+00:00
-- url     : https://prove2.me/submissions/f7c24af2-c214-4dcf-89d7-832664c3ce3a

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2996_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3847_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11802 raw11802Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11802 raw11802Labels = mixedMoment B raw11802step0 raw11802step0Labels := by
      have ha : raw11802step0 = (fun i j => raw11802 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11802step0 raw11802; decide +kernel
      have hl : raw11802step0Labels = raw11802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11802 raw11802Labels permutation427 permutation6
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical11803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11803 raw11803Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11803 raw11803Labels = mixedMoment B raw11803step0 raw11803step0Labels := by
      have ha : raw11803step0 = (fun i j => raw11803 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11803step0 raw11803; decide +kernel
      have hl : raw11803step0Labels = raw11803Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11803 raw11803Labels permutation427 permutation6
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical11804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11804 raw11804Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11804 raw11804Labels = mixedMoment B raw11804step0 raw11804step0Labels := by
      have hz : ∀ j, raw11804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11804step0 = (fun i j => raw11804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11804step0 raw11804; decide +kernel
      have hl : raw11804step0Labels = raw11804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11804 raw11804Labels permutation434 hz
    mixedMoment B raw11804step0 raw11804step0Labels = mixedMoment B raw11804step1 raw11804step1Labels := by
      have ha : raw11804step1 = (fun i j => raw11804step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11804step1 raw11804step0; decide +kernel
      have hl : raw11804step1Labels = raw11804step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11804step0 raw11804step0Labels permutation103 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical11805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11805 raw11805Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11805 raw11805Labels = mixedMoment B raw11805step0 raw11805step0Labels := by
      have hz : ∀ j, raw11805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11805step0 = (fun i j => raw11805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11805step0 raw11805; decide +kernel
      have hl : raw11805step0Labels = raw11805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11805 raw11805Labels permutation520 hz
    mixedMoment B raw11805step0 raw11805step0Labels = mixedMoment B raw11805step1 raw11805step1Labels := by
      have ha : raw11805step1 = (fun i j => raw11805step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11805step1 raw11805step0; decide +kernel
      have hl : raw11805step1Labels = raw11805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11805step0 raw11805step0Labels permutation103 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical11806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11806 raw11806Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11806 raw11806Labels = mixedMoment B raw11806step0 raw11806step0Labels := by
      have ha : raw11806step0 = (fun i j => raw11806 (permutation427 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11806step0 raw11806; decide +kernel
      have hl : raw11806step0Labels = raw11806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11806 raw11806Labels permutation427 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical11807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11807 raw11807Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw11807 raw11807Labels = mixedMoment B raw11807step0 raw11807step0Labels := by
      have ha : raw11807step0 = (fun i j => raw11807 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11807step0 raw11807; decide +kernel
      have hl : raw11807step0Labels = raw11807Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11807 raw11807Labels permutation197 permutation3
    _ = mixedMoment B node1183 node1183Labels := by rfl

theorem canonical11808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11808 raw11808Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw11808 raw11808Labels = mixedMoment B raw11808step0 raw11808step0Labels := by
      have ha : raw11808step0 = (fun i j => raw11808 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11808step0 raw11808; decide +kernel
      have hl : raw11808step0Labels = raw11808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11808 raw11808Labels permutation197 permutation3
    _ = mixedMoment B node2836 node2836Labels := by rfl

theorem canonical11809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11809 raw11809Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw11809 raw11809Labels = mixedMoment B raw11809step0 raw11809step0Labels := by
      have hz : ∀ j, raw11809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11809step0 = (fun i j => raw11809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11809step0 raw11809; decide +kernel
      have hl : raw11809step0Labels = raw11809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11809 raw11809Labels permutation434 hz
    mixedMoment B raw11809step0 raw11809step0Labels = mixedMoment B raw11809step1 raw11809step1Labels := by
      have ha : raw11809step1 = (fun i j => raw11809step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11809step1 raw11809step0; decide +kernel
      have hl : raw11809step1Labels = raw11809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11809step0 raw11809step0Labels permutation43 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical11810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11810 raw11810Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw11810 raw11810Labels = mixedMoment B raw11810step0 raw11810step0Labels := by
      have hz : ∀ j, raw11810 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11810step0 = (fun i j => raw11810 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11810step0 raw11810; decide +kernel
      have hl : raw11810step0Labels = raw11810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11810 raw11810Labels permutation520 hz
    mixedMoment B raw11810step0 raw11810step0Labels = mixedMoment B raw11810step1 raw11810step1Labels := by
      have ha : raw11810step1 = (fun i j => raw11810step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11810step1 raw11810step0; decide +kernel
      have hl : raw11810step1Labels = raw11810step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11810step0 raw11810step0Labels permutation43 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical11811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11811 raw11811Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw11811 raw11811Labels = mixedMoment B raw11811step0 raw11811step0Labels := by
      have ha : raw11811step0 = (fun i j => raw11811 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11811step0 raw11811; decide +kernel
      have hl : raw11811step0Labels = raw11811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11811 raw11811Labels permutation197 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical11812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11812 raw11812Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw11812 raw11812Labels = mixedMoment B raw11812step0 raw11812step0Labels := by
      have ha : raw11812step0 = (fun i j => raw11812 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11812step0 raw11812; decide +kernel
      have hl : raw11812step0Labels = raw11812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11812 raw11812Labels permutation156 permutation3
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical11813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11813 raw11813Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw11813 raw11813Labels = mixedMoment B raw11813step0 raw11813step0Labels := by
      have ha : raw11813step0 = (fun i j => raw11813 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11813step0 raw11813; decide +kernel
      have hl : raw11813step0Labels = raw11813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11813 raw11813Labels permutation156 permutation3
    _ = mixedMoment B node2996 node2996Labels := by rfl

theorem canonical11814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11814 raw11814Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11814 raw11814Labels = mixedMoment B raw11814step0 raw11814step0Labels := by
      have hz : ∀ j, raw11814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11814step0 = (fun i j => raw11814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11814step0 raw11814; decide +kernel
      have hl : raw11814step0Labels = raw11814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11814 raw11814Labels permutation434 hz
    mixedMoment B raw11814step0 raw11814step0Labels = mixedMoment B raw11814step1 raw11814step1Labels := by
      have ha : raw11814step1 = (fun i j => raw11814step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11814step1 raw11814step0; decide +kernel
      have hl : raw11814step1Labels = raw11814step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11814step0 raw11814step0Labels permutation33 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11815 raw11815Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11815 raw11815Labels = mixedMoment B raw11815step0 raw11815step0Labels := by
      have hz : ∀ j, raw11815 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11815step0 = (fun i j => raw11815 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11815step0 raw11815; decide +kernel
      have hl : raw11815step0Labels = raw11815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11815 raw11815Labels permutation520 hz
    mixedMoment B raw11815step0 raw11815step0Labels = mixedMoment B raw11815step1 raw11815step1Labels := by
      have ha : raw11815step1 = (fun i j => raw11815step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11815step1 raw11815step0; decide +kernel
      have hl : raw11815step1Labels = raw11815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11815step0 raw11815step0Labels permutation33 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11816 raw11816Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw11816 raw11816Labels = mixedMoment B raw11816step0 raw11816step0Labels := by
      have ha : raw11816step0 = (fun i j => raw11816 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11816step0 raw11816; decide +kernel
      have hl : raw11816step0Labels = raw11816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11816 raw11816Labels permutation246 permutation3
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical11817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11817 raw11817Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw11817 raw11817Labels = mixedMoment B raw11817step0 raw11817step0Labels := by
      have ha : raw11817step0 = (fun i j => raw11817 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11817step0 raw11817; decide +kernel
      have hl : raw11817step0Labels = raw11817Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11817 raw11817Labels permutation181 permutation3
    _ = mixedMoment B node1178 node1178Labels := by rfl

theorem canonical11818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11818 raw11818Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw11818 raw11818Labels = mixedMoment B raw11818step0 raw11818step0Labels := by
      have ha : raw11818step0 = (fun i j => raw11818 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11818step0 raw11818; decide +kernel
      have hl : raw11818step0Labels = raw11818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11818 raw11818Labels permutation157 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical11819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11819 raw11819Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11819 raw11819Labels = mixedMoment B raw11819step0 raw11819step0Labels := by
      have ha : raw11819step0 = (fun i j => raw11819 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11819step0 raw11819; decide +kernel
      have hl : raw11819step0Labels = raw11819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11819 raw11819Labels permutation181 permutation3
    _ = mixedMoment B node2833 node2833Labels := by rfl

theorem canonical11820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11820 raw11820Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw11820 raw11820Labels = mixedMoment B raw11820step0 raw11820step0Labels := by
      have hz : ∀ j, raw11820 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11820step0 = (fun i j => raw11820 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11820step0 raw11820; decide +kernel
      have hl : raw11820step0Labels = raw11820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11820 raw11820Labels permutation520 hz
    mixedMoment B raw11820step0 raw11820step0Labels = mixedMoment B raw11820step1 raw11820step1Labels := by
      have ha : raw11820step1 = (fun i j => raw11820step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11820step1 raw11820step0; decide +kernel
      have hl : raw11820step1Labels = raw11820step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11820step0 raw11820step0Labels permutation39 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical11821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11821 raw11821Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11821 raw11821Labels = mixedMoment B raw11821step0 raw11821step0Labels := by
      have ha : raw11821step0 = (fun i j => raw11821 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11821step0 raw11821; decide +kernel
      have hl : raw11821step0Labels = raw11821Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11821 raw11821Labels permutation195 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical11822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11822 raw11822Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw11822 raw11822Labels = mixedMoment B raw11822step0 raw11822step0Labels := by
      have ha : raw11822step0 = (fun i j => raw11822 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11822step0 raw11822; decide +kernel
      have hl : raw11822step0Labels = raw11822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11822 raw11822Labels permutation180 permutation3
    _ = mixedMoment B node1178 node1178Labels := by rfl

theorem canonical11823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11823 raw11823Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw11823 raw11823Labels = mixedMoment B raw11823step0 raw11823step0Labels := by
      have ha : raw11823step0 = (fun i j => raw11823 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11823step0 raw11823; decide +kernel
      have hl : raw11823step0Labels = raw11823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11823 raw11823Labels permutation156 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical11824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11824 raw11824Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11824 raw11824Labels = mixedMoment B raw11824step0 raw11824step0Labels := by
      have ha : raw11824step0 = (fun i j => raw11824 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11824step0 raw11824; decide +kernel
      have hl : raw11824step0Labels = raw11824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11824 raw11824Labels permutation180 permutation3
    _ = mixedMoment B node2833 node2833Labels := by rfl

theorem canonical11825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11825 raw11825Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw11825 raw11825Labels = mixedMoment B raw11825step0 raw11825step0Labels := by
      have hz : ∀ j, raw11825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11825step0 = (fun i j => raw11825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11825step0 raw11825; decide +kernel
      have hl : raw11825step0Labels = raw11825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11825 raw11825Labels permutation434 hz
    mixedMoment B raw11825step0 raw11825step0Labels = mixedMoment B raw11825step1 raw11825step1Labels := by
      have ha : raw11825step1 = (fun i j => raw11825step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11825step1 raw11825step0; decide +kernel
      have hl : raw11825step1Labels = raw11825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11825step0 raw11825step0Labels permutation39 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical11826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11826 raw11826Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11826 raw11826Labels = mixedMoment B raw11826step0 raw11826step0Labels := by
      have ha : raw11826step0 = (fun i j => raw11826 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11826step0 raw11826; decide +kernel
      have hl : raw11826step0Labels = raw11826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11826 raw11826Labels permutation194 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical11827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11827 raw11827Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw11827 raw11827Labels = mixedMoment B raw11827step0 raw11827step0Labels := by
      have ha : raw11827step0 = (fun i j => raw11827 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11827step0 raw11827; decide +kernel
      have hl : raw11827step0Labels = raw11827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11827 raw11827Labels permutation176 permutation3
    _ = mixedMoment B node1180 node1180Labels := by rfl

theorem canonical11828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11828 raw11828Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw11828 raw11828Labels = mixedMoment B raw11828step0 raw11828step0Labels := by
      have ha : raw11828step0 = (fun i j => raw11828 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11828step0 raw11828; decide +kernel
      have hl : raw11828step0Labels = raw11828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11828 raw11828Labels permutation152 permutation3
    _ = mixedMoment B node2976 node2976Labels := by rfl

theorem canonical11829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11829 raw11829Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw11829 raw11829Labels = mixedMoment B raw11829step0 raw11829step0Labels := by
      have ha : raw11829step0 = (fun i j => raw11829 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11829step0 raw11829; decide +kernel
      have hl : raw11829step0Labels = raw11829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11829 raw11829Labels permutation176 permutation3
    _ = mixedMoment B node2834 node2834Labels := by rfl

theorem canonical11830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11830 raw11830Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw11830 raw11830Labels = mixedMoment B raw11830step0 raw11830step0Labels := by
      have hz : ∀ j, raw11830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11830step0 = (fun i j => raw11830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11830step0 raw11830; decide +kernel
      have hl : raw11830step0Labels = raw11830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11830 raw11830Labels permutation434 hz
    mixedMoment B raw11830step0 raw11830step0Labels = mixedMoment B raw11830step1 raw11830step1Labels := by
      have ha : raw11830step1 = (fun i j => raw11830step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11830step1 raw11830step0; decide +kernel
      have hl : raw11830step1Labels = raw11830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11830step0 raw11830step0Labels permutation38 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical11831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11831 raw11831Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw11831 raw11831Labels = mixedMoment B raw11831step0 raw11831step0Labels := by
      have hz : ∀ j, raw11831 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11831step0 = (fun i j => raw11831 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11831step0 raw11831; decide +kernel
      have hl : raw11831step0Labels = raw11831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11831 raw11831Labels permutation520 hz
    mixedMoment B raw11831step0 raw11831step0Labels = mixedMoment B raw11831step1 raw11831step1Labels := by
      have ha : raw11831step1 = (fun i j => raw11831step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11831step1 raw11831step0; decide +kernel
      have hl : raw11831step1Labels = raw11831step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11831step0 raw11831step0Labels permutation38 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

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

theorem sound1178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1178 node1178Labels = Sparse.eval nodeValue1178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1178) = mixedMoment B node1178 node1178Labels := rfl
  simpa [nodeValue1178, Sparse.eval] using hc.symm

theorem sound1180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1180 node1180Labels = Sparse.eval nodeValue1180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1180) = mixedMoment B node1180 node1180Labels := rfl
  simpa [nodeValue1180, Sparse.eval] using hc.symm

theorem sound1183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1183 node1183Labels = Sparse.eval nodeValue1183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1183) = mixedMoment B node1183 node1183Labels := rfl
  simpa [nodeValue1183, Sparse.eval] using hc.symm

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

theorem sound2833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2833 node2833Labels = Sparse.eval nodeValue2833 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2833) = mixedMoment B node2833 node2833Labels := rfl
  simpa [nodeValue2833, Sparse.eval] using hc.symm

theorem sound2834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2834 node2834Labels = Sparse.eval nodeValue2834 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2834) = mixedMoment B node2834 node2834Labels := rfl
  simpa [nodeValue2834, Sparse.eval] using hc.symm

theorem sound2836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2836 node2836Labels = Sparse.eval nodeValue2836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2836) = mixedMoment B node2836 node2836Labels := rfl
  simpa [nodeValue2836, Sparse.eval] using hc.symm

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

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

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

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = 0 := by
  exact mixedMoment_alpha B hF node3085 node3085Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = Sparse.eval nodeValue3085 (mixedVector B) := by
  simpa only [nodeValue3085, Sparse.eval_nil] using zero3085 B _hB _hF

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

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

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

theorem sourceEq700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA700 + difference 0 1) (sourceB700 + difference 1 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA700 + difference 0 1) (sourceB700 + difference 1 0) sourceC700) = raw11802 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11802; decide +kernel
    rw [ha]
    exact (canonical11802 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA700 + difference 0 2) (sourceB700 + difference 2 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA700 + difference 0 2) (sourceB700 + difference 2 0) sourceC700) = raw11803 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11803; decide +kernel
    rw [ha]
    exact (canonical11803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA700 + difference 0 3) (sourceB700 + difference 3 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA700 + difference 0 3) (sourceB700 + difference 3 0) sourceC700) = raw11804 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11804; decide +kernel
    rw [ha]
    exact (canonical11804 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA700 + difference 0 4) (sourceB700 + difference 4 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA700 + difference 0 4) (sourceB700 + difference 4 0) sourceC700) = raw11805 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11805; decide +kernel
    rw [ha]
    exact (canonical11805 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA700 + difference 0 5) (sourceB700 + difference 5 0) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA700 + difference 0 5) (sourceB700 + difference 5 0) sourceC700) = raw11806 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11806; decide +kernel
    rw [ha]
    exact (canonical11806 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA700 + difference 1 0) (sourceB700 + difference 0 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA700 + difference 1 0) (sourceB700 + difference 0 1) sourceC700) = raw11807 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11807; decide +kernel
    rw [ha]
    exact (canonical11807 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA700 + difference 1 2) (sourceB700 + difference 2 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA700 + difference 1 2) (sourceB700 + difference 2 1) sourceC700) = raw11808 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11808; decide +kernel
    rw [ha]
    exact (canonical11808 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA700 + difference 1 3) (sourceB700 + difference 3 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA700 + difference 1 3) (sourceB700 + difference 3 1) sourceC700) = raw11809 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11809; decide +kernel
    rw [ha]
    exact (canonical11809 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA700 + difference 1 4) (sourceB700 + difference 4 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA700 + difference 1 4) (sourceB700 + difference 4 1) sourceC700) = raw11810 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11810; decide +kernel
    rw [ha]
    exact (canonical11810 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA700 + difference 1 5) (sourceB700 + difference 5 1) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA700 + difference 1 5) (sourceB700 + difference 5 1) sourceC700) = raw11811 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11811; decide +kernel
    rw [ha]
    exact (canonical11811 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA700 + difference 2 0) (sourceB700 + difference 0 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA700 + difference 2 0) (sourceB700 + difference 0 2) sourceC700) = raw11812 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11812; decide +kernel
    rw [ha]
    exact (canonical11812 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA700 + difference 2 1) (sourceB700 + difference 1 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2996) := by
    have ha : (tripleCharges (sourceA700 + difference 2 1) (sourceB700 + difference 1 2) sourceC700) = raw11813 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11813; decide +kernel
    rw [ha]
    exact (canonical11813 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA700 + difference 2 3) (sourceB700 + difference 3 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA700 + difference 2 3) (sourceB700 + difference 3 2) sourceC700) = raw11814 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11814; decide +kernel
    rw [ha]
    exact (canonical11814 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA700 + difference 2 4) (sourceB700 + difference 4 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA700 + difference 2 4) (sourceB700 + difference 4 2) sourceC700) = raw11815 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11815; decide +kernel
    rw [ha]
    exact (canonical11815 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA700 + difference 2 5) (sourceB700 + difference 5 2) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA700 + difference 2 5) (sourceB700 + difference 5 2) sourceC700) = raw11816 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11816; decide +kernel
    rw [ha]
    exact (canonical11816 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA700 + difference 3 0) (sourceB700 + difference 0 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA700 + difference 3 0) (sourceB700 + difference 0 3) sourceC700) = raw11817 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11817; decide +kernel
    rw [ha]
    exact (canonical11817 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA700 + difference 3 1) (sourceB700 + difference 1 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA700 + difference 3 1) (sourceB700 + difference 1 3) sourceC700) = raw11818 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11818; decide +kernel
    rw [ha]
    exact (canonical11818 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA700 + difference 3 2) (sourceB700 + difference 2 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA700 + difference 3 2) (sourceB700 + difference 2 3) sourceC700) = raw11819 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11819; decide +kernel
    rw [ha]
    exact (canonical11819 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA700 + difference 3 4) (sourceB700 + difference 4 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA700 + difference 3 4) (sourceB700 + difference 4 3) sourceC700) = raw11820 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11820; decide +kernel
    rw [ha]
    exact (canonical11820 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA700 + difference 3 5) (sourceB700 + difference 5 3) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA700 + difference 3 5) (sourceB700 + difference 5 3) sourceC700) = raw11821 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11821; decide +kernel
    rw [ha]
    exact (canonical11821 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA700 + difference 4 0) (sourceB700 + difference 0 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA700 + difference 4 0) (sourceB700 + difference 0 4) sourceC700) = raw11822 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11822; decide +kernel
    rw [ha]
    exact (canonical11822 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA700 + difference 4 1) (sourceB700 + difference 1 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA700 + difference 4 1) (sourceB700 + difference 1 4) sourceC700) = raw11823 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11823; decide +kernel
    rw [ha]
    exact (canonical11823 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA700 + difference 4 2) (sourceB700 + difference 2 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA700 + difference 4 2) (sourceB700 + difference 2 4) sourceC700) = raw11824 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11824; decide +kernel
    rw [ha]
    exact (canonical11824 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA700 + difference 4 3) (sourceB700 + difference 3 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA700 + difference 4 3) (sourceB700 + difference 3 4) sourceC700) = raw11825 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11825; decide +kernel
    rw [ha]
    exact (canonical11825 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA700 + difference 4 5) (sourceB700 + difference 5 4) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA700 + difference 4 5) (sourceB700 + difference 5 4) sourceC700) = raw11826 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11826; decide +kernel
    rw [ha]
    exact (canonical11826 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA700 + difference 5 0) (sourceB700 + difference 0 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA700 + difference 5 0) (sourceB700 + difference 0 5) sourceC700) = raw11827 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11827; decide +kernel
    rw [ha]
    exact (canonical11827 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA700 + difference 5 1) (sourceB700 + difference 1 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA700 + difference 5 1) (sourceB700 + difference 1 5) sourceC700) = raw11828 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11828; decide +kernel
    rw [ha]
    exact (canonical11828 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA700 + difference 5 2) (sourceB700 + difference 2 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA700 + difference 5 2) (sourceB700 + difference 2 5) sourceC700) = raw11829 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11829; decide +kernel
    rw [ha]
    exact (canonical11829 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA700 + difference 5 3) (sourceB700 + difference 3 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA700 + difference 5 3) (sourceB700 + difference 3 5) sourceC700) = raw11830 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11830; decide +kernel
    rw [ha]
    exact (canonical11830 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA700 + difference 5 4) (sourceB700 + difference 4 5) sourceC700) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA700 + difference 5 4) (sourceB700 + difference 4 5) sourceC700) = raw11831 := by
      apply Matrix.ext; unfold tripleCharges sourceA700 sourceB700 sourceC700 difference raw11831; decide +kernel
    rw [ha]
    exact (canonical11831 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA700 sourceB700 sourceC700
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm700, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck607 : Integer.Sparse.reindex keyMap MixedData.row607 = numericRow607 := by decide +kernel

theorem numericCheck607 (x : Master → ℝ) : Integer.Sparse.eval numericRow607 x =
    (4320 : ℝ) * reducedSource607 x := by
  norm_num [numericRow607, reducedSource607, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue1180, nodeValue1183, nodeValue1260, nodeValue2833, nodeValue2834, nodeValue2836, nodeValue2974, nodeValue2976, nodeValue2996, nodeValue3016, nodeValue3023, nodeValue3038, nodeValue3039, nodeValue3051, nodeValue3085, nodeValue3109, nodeValue3526, nodeValue3801, nodeValue3847, nodeValue3853] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource607 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h2833 : mixedVector B (Sum.inr 2833) = Sparse.eval nodeValue2833 (mixedVector B) := by
    change mixedMoment B node2833 node2833Labels = _
    exact sound2833 B hB hF
  have h2834 : mixedVector B (Sum.inr 2834) = Sparse.eval nodeValue2834 (mixedVector B) := by
    change mixedMoment B node2834 node2834Labels = _
    exact sound2834 B hB hF
  have h2836 : mixedVector B (Sum.inr 2836) = Sparse.eval nodeValue2836 (mixedVector B) := by
    change mixedMoment B node2836 node2836Labels = _
    exact sound2836 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h2996 : mixedVector B (Sum.inr 2996) = Sparse.eval nodeValue2996 (mixedVector B) := by
    change mixedMoment B node2996 node2996Labels = _
    exact sound2996_e B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109_e B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  simpa only [sourceForm700, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h1180, h1183, h1260, h2833, h2834, h2836, h2974, h2976, h2996, h3016, h3023, h3038, h3039, h3051, h3085, h3109, h3526, h3801, h3847, h3853, reducedSource607] using sourceEq700 B hB

theorem rowSound607_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row607 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck607, numericCheck607, reducedZero607 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e_oai
