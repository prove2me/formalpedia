-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:14:53.827609+00:00
-- url     : https://prove2.me/submissions/4cafec30-bfa1-4130-9296-1a6e17626dda

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3984_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound4026_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13269 raw13269Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13269 raw13269Labels = mixedMoment B raw13269step0 raw13269step0Labels := by
      have ha : raw13269step0 = (fun i j => raw13269 (permutation504 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13269step0 raw13269; decide +kernel
      have hl : raw13269step0Labels = raw13269Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13269 raw13269Labels permutation504 permutation7
    mixedMoment B raw13269step0 raw13269step0Labels = mixedMoment B raw13269step1 raw13269step1Labels := by
      have ha : raw13269step1 = raw13269step0 := by apply Matrix.ext; unfold raw13269step1 raw13269step0; decide +kernel
      have hl : raw13269step0Labels = labelEmbedding1 ∘ raw13269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13269step0 raw13269step0Labels raw13269step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical13270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13270 raw13270Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13270 raw13270Labels = mixedMoment B raw13270step0 raw13270step0Labels := by
      have ha : raw13270step0 = (fun i j => raw13270 (permutation502 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13270step0 raw13270; decide +kernel
      have hl : raw13270step0Labels = raw13270Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13270 raw13270Labels permutation502 permutation7
    mixedMoment B raw13270step0 raw13270step0Labels = mixedMoment B raw13270step1 raw13270step1Labels := by
      have ha : raw13270step1 = raw13270step0 := by apply Matrix.ext; unfold raw13270step1 raw13270step0; decide +kernel
      have hl : raw13270step0Labels = labelEmbedding1 ∘ raw13270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13270step0 raw13270step0Labels raw13270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical13271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13271 raw13271Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw13271 raw13271Labels = mixedMoment B raw13271step0 raw13271step0Labels := by
      have ha : raw13271step0 = (fun i j => raw13271 (permutation443 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13271step0 raw13271; decide +kernel
      have hl : raw13271step0Labels = raw13271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13271 raw13271Labels permutation443 permutation5
    mixedMoment B raw13271step0 raw13271step0Labels = mixedMoment B raw13271step1 raw13271step1Labels := by
      have ha : raw13271step1 = -raw13271step0 := by apply Matrix.ext; change ∀ i j, raw13271step1 i j = -(raw13271step0 i j); unfold raw13271step1 raw13271step0; decide +kernel
      have hl : raw13271step1Labels = raw13271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13271step1 raw13271step1Labels = mixedMoment B raw13271step2 raw13271step2Labels := by
      have ha : raw13271step2 = raw13271step1 := by apply Matrix.ext; unfold raw13271step2 raw13271step1; decide +kernel
      have hl : raw13271step1Labels = labelEmbedding1 ∘ raw13271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13271step1 raw13271step1Labels raw13271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

theorem canonical13272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13272 raw13272Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw13272 raw13272Labels = mixedMoment B raw13272step0 raw13272step0Labels := by
      have ha : raw13272step0 = (fun i j => raw13272 (permutation502 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13272step0 raw13272; decide +kernel
      have hl : raw13272step0Labels = raw13272Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13272 raw13272Labels permutation502 permutation7
    mixedMoment B raw13272step0 raw13272step0Labels = mixedMoment B raw13272step1 raw13272step1Labels := by
      have ha : raw13272step1 = raw13272step0 := by apply Matrix.ext; unfold raw13272step1 raw13272step0; decide +kernel
      have hl : raw13272step0Labels = labelEmbedding1 ∘ raw13272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13272step0 raw13272step0Labels raw13272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

theorem canonical13273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13273 raw13273Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw13273 raw13273Labels = mixedMoment B raw13273step0 raw13273step0Labels := by
      have hz : ∀ j, raw13273 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13273step0 = (fun i j => raw13273 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13273step0 raw13273; decide +kernel
      have hl : raw13273step0Labels = raw13273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13273 raw13273Labels permutation590 hz
    mixedMoment B raw13273step0 raw13273step0Labels = mixedMoment B raw13273step1 raw13273step1Labels := by
      have ha : raw13273step1 = (fun i j => raw13273step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13273step1 raw13273step0; decide +kernel
      have hl : raw13273step1Labels = raw13273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13273step0 raw13273step0Labels permutation125 permutation7
    mixedMoment B raw13273step1 raw13273step1Labels = mixedMoment B raw13273step2 raw13273step2Labels := by
      have ha : raw13273step2 = raw13273step1 := by apply Matrix.ext; unfold raw13273step2 raw13273step1; decide +kernel
      have hl : raw13273step1Labels = labelEmbedding1 ∘ raw13273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13273step1 raw13273step1Labels raw13273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

theorem canonical13274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13274 raw13274Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw13274 raw13274Labels = mixedMoment B raw13274step0 raw13274step0Labels := by
      have ha : raw13274step0 = (fun i j => raw13274 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13274step0 raw13274; decide +kernel
      have hl : raw13274step0Labels = raw13274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13274 raw13274Labels permutation215 permutation5
    mixedMoment B raw13274step0 raw13274step0Labels = mixedMoment B raw13274step1 raw13274step1Labels := by
      have ha : raw13274step1 = -raw13274step0 := by apply Matrix.ext; change ∀ i j, raw13274step1 i j = -(raw13274step0 i j); unfold raw13274step1 raw13274step0; decide +kernel
      have hl : raw13274step1Labels = raw13274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13274step1 raw13274step1Labels = mixedMoment B raw13274step2 raw13274step2Labels := by
      have ha : raw13274step2 = raw13274step1 := by apply Matrix.ext; unfold raw13274step2 raw13274step1; decide +kernel
      have hl : raw13274step1Labels = labelEmbedding1 ∘ raw13274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13274step1 raw13274step1Labels raw13274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical13275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13275 raw13275Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13275 raw13275Labels = mixedMoment B raw13275step0 raw13275step0Labels := by
      have ha : raw13275step0 = (fun i j => raw13275 (permutation209 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13275step0 raw13275; decide +kernel
      have hl : raw13275step0Labels = raw13275Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13275 raw13275Labels permutation209 permutation5
    mixedMoment B raw13275step0 raw13275step0Labels = mixedMoment B raw13275step1 raw13275step1Labels := by
      have ha : raw13275step1 = -raw13275step0 := by apply Matrix.ext; change ∀ i j, raw13275step1 i j = -(raw13275step0 i j); unfold raw13275step1 raw13275step0; decide +kernel
      have hl : raw13275step1Labels = raw13275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13275step1 raw13275step1Labels = mixedMoment B raw13275step2 raw13275step2Labels := by
      have ha : raw13275step2 = raw13275step1 := by apply Matrix.ext; unfold raw13275step2 raw13275step1; decide +kernel
      have hl : raw13275step1Labels = labelEmbedding1 ∘ raw13275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13275step1 raw13275step1Labels raw13275step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical13276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13276 raw13276Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw13276 raw13276Labels = mixedMoment B raw13276step0 raw13276step0Labels := by
      have ha : raw13276step0 = (fun i j => raw13276 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13276step0 raw13276; decide +kernel
      have hl : raw13276step0Labels = raw13276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13276 raw13276Labels permutation215 permutation5
    mixedMoment B raw13276step0 raw13276step0Labels = mixedMoment B raw13276step1 raw13276step1Labels := by
      have ha : raw13276step1 = -raw13276step0 := by apply Matrix.ext; change ∀ i j, raw13276step1 i j = -(raw13276step0 i j); unfold raw13276step1 raw13276step0; decide +kernel
      have hl : raw13276step1Labels = raw13276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13276step1 raw13276step1Labels = mixedMoment B raw13276step2 raw13276step2Labels := by
      have ha : raw13276step2 = raw13276step1 := by apply Matrix.ext; unfold raw13276step2 raw13276step1; decide +kernel
      have hl : raw13276step1Labels = labelEmbedding1 ∘ raw13276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13276step1 raw13276step1Labels raw13276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical13277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13277 raw13277Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw13277 raw13277Labels = mixedMoment B raw13277step0 raw13277step0Labels := by
      have ha : raw13277step0 = (fun i j => raw13277 (permutation237 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13277step0 raw13277; decide +kernel
      have hl : raw13277step0Labels = raw13277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13277 raw13277Labels permutation237 permutation5
    mixedMoment B raw13277step0 raw13277step0Labels = mixedMoment B raw13277step1 raw13277step1Labels := by
      have ha : raw13277step1 = -raw13277step0 := by apply Matrix.ext; change ∀ i j, raw13277step1 i j = -(raw13277step0 i j); unfold raw13277step1 raw13277step0; decide +kernel
      have hl : raw13277step1Labels = raw13277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13277step1 raw13277step1Labels = mixedMoment B raw13277step2 raw13277step2Labels := by
      have ha : raw13277step2 = raw13277step1 := by apply Matrix.ext; unfold raw13277step2 raw13277step1; decide +kernel
      have hl : raw13277step1Labels = labelEmbedding1 ∘ raw13277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13277step1 raw13277step1Labels raw13277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical13278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13278 raw13278Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13278 raw13278Labels = mixedMoment B raw13278step0 raw13278step0Labels := by
      have hz : ∀ j, raw13278 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13278step0 = (fun i j => raw13278 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13278step0 raw13278; decide +kernel
      have hl : raw13278step0Labels = raw13278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13278 raw13278Labels permutation590 hz
    mixedMoment B raw13278step0 raw13278step0Labels = mixedMoment B raw13278step1 raw13278step1Labels := by
      have ha : raw13278step1 = (fun i j => raw13278step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13278step1 raw13278step0; decide +kernel
      have hl : raw13278step1Labels = raw13278step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13278step0 raw13278step0Labels permutation49 permutation5
    mixedMoment B raw13278step1 raw13278step1Labels = mixedMoment B raw13278step2 raw13278step2Labels := by
      have ha : raw13278step2 = -raw13278step1 := by apply Matrix.ext; change ∀ i j, raw13278step2 i j = -(raw13278step1 i j); unfold raw13278step2 raw13278step1; decide +kernel
      have hl : raw13278step2Labels = raw13278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13278step2 raw13278step2Labels = mixedMoment B raw13278step3 raw13278step3Labels := by
      have ha : raw13278step3 = raw13278step2 := by apply Matrix.ext; unfold raw13278step3 raw13278step2; decide +kernel
      have hl : raw13278step2Labels = labelEmbedding1 ∘ raw13278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13278step2 raw13278step2Labels raw13278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical13279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13279 raw13279Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw13279 raw13279Labels = mixedMoment B raw13279step0 raw13279step0Labels := by
      have ha : raw13279step0 = (fun i j => raw13279 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13279step0 raw13279; decide +kernel
      have hl : raw13279step0Labels = raw13279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13279 raw13279Labels permutation213 permutation5
    mixedMoment B raw13279step0 raw13279step0Labels = mixedMoment B raw13279step1 raw13279step1Labels := by
      have ha : raw13279step1 = -raw13279step0 := by apply Matrix.ext; change ∀ i j, raw13279step1 i j = -(raw13279step0 i j); unfold raw13279step1 raw13279step0; decide +kernel
      have hl : raw13279step1Labels = raw13279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13279step1 raw13279step1Labels = mixedMoment B raw13279step2 raw13279step2Labels := by
      have ha : raw13279step2 = raw13279step1 := by apply Matrix.ext; unfold raw13279step2 raw13279step1; decide +kernel
      have hl : raw13279step1Labels = labelEmbedding1 ∘ raw13279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13279step1 raw13279step1Labels raw13279step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical13280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13280 raw13280Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13280 raw13280Labels = mixedMoment B raw13280step0 raw13280step0Labels := by
      have ha : raw13280step0 = (fun i j => raw13280 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13280step0 raw13280; decide +kernel
      have hl : raw13280step0Labels = raw13280Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13280 raw13280Labels permutation203 permutation5
    mixedMoment B raw13280step0 raw13280step0Labels = mixedMoment B raw13280step1 raw13280step1Labels := by
      have ha : raw13280step1 = -raw13280step0 := by apply Matrix.ext; change ∀ i j, raw13280step1 i j = -(raw13280step0 i j); unfold raw13280step1 raw13280step0; decide +kernel
      have hl : raw13280step1Labels = raw13280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13280step1 raw13280step1Labels = mixedMoment B raw13280step2 raw13280step2Labels := by
      have ha : raw13280step2 = raw13280step1 := by apply Matrix.ext; unfold raw13280step2 raw13280step1; decide +kernel
      have hl : raw13280step1Labels = labelEmbedding1 ∘ raw13280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13280step1 raw13280step1Labels raw13280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical13281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13281 raw13281Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw13281 raw13281Labels = mixedMoment B raw13281step0 raw13281step0Labels := by
      have ha : raw13281step0 = (fun i j => raw13281 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13281step0 raw13281; decide +kernel
      have hl : raw13281step0Labels = raw13281Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13281 raw13281Labels permutation213 permutation5
    mixedMoment B raw13281step0 raw13281step0Labels = mixedMoment B raw13281step1 raw13281step1Labels := by
      have ha : raw13281step1 = -raw13281step0 := by apply Matrix.ext; change ∀ i j, raw13281step1 i j = -(raw13281step0 i j); unfold raw13281step1 raw13281step0; decide +kernel
      have hl : raw13281step1Labels = raw13281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13281step1 raw13281step1Labels = mixedMoment B raw13281step2 raw13281step2Labels := by
      have ha : raw13281step2 = raw13281step1 := by apply Matrix.ext; unfold raw13281step2 raw13281step1; decide +kernel
      have hl : raw13281step1Labels = labelEmbedding1 ∘ raw13281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13281step1 raw13281step1Labels raw13281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical13282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13282 raw13282Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw13282 raw13282Labels = mixedMoment B raw13282step0 raw13282step0Labels := by
      have ha : raw13282step0 = (fun i j => raw13282 (permutation235 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13282step0 raw13282; decide +kernel
      have hl : raw13282step0Labels = raw13282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13282 raw13282Labels permutation235 permutation5
    mixedMoment B raw13282step0 raw13282step0Labels = mixedMoment B raw13282step1 raw13282step1Labels := by
      have ha : raw13282step1 = -raw13282step0 := by apply Matrix.ext; change ∀ i j, raw13282step1 i j = -(raw13282step0 i j); unfold raw13282step1 raw13282step0; decide +kernel
      have hl : raw13282step1Labels = raw13282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13282step1 raw13282step1Labels = mixedMoment B raw13282step2 raw13282step2Labels := by
      have ha : raw13282step2 = raw13282step1 := by apply Matrix.ext; unfold raw13282step2 raw13282step1; decide +kernel
      have hl : raw13282step1Labels = labelEmbedding1 ∘ raw13282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13282step1 raw13282step1Labels raw13282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical13283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13283 raw13283Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13283 raw13283Labels = mixedMoment B raw13283step0 raw13283step0Labels := by
      have hz : ∀ j, raw13283 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13283step0 = (fun i j => raw13283 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13283step0 raw13283; decide +kernel
      have hl : raw13283step0Labels = raw13283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13283 raw13283Labels permutation590 hz
    mixedMoment B raw13283step0 raw13283step0Labels = mixedMoment B raw13283step1 raw13283step1Labels := by
      have ha : raw13283step1 = (fun i j => raw13283step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13283step1 raw13283step0; decide +kernel
      have hl : raw13283step1Labels = raw13283step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13283step0 raw13283step0Labels permutation48 permutation5
    mixedMoment B raw13283step1 raw13283step1Labels = mixedMoment B raw13283step2 raw13283step2Labels := by
      have ha : raw13283step2 = -raw13283step1 := by apply Matrix.ext; change ∀ i j, raw13283step2 i j = -(raw13283step1 i j); unfold raw13283step2 raw13283step1; decide +kernel
      have hl : raw13283step2Labels = raw13283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13283step2 raw13283step2Labels = mixedMoment B raw13283step3 raw13283step3Labels := by
      have ha : raw13283step3 = raw13283step2 := by apply Matrix.ext; unfold raw13283step3 raw13283step2; decide +kernel
      have hl : raw13283step2Labels = labelEmbedding1 ∘ raw13283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13283step2 raw13283step2Labels raw13283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical13284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13284 raw13284Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw13284 raw13284Labels = mixedMoment B raw13284step0 raw13284step0Labels := by
      have ha : raw13284step0 = (fun i j => raw13284 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13284step0 raw13284; decide +kernel
      have hl : raw13284step0Labels = raw13284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13284 raw13284Labels permutation234 permutation5
    mixedMoment B raw13284step0 raw13284step0Labels = mixedMoment B raw13284step1 raw13284step1Labels := by
      have ha : raw13284step1 = -raw13284step0 := by apply Matrix.ext; change ∀ i j, raw13284step1 i j = -(raw13284step0 i j); unfold raw13284step1 raw13284step0; decide +kernel
      have hl : raw13284step1Labels = raw13284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13284step1 raw13284step1Labels = mixedMoment B raw13284step2 raw13284step2Labels := by
      have ha : raw13284step2 = raw13284step1 := by apply Matrix.ext; unfold raw13284step2 raw13284step1; decide +kernel
      have hl : raw13284step1Labels = labelEmbedding1 ∘ raw13284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13284step1 raw13284step1Labels raw13284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical13285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13285 raw13285Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw13285 raw13285Labels = mixedMoment B raw13285step0 raw13285step0Labels := by
      have ha : raw13285step0 = (fun i j => raw13285 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13285step0 raw13285; decide +kernel
      have hl : raw13285step0Labels = raw13285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13285 raw13285Labels permutation166 permutation5
    mixedMoment B raw13285step0 raw13285step0Labels = mixedMoment B raw13285step1 raw13285step1Labels := by
      have ha : raw13285step1 = -raw13285step0 := by apply Matrix.ext; change ∀ i j, raw13285step1 i j = -(raw13285step0 i j); unfold raw13285step1 raw13285step0; decide +kernel
      have hl : raw13285step1Labels = raw13285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13285step1 raw13285step1Labels = mixedMoment B raw13285step2 raw13285step2Labels := by
      have ha : raw13285step2 = raw13285step1 := by apply Matrix.ext; unfold raw13285step2 raw13285step1; decide +kernel
      have hl : raw13285step1Labels = labelEmbedding1 ∘ raw13285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13285step1 raw13285step1Labels raw13285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical13286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13286 raw13286Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw13286 raw13286Labels = mixedMoment B raw13286step0 raw13286step0Labels := by
      have ha : raw13286step0 = (fun i j => raw13286 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13286step0 raw13286; decide +kernel
      have hl : raw13286step0Labels = raw13286Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13286 raw13286Labels permutation190 permutation5
    mixedMoment B raw13286step0 raw13286step0Labels = mixedMoment B raw13286step1 raw13286step1Labels := by
      have ha : raw13286step1 = -raw13286step0 := by apply Matrix.ext; change ∀ i j, raw13286step1 i j = -(raw13286step0 i j); unfold raw13286step1 raw13286step0; decide +kernel
      have hl : raw13286step1Labels = raw13286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13286step1 raw13286step1Labels = mixedMoment B raw13286step2 raw13286step2Labels := by
      have ha : raw13286step2 = raw13286step1 := by apply Matrix.ext; unfold raw13286step2 raw13286step1; decide +kernel
      have hl : raw13286step1Labels = labelEmbedding1 ∘ raw13286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13286step1 raw13286step1Labels raw13286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical13287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13287 raw13287Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13287 raw13287Labels = mixedMoment B raw13287step0 raw13287step0Labels := by
      have ha : raw13287step0 = (fun i j => raw13287 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13287step0 raw13287; decide +kernel
      have hl : raw13287step0Labels = raw13287Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13287 raw13287Labels permutation234 permutation5
    mixedMoment B raw13287step0 raw13287step0Labels = mixedMoment B raw13287step1 raw13287step1Labels := by
      have ha : raw13287step1 = -raw13287step0 := by apply Matrix.ext; change ∀ i j, raw13287step1 i j = -(raw13287step0 i j); unfold raw13287step1 raw13287step0; decide +kernel
      have hl : raw13287step1Labels = raw13287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13287step1 raw13287step1Labels = mixedMoment B raw13287step2 raw13287step2Labels := by
      have ha : raw13287step2 = raw13287step1 := by apply Matrix.ext; unfold raw13287step2 raw13287step1; decide +kernel
      have hl : raw13287step1Labels = labelEmbedding1 ∘ raw13287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13287step1 raw13287step1Labels raw13287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical13288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13288 raw13288Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw13288 raw13288Labels = mixedMoment B raw13288step0 raw13288step0Labels := by
      have hz : ∀ j, raw13288 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13288step0 = (fun i j => raw13288 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13288step0 raw13288; decide +kernel
      have hl : raw13288step0Labels = raw13288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13288 raw13288Labels permutation590 hz
    mixedMoment B raw13288step0 raw13288step0Labels = mixedMoment B raw13288step1 raw13288step1Labels := by
      have ha : raw13288step1 = (fun i j => raw13288step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13288step1 raw13288step0; decide +kernel
      have hl : raw13288step1Labels = raw13288step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13288step0 raw13288step0Labels permutation54 permutation5
    mixedMoment B raw13288step1 raw13288step1Labels = mixedMoment B raw13288step2 raw13288step2Labels := by
      have ha : raw13288step2 = -raw13288step1 := by apply Matrix.ext; change ∀ i j, raw13288step2 i j = -(raw13288step1 i j); unfold raw13288step2 raw13288step1; decide +kernel
      have hl : raw13288step2Labels = raw13288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13288step2 raw13288step2Labels = mixedMoment B raw13288step3 raw13288step3Labels := by
      have ha : raw13288step3 = raw13288step2 := by apply Matrix.ext; unfold raw13288step3 raw13288step2; decide +kernel
      have hl : raw13288step2Labels = labelEmbedding1 ∘ raw13288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13288step2 raw13288step2Labels raw13288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical13289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13289 raw13289Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw13289 raw13289Labels = mixedMoment B raw13289step0 raw13289step0Labels := by
      have ha : raw13289step0 = (fun i j => raw13289 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13289step0 raw13289; decide +kernel
      have hl : raw13289step0Labels = raw13289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13289 raw13289Labels permutation201 permutation5
    mixedMoment B raw13289step0 raw13289step0Labels = mixedMoment B raw13289step1 raw13289step1Labels := by
      have ha : raw13289step1 = -raw13289step0 := by apply Matrix.ext; change ∀ i j, raw13289step1 i j = -(raw13289step0 i j); unfold raw13289step1 raw13289step0; decide +kernel
      have hl : raw13289step1Labels = raw13289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13289step1 raw13289step1Labels = mixedMoment B raw13289step2 raw13289step2Labels := by
      have ha : raw13289step2 = raw13289step1 := by apply Matrix.ext; unfold raw13289step2 raw13289step1; decide +kernel
      have hl : raw13289step1Labels = labelEmbedding1 ∘ raw13289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13289step1 raw13289step1Labels raw13289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1642 node1642Labels := by rfl

theorem canonical13290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13290 raw13290Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13290 raw13290Labels = mixedMoment B raw13290step0 raw13290step0Labels := by
      have ha : raw13290step0 = (fun i j => raw13290 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13290step0 raw13290; decide +kernel
      have hl : raw13290step0Labels = raw13290Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13290 raw13290Labels permutation201 permutation5
    mixedMoment B raw13290step0 raw13290step0Labels = mixedMoment B raw13290step1 raw13290step1Labels := by
      have ha : raw13290step1 = -raw13290step0 := by apply Matrix.ext; change ∀ i j, raw13290step1 i j = -(raw13290step0 i j); unfold raw13290step1 raw13290step0; decide +kernel
      have hl : raw13290step1Labels = raw13290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13290step1 raw13290step1Labels = mixedMoment B raw13290step2 raw13290step2Labels := by
      have ha : raw13290step2 = raw13290step1 := by apply Matrix.ext; unfold raw13290step2 raw13290step1; decide +kernel
      have hl : raw13290step1Labels = labelEmbedding1 ∘ raw13290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13290step1 raw13290step1Labels raw13290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical13291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13291 raw13291Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13291 raw13291Labels = mixedMoment B raw13291step0 raw13291step0Labels := by
      have ha : raw13291step0 = (fun i j => raw13291 (permutation207 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13291step0 raw13291; decide +kernel
      have hl : raw13291step0Labels = raw13291Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13291 raw13291Labels permutation207 permutation5
    mixedMoment B raw13291step0 raw13291step0Labels = mixedMoment B raw13291step1 raw13291step1Labels := by
      have ha : raw13291step1 = -raw13291step0 := by apply Matrix.ext; change ∀ i j, raw13291step1 i j = -(raw13291step0 i j); unfold raw13291step1 raw13291step0; decide +kernel
      have hl : raw13291step1Labels = raw13291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13291step1 raw13291step1Labels = mixedMoment B raw13291step2 raw13291step2Labels := by
      have ha : raw13291step2 = raw13291step1 := by apply Matrix.ext; unfold raw13291step2 raw13291step1; decide +kernel
      have hl : raw13291step1Labels = labelEmbedding1 ∘ raw13291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13291step1 raw13291step1Labels raw13291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical13292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13292 raw13292Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw13292 raw13292Labels = mixedMoment B raw13292step0 raw13292step0Labels := by
      have ha : raw13292step0 = (fun i j => raw13292 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13292step0 raw13292; decide +kernel
      have hl : raw13292step0Labels = raw13292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13292 raw13292Labels permutation201 permutation5
    mixedMoment B raw13292step0 raw13292step0Labels = mixedMoment B raw13292step1 raw13292step1Labels := by
      have ha : raw13292step1 = -raw13292step0 := by apply Matrix.ext; change ∀ i j, raw13292step1 i j = -(raw13292step0 i j); unfold raw13292step1 raw13292step0; decide +kernel
      have hl : raw13292step1Labels = raw13292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13292step1 raw13292step1Labels = mixedMoment B raw13292step2 raw13292step2Labels := by
      have ha : raw13292step2 = raw13292step1 := by apply Matrix.ext; unfold raw13292step2 raw13292step1; decide +kernel
      have hl : raw13292step1Labels = labelEmbedding1 ∘ raw13292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13292step1 raw13292step1Labels raw13292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3388 node3388Labels := by rfl

theorem canonical13293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13293 raw13293Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw13293 raw13293Labels = mixedMoment B raw13293step0 raw13293step0Labels := by
      have hz : ∀ j, raw13293 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13293step0 = (fun i j => raw13293 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13293step0 raw13293; decide +kernel
      have hl : raw13293step0Labels = raw13293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13293 raw13293Labels permutation590 hz
    mixedMoment B raw13293step0 raw13293step0Labels = mixedMoment B raw13293step1 raw13293step1Labels := by
      have ha : raw13293step1 = (fun i j => raw13293step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13293step1 raw13293step0; decide +kernel
      have hl : raw13293step1Labels = raw13293step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13293step0 raw13293step0Labels permutation44 permutation5
    mixedMoment B raw13293step1 raw13293step1Labels = mixedMoment B raw13293step2 raw13293step2Labels := by
      have ha : raw13293step2 = -raw13293step1 := by apply Matrix.ext; change ∀ i j, raw13293step2 i j = -(raw13293step1 i j); unfold raw13293step2 raw13293step1; decide +kernel
      have hl : raw13293step2Labels = raw13293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13293step2 raw13293step2Labels = mixedMoment B raw13293step3 raw13293step3Labels := by
      have ha : raw13293step3 = raw13293step2 := by apply Matrix.ext; unfold raw13293step3 raw13293step2; decide +kernel
      have hl : raw13293step2Labels = labelEmbedding1 ∘ raw13293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13293step2 raw13293step2Labels raw13293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical13294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13294 raw13294Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw13294 raw13294Labels = mixedMoment B raw13294step0 raw13294step0Labels := by
      have ha : raw13294step0 = (fun i j => raw13294 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13294step0 raw13294; decide +kernel
      have hl : raw13294step0Labels = raw13294Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13294 raw13294Labels permutation212 permutation5
    mixedMoment B raw13294step0 raw13294step0Labels = mixedMoment B raw13294step1 raw13294step1Labels := by
      have ha : raw13294step1 = -raw13294step0 := by apply Matrix.ext; change ∀ i j, raw13294step1 i j = -(raw13294step0 i j); unfold raw13294step1 raw13294step0; decide +kernel
      have hl : raw13294step1Labels = raw13294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13294step1 raw13294step1Labels = mixedMoment B raw13294step2 raw13294step2Labels := by
      have ha : raw13294step2 = raw13294step1 := by apply Matrix.ext; unfold raw13294step2 raw13294step1; decide +kernel
      have hl : raw13294step1Labels = labelEmbedding1 ∘ raw13294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13294step1 raw13294step1Labels raw13294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1635 node1635Labels := by rfl

theorem canonical13295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13295 raw13295Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw13295 raw13295Labels = mixedMoment B raw13295step0 raw13295step0Labels := by
      have ha : raw13295step0 = (fun i j => raw13295 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13295step0 raw13295; decide +kernel
      have hl : raw13295step0Labels = raw13295Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13295 raw13295Labels permutation202 permutation5
    mixedMoment B raw13295step0 raw13295step0Labels = mixedMoment B raw13295step1 raw13295step1Labels := by
      have ha : raw13295step1 = -raw13295step0 := by apply Matrix.ext; change ∀ i j, raw13295step1 i j = -(raw13295step0 i j); unfold raw13295step1 raw13295step0; decide +kernel
      have hl : raw13295step1Labels = raw13295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13295step1 raw13295step1Labels = mixedMoment B raw13295step2 raw13295step2Labels := by
      have ha : raw13295step2 = raw13295step1 := by apply Matrix.ext; unfold raw13295step2 raw13295step1; decide +kernel
      have hl : raw13295step1Labels = labelEmbedding1 ∘ raw13295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13295step1 raw13295step1Labels raw13295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical13296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13296 raw13296Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw13296 raw13296Labels = mixedMoment B raw13296step0 raw13296step0Labels := by
      have ha : raw13296step0 = (fun i j => raw13296 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13296step0 raw13296; decide +kernel
      have hl : raw13296step0Labels = raw13296Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13296 raw13296Labels permutation208 permutation5
    mixedMoment B raw13296step0 raw13296step0Labels = mixedMoment B raw13296step1 raw13296step1Labels := by
      have ha : raw13296step1 = -raw13296step0 := by apply Matrix.ext; change ∀ i j, raw13296step1 i j = -(raw13296step0 i j); unfold raw13296step1 raw13296step0; decide +kernel
      have hl : raw13296step1Labels = raw13296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13296step1 raw13296step1Labels = mixedMoment B raw13296step2 raw13296step2Labels := by
      have ha : raw13296step2 = raw13296step1 := by apply Matrix.ext; unfold raw13296step2 raw13296step1; decide +kernel
      have hl : raw13296step1Labels = labelEmbedding1 ∘ raw13296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13296step1 raw13296step1Labels raw13296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical13297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13297 raw13297Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw13297 raw13297Labels = mixedMoment B raw13297step0 raw13297step0Labels := by
      have ha : raw13297step0 = (fun i j => raw13297 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13297step0 raw13297; decide +kernel
      have hl : raw13297step0Labels = raw13297Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13297 raw13297Labels permutation212 permutation5
    mixedMoment B raw13297step0 raw13297step0Labels = mixedMoment B raw13297step1 raw13297step1Labels := by
      have ha : raw13297step1 = -raw13297step0 := by apply Matrix.ext; change ∀ i j, raw13297step1 i j = -(raw13297step0 i j); unfold raw13297step1 raw13297step0; decide +kernel
      have hl : raw13297step1Labels = raw13297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13297step1 raw13297step1Labels = mixedMoment B raw13297step2 raw13297step2Labels := by
      have ha : raw13297step2 = raw13297step1 := by apply Matrix.ext; unfold raw13297step2 raw13297step1; decide +kernel
      have hl : raw13297step1Labels = labelEmbedding1 ∘ raw13297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13297step1 raw13297step1Labels raw13297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3375 node3375Labels := by rfl

theorem canonical13298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13298 raw13298Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw13298 raw13298Labels = mixedMoment B raw13298step0 raw13298step0Labels := by
      have ha : raw13298step0 = (fun i j => raw13298 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13298step0 raw13298; decide +kernel
      have hl : raw13298step0Labels = raw13298Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13298 raw13298Labels permutation234 permutation5
    mixedMoment B raw13298step0 raw13298step0Labels = mixedMoment B raw13298step1 raw13298step1Labels := by
      have ha : raw13298step1 = -raw13298step0 := by apply Matrix.ext; change ∀ i j, raw13298step1 i j = -(raw13298step0 i j); unfold raw13298step1 raw13298step0; decide +kernel
      have hl : raw13298step1Labels = raw13298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13298step1 raw13298step1Labels = mixedMoment B raw13298step2 raw13298step2Labels := by
      have ha : raw13298step2 = raw13298step1 := by apply Matrix.ext; unfold raw13298step2 raw13298step1; decide +kernel
      have hl : raw13298step1Labels = labelEmbedding1 ∘ raw13298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13298step1 raw13298step1Labels raw13298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3502 node3502Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1635 node1635Labels = Sparse.eval nodeValue1635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1635) = mixedMoment B node1635 node1635Labels := rfl
  simpa [nodeValue1635, Sparse.eval] using hc.symm

theorem sound1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1636 node1636Labels = Sparse.eval nodeValue1636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1636) = mixedMoment B node1636 node1636Labels := rfl
  simpa [nodeValue1636, Sparse.eval] using hc.symm

theorem sound1642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1642 node1642Labels = Sparse.eval nodeValue1642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1642) = mixedMoment B node1642 node1642Labels := rfl
  simpa [nodeValue1642, Sparse.eval] using hc.symm

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

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

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

theorem sound3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3375 node3375Labels = Sparse.eval nodeValue3375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3375) = mixedMoment B node3375 node3375Labels := rfl
  simpa [nodeValue3375, Sparse.eval] using hc.symm

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

theorem sound3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3388 node3388Labels = Sparse.eval nodeValue3388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3388) = mixedMoment B node3388 node3388Labels := rfl
  simpa [nodeValue3388, Sparse.eval] using hc.symm

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

theorem sound3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3502 node3502Labels = Sparse.eval nodeValue3502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3502) = mixedMoment B node3502 node3502Labels := rfl
  simpa [nodeValue3502, Sparse.eval] using hc.symm

theorem sound3503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3503 node3503Labels = Sparse.eval nodeValue3503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3503) = mixedMoment B node3503 node3503Labels := rfl
  simpa [nodeValue3503, Sparse.eval] using hc.symm

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

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

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

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3991 node3991Labels = 0 := by
  exact mixedMoment_alpha B hF node3991 node3991Labels 1 permutation161
    (by decide +kernel)

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

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3991 node3991Labels = Sparse.eval nodeValue3991 (mixedVector B) := by
  simpa only [nodeValue3991, Sparse.eval_nil] using zero3991 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm803 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA803 + difference 0 1) (sourceB803 + difference 1 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA803 + difference 0 1) (sourceB803 + difference 1 0) sourceC803) = raw13269 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13269; decide +kernel
    rw [ha]
    exact (canonical13269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA803 + difference 0 2) (sourceB803 + difference 2 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA803 + difference 0 2) (sourceB803 + difference 2 0) sourceC803) = raw13270 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13270; decide +kernel
    rw [ha]
    exact (canonical13270 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA803 + difference 0 3) (sourceB803 + difference 3 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA803 + difference 0 3) (sourceB803 + difference 3 0) sourceC803) = raw13271 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13271; decide +kernel
    rw [ha]
    exact (canonical13271 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA803 + difference 0 4) (sourceB803 + difference 4 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA803 + difference 0 4) (sourceB803 + difference 4 0) sourceC803) = raw13272 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13272; decide +kernel
    rw [ha]
    exact (canonical13272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA803 + difference 0 5) (sourceB803 + difference 5 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA803 + difference 0 5) (sourceB803 + difference 5 0) sourceC803) = raw13273 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13273; decide +kernel
    rw [ha]
    exact (canonical13273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA803 + difference 1 0) (sourceB803 + difference 0 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA803 + difference 1 0) (sourceB803 + difference 0 1) sourceC803) = raw13274 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13274; decide +kernel
    rw [ha]
    exact (canonical13274 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA803 + difference 1 2) (sourceB803 + difference 2 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA803 + difference 1 2) (sourceB803 + difference 2 1) sourceC803) = raw13275 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13275; decide +kernel
    rw [ha]
    exact (canonical13275 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA803 + difference 1 3) (sourceB803 + difference 3 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA803 + difference 1 3) (sourceB803 + difference 3 1) sourceC803) = raw13276 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13276; decide +kernel
    rw [ha]
    exact (canonical13276 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA803 + difference 1 4) (sourceB803 + difference 4 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA803 + difference 1 4) (sourceB803 + difference 4 1) sourceC803) = raw13277 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13277; decide +kernel
    rw [ha]
    exact (canonical13277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA803 + difference 1 5) (sourceB803 + difference 5 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA803 + difference 1 5) (sourceB803 + difference 5 1) sourceC803) = raw13278 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13278; decide +kernel
    rw [ha]
    exact (canonical13278 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA803 + difference 2 0) (sourceB803 + difference 0 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA803 + difference 2 0) (sourceB803 + difference 0 2) sourceC803) = raw13279 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13279; decide +kernel
    rw [ha]
    exact (canonical13279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA803 + difference 2 1) (sourceB803 + difference 1 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA803 + difference 2 1) (sourceB803 + difference 1 2) sourceC803) = raw13280 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13280; decide +kernel
    rw [ha]
    exact (canonical13280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA803 + difference 2 3) (sourceB803 + difference 3 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA803 + difference 2 3) (sourceB803 + difference 3 2) sourceC803) = raw13281 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13281; decide +kernel
    rw [ha]
    exact (canonical13281 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA803 + difference 2 4) (sourceB803 + difference 4 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA803 + difference 2 4) (sourceB803 + difference 4 2) sourceC803) = raw13282 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13282; decide +kernel
    rw [ha]
    exact (canonical13282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA803 + difference 2 5) (sourceB803 + difference 5 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA803 + difference 2 5) (sourceB803 + difference 5 2) sourceC803) = raw13283 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13283; decide +kernel
    rw [ha]
    exact (canonical13283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA803 + difference 3 0) (sourceB803 + difference 0 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA803 + difference 3 0) (sourceB803 + difference 0 3) sourceC803) = raw13284 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13284; decide +kernel
    rw [ha]
    exact (canonical13284 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA803 + difference 3 1) (sourceB803 + difference 1 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA803 + difference 3 1) (sourceB803 + difference 1 3) sourceC803) = raw13285 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13285; decide +kernel
    rw [ha]
    exact (canonical13285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA803 + difference 3 2) (sourceB803 + difference 2 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA803 + difference 3 2) (sourceB803 + difference 2 3) sourceC803) = raw13286 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13286; decide +kernel
    rw [ha]
    exact (canonical13286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA803 + difference 3 4) (sourceB803 + difference 4 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA803 + difference 3 4) (sourceB803 + difference 4 3) sourceC803) = raw13287 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13287; decide +kernel
    rw [ha]
    exact (canonical13287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA803 + difference 3 5) (sourceB803 + difference 5 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA803 + difference 3 5) (sourceB803 + difference 5 3) sourceC803) = raw13288 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13288; decide +kernel
    rw [ha]
    exact (canonical13288 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA803 + difference 4 0) (sourceB803 + difference 0 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA803 + difference 4 0) (sourceB803 + difference 0 4) sourceC803) = raw13289 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13289; decide +kernel
    rw [ha]
    exact (canonical13289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA803 + difference 4 1) (sourceB803 + difference 1 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA803 + difference 4 1) (sourceB803 + difference 1 4) sourceC803) = raw13290 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13290; decide +kernel
    rw [ha]
    exact (canonical13290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA803 + difference 4 2) (sourceB803 + difference 2 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA803 + difference 4 2) (sourceB803 + difference 2 4) sourceC803) = raw13291 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13291; decide +kernel
    rw [ha]
    exact (canonical13291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA803 + difference 4 3) (sourceB803 + difference 3 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA803 + difference 4 3) (sourceB803 + difference 3 4) sourceC803) = raw13292 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13292; decide +kernel
    rw [ha]
    exact (canonical13292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA803 + difference 4 5) (sourceB803 + difference 5 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA803 + difference 4 5) (sourceB803 + difference 5 4) sourceC803) = raw13293 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13293; decide +kernel
    rw [ha]
    exact (canonical13293 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA803 + difference 5 0) (sourceB803 + difference 0 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA803 + difference 5 0) (sourceB803 + difference 0 5) sourceC803) = raw13294 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13294; decide +kernel
    rw [ha]
    exact (canonical13294 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA803 + difference 5 1) (sourceB803 + difference 1 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA803 + difference 5 1) (sourceB803 + difference 1 5) sourceC803) = raw13295 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13295; decide +kernel
    rw [ha]
    exact (canonical13295 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA803 + difference 5 2) (sourceB803 + difference 2 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA803 + difference 5 2) (sourceB803 + difference 2 5) sourceC803) = raw13296 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13296; decide +kernel
    rw [ha]
    exact (canonical13296 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA803 + difference 5 3) (sourceB803 + difference 3 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA803 + difference 5 3) (sourceB803 + difference 3 5) sourceC803) = raw13297 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13297; decide +kernel
    rw [ha]
    exact (canonical13297 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA803 + difference 5 4) (sourceB803 + difference 4 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA803 + difference 5 4) (sourceB803 + difference 4 5) sourceC803) = raw13298 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13298; decide +kernel
    rw [ha]
    exact (canonical13298 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA803 sourceB803 sourceC803
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm803, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck695 : Integer.Sparse.reindex keyMap MixedData.row695 = numericRow695 := by decide +kernel

theorem numericCheck695 (x : Master → ℝ) : Integer.Sparse.eval numericRow695 x =
    (4320 : ℝ) * reducedSource695 x := by
  norm_num [numericRow695, reducedSource695, Integer.Sparse.eval, Sparse.eval, nodeValue1635, nodeValue1636, nodeValue1642, nodeValue1713, nodeValue3375, nodeValue3376, nodeValue3388, nodeValue3502, nodeValue3503, nodeValue3539, nodeValue3557, nodeValue3558, nodeValue3562, nodeValue3572, nodeValue3580, nodeValue3605, nodeValue3625, nodeValue3974, nodeValue3984, nodeValue3991, nodeValue4026]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource695 (mixedVector B) = 0 := by
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
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
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3984 : mixedVector B (Sum.inr 3984) = Sparse.eval nodeValue3984 (mixedVector B) := by
    change mixedMoment B node3984 node3984Labels = _
    exact sound3984_e B hB hF
  have h3991 : mixedVector B (Sum.inr 3991) = Sparse.eval nodeValue3991 (mixedVector B) := by
    change mixedMoment B node3991 node3991Labels = _
    exact sound3991 B hB hF
  have h4026 : mixedVector B (Sum.inr 4026) = Sparse.eval nodeValue4026 (mixedVector B) := by
    change mixedMoment B node4026 node4026Labels = _
    exact sound4026_e B hB hF
  simpa only [sourceForm803, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1635, h1636, h1642, h1713, h3375, h3376, h3388, h3502, h3503, h3539, h3557, h3558, h3562, h3572, h3580, h3605, h3625, h3974, h3984, h3991, h4026, reducedSource695] using sourceEq803 B hB

theorem rowSound695_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row695 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck695, numericCheck695, reducedZero695 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e_oai
