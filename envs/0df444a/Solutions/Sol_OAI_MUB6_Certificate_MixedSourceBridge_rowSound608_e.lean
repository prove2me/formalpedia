-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:03:26.383431+00:00
-- url     : https://prove2.me/submissions/2d63e36f-7a14-4c90-ba28-23ff7b0abccf

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11832 raw11832Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11832 raw11832Labels = mixedMoment B raw11832step0 raw11832step0Labels := by
      have ha : raw11832step0 = (fun i j => raw11832 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11832step0 raw11832; decide +kernel
      have hl : raw11832step0Labels = raw11832Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11832 raw11832Labels permutation161 permutation7
    mixedMoment B raw11832step0 raw11832step0Labels = mixedMoment B raw11832step1 raw11832step1Labels := by
      have ha : raw11832step1 = -raw11832step0 := by apply Matrix.ext; change ∀ i j, raw11832step1 i j = -(raw11832step0 i j); unfold raw11832step1 raw11832step0; decide +kernel
      have hl : raw11832step1Labels = raw11832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11832step1 raw11832step1Labels = mixedMoment B raw11832step2 raw11832step2Labels := by
      have ha : raw11832step2 = raw11832step1 := by apply Matrix.ext; unfold raw11832step2 raw11832step1; decide +kernel
      have hl : raw11832step1Labels = labelEmbedding1 ∘ raw11832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11832step1 raw11832step1Labels raw11832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical11833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11833 raw11833Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11833 raw11833Labels = mixedMoment B raw11833step0 raw11833step0Labels := by
      have ha : raw11833step0 = (fun i j => raw11833 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11833step0 raw11833; decide +kernel
      have hl : raw11833step0Labels = raw11833Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11833 raw11833Labels permutation361 permutation5
    mixedMoment B raw11833step0 raw11833step0Labels = mixedMoment B raw11833step1 raw11833step1Labels := by
      have ha : raw11833step1 = -raw11833step0 := by apply Matrix.ext; change ∀ i j, raw11833step1 i j = -(raw11833step0 i j); unfold raw11833step1 raw11833step0; decide +kernel
      have hl : raw11833step1Labels = raw11833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11833step1 raw11833step1Labels = mixedMoment B raw11833step2 raw11833step2Labels := by
      have ha : raw11833step2 = raw11833step1 := by apply Matrix.ext; unfold raw11833step2 raw11833step1; decide +kernel
      have hl : raw11833step1Labels = labelEmbedding1 ∘ raw11833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11833step1 raw11833step1Labels raw11833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11834 raw11834Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11834 raw11834Labels = mixedMoment B raw11834step0 raw11834step0Labels := by
      have hz : ∀ j, raw11834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11834step0 = (fun i j => raw11834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11834step0 raw11834; decide +kernel
      have hl : raw11834step0Labels = raw11834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11834 raw11834Labels permutation434 hz
    mixedMoment B raw11834step0 raw11834step0Labels = mixedMoment B raw11834step1 raw11834step1Labels := by
      have ha : raw11834step1 = (fun i j => raw11834step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11834step1 raw11834step0; decide +kernel
      have hl : raw11834step1Labels = raw11834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11834step0 raw11834step0Labels permutation35 permutation7
    mixedMoment B raw11834step1 raw11834step1Labels = mixedMoment B raw11834step2 raw11834step2Labels := by
      have ha : raw11834step2 = -raw11834step1 := by apply Matrix.ext; change ∀ i j, raw11834step2 i j = -(raw11834step1 i j); unfold raw11834step2 raw11834step1; decide +kernel
      have hl : raw11834step2Labels = raw11834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11834step2 raw11834step2Labels = mixedMoment B raw11834step3 raw11834step3Labels := by
      have ha : raw11834step3 = raw11834step2 := by apply Matrix.ext; unfold raw11834step3 raw11834step2; decide +kernel
      have hl : raw11834step2Labels = labelEmbedding1 ∘ raw11834step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11834step2 raw11834step2Labels raw11834step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical11835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11835 raw11835Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11835 raw11835Labels = mixedMoment B raw11835step0 raw11835step0Labels := by
      have hz : ∀ j, raw11835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11835step0 = (fun i j => raw11835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11835step0 raw11835; decide +kernel
      have hl : raw11835step0Labels = raw11835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11835 raw11835Labels permutation520 hz
    mixedMoment B raw11835step0 raw11835step0Labels = mixedMoment B raw11835step1 raw11835step1Labels := by
      have ha : raw11835step1 = (fun i j => raw11835step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11835step1 raw11835step0; decide +kernel
      have hl : raw11835step1Labels = raw11835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11835step0 raw11835step0Labels permutation35 permutation7
    mixedMoment B raw11835step1 raw11835step1Labels = mixedMoment B raw11835step2 raw11835step2Labels := by
      have ha : raw11835step2 = -raw11835step1 := by apply Matrix.ext; change ∀ i j, raw11835step2 i j = -(raw11835step1 i j); unfold raw11835step2 raw11835step1; decide +kernel
      have hl : raw11835step2Labels = raw11835step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11835step2 raw11835step2Labels = mixedMoment B raw11835step3 raw11835step3Labels := by
      have ha : raw11835step3 = raw11835step2 := by apply Matrix.ext; unfold raw11835step3 raw11835step2; decide +kernel
      have hl : raw11835step2Labels = labelEmbedding1 ∘ raw11835step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11835step2 raw11835step2Labels raw11835step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical11836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11836 raw11836Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11836 raw11836Labels = mixedMoment B raw11836step0 raw11836step0Labels := by
      have ha : raw11836step0 = (fun i j => raw11836 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11836step0 raw11836; decide +kernel
      have hl : raw11836step0Labels = raw11836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11836 raw11836Labels permutation161 permutation7
    mixedMoment B raw11836step0 raw11836step0Labels = mixedMoment B raw11836step1 raw11836step1Labels := by
      have ha : raw11836step1 = -raw11836step0 := by apply Matrix.ext; change ∀ i j, raw11836step1 i j = -(raw11836step0 i j); unfold raw11836step1 raw11836step0; decide +kernel
      have hl : raw11836step1Labels = raw11836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11836step1 raw11836step1Labels = mixedMoment B raw11836step2 raw11836step2Labels := by
      have ha : raw11836step2 = raw11836step1 := by apply Matrix.ext; unfold raw11836step2 raw11836step1; decide +kernel
      have hl : raw11836step1Labels = labelEmbedding1 ∘ raw11836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11836step1 raw11836step1Labels raw11836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical11837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11837 raw11837Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw11837 raw11837Labels = mixedMoment B raw11837step0 raw11837step0Labels := by
      have ha : raw11837step0 = (fun i j => raw11837 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11837step0 raw11837; decide +kernel
      have hl : raw11837step0Labels = raw11837Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11837 raw11837Labels permutation197 permutation5
    mixedMoment B raw11837step0 raw11837step0Labels = mixedMoment B raw11837step1 raw11837step1Labels := by
      have ha : raw11837step1 = -raw11837step0 := by apply Matrix.ext; change ∀ i j, raw11837step1 i j = -(raw11837step0 i j); unfold raw11837step1 raw11837step0; decide +kernel
      have hl : raw11837step1Labels = raw11837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11837step1 raw11837step1Labels = mixedMoment B raw11837step2 raw11837step2Labels := by
      have ha : raw11837step2 = raw11837step1 := by apply Matrix.ext; unfold raw11837step2 raw11837step1; decide +kernel
      have hl : raw11837step1Labels = labelEmbedding1 ∘ raw11837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11837step1 raw11837step1Labels raw11837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3239 node3239Labels := by rfl

theorem canonical11838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11838 raw11838Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw11838 raw11838Labels = mixedMoment B raw11838step0 raw11838step0Labels := by
      have ha : raw11838step0 = (fun i j => raw11838 (permutation364 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11838step0 raw11838; decide +kernel
      have hl : raw11838step0Labels = raw11838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11838 raw11838Labels permutation364 permutation5
    mixedMoment B raw11838step0 raw11838step0Labels = mixedMoment B raw11838step1 raw11838step1Labels := by
      have ha : raw11838step1 = -raw11838step0 := by apply Matrix.ext; change ∀ i j, raw11838step1 i j = -(raw11838step0 i j); unfold raw11838step1 raw11838step0; decide +kernel
      have hl : raw11838step1Labels = raw11838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11838step1 raw11838step1Labels = mixedMoment B raw11838step2 raw11838step2Labels := by
      have ha : raw11838step2 = raw11838step1 := by apply Matrix.ext; unfold raw11838step2 raw11838step1; decide +kernel
      have hl : raw11838step1Labels = labelEmbedding1 ∘ raw11838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11838step1 raw11838step1Labels raw11838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2834 node2834Labels := by rfl

theorem canonical11839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11839 raw11839Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11839 raw11839Labels = mixedMoment B raw11839step0 raw11839step0Labels := by
      have hz : ∀ j, raw11839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11839step0 = (fun i j => raw11839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11839step0 raw11839; decide +kernel
      have hl : raw11839step0Labels = raw11839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11839 raw11839Labels permutation434 hz
    mixedMoment B raw11839step0 raw11839step0Labels = mixedMoment B raw11839step1 raw11839step1Labels := by
      have ha : raw11839step1 = (fun i j => raw11839step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11839step1 raw11839step0; decide +kernel
      have hl : raw11839step1Labels = raw11839step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11839step0 raw11839step0Labels permutation35 permutation7
    mixedMoment B raw11839step1 raw11839step1Labels = mixedMoment B raw11839step2 raw11839step2Labels := by
      have ha : raw11839step2 = -raw11839step1 := by apply Matrix.ext; change ∀ i j, raw11839step2 i j = -(raw11839step1 i j); unfold raw11839step2 raw11839step1; decide +kernel
      have hl : raw11839step2Labels = raw11839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11839step2 raw11839step2Labels = mixedMoment B raw11839step3 raw11839step3Labels := by
      have ha : raw11839step3 = raw11839step2 := by apply Matrix.ext; unfold raw11839step3 raw11839step2; decide +kernel
      have hl : raw11839step2Labels = labelEmbedding1 ∘ raw11839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11839step2 raw11839step2Labels raw11839step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical11840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11840 raw11840Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11840 raw11840Labels = mixedMoment B raw11840step0 raw11840step0Labels := by
      have hz : ∀ j, raw11840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11840step0 = (fun i j => raw11840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11840step0 raw11840; decide +kernel
      have hl : raw11840step0Labels = raw11840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11840 raw11840Labels permutation520 hz
    mixedMoment B raw11840step0 raw11840step0Labels = mixedMoment B raw11840step1 raw11840step1Labels := by
      have ha : raw11840step1 = (fun i j => raw11840step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11840step1 raw11840step0; decide +kernel
      have hl : raw11840step1Labels = raw11840step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11840step0 raw11840step0Labels permutation35 permutation7
    mixedMoment B raw11840step1 raw11840step1Labels = mixedMoment B raw11840step2 raw11840step2Labels := by
      have ha : raw11840step2 = -raw11840step1 := by apply Matrix.ext; change ∀ i j, raw11840step2 i j = -(raw11840step1 i j); unfold raw11840step2 raw11840step1; decide +kernel
      have hl : raw11840step2Labels = raw11840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11840step2 raw11840step2Labels = mixedMoment B raw11840step3 raw11840step3Labels := by
      have ha : raw11840step3 = raw11840step2 := by apply Matrix.ext; unfold raw11840step3 raw11840step2; decide +kernel
      have hl : raw11840step2Labels = labelEmbedding1 ∘ raw11840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11840step2 raw11840step2Labels raw11840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical11841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11841 raw11841Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw11841 raw11841Labels = mixedMoment B raw11841step0 raw11841step0Labels := by
      have ha : raw11841step0 = (fun i j => raw11841 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11841step0 raw11841; decide +kernel
      have hl : raw11841step0Labels = raw11841Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11841 raw11841Labels permutation161 permutation7
    mixedMoment B raw11841step0 raw11841step0Labels = mixedMoment B raw11841step1 raw11841step1Labels := by
      have ha : raw11841step1 = -raw11841step0 := by apply Matrix.ext; change ∀ i j, raw11841step1 i j = -(raw11841step0 i j); unfold raw11841step1 raw11841step0; decide +kernel
      have hl : raw11841step1Labels = raw11841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11841step1 raw11841step1Labels = mixedMoment B raw11841step2 raw11841step2Labels := by
      have ha : raw11841step2 = raw11841step1 := by apply Matrix.ext; unfold raw11841step2 raw11841step1; decide +kernel
      have hl : raw11841step1Labels = labelEmbedding1 ∘ raw11841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11841step1 raw11841step1Labels raw11841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical11842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11842 raw11842Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw11842 raw11842Labels = mixedMoment B raw11842step0 raw11842step0Labels := by
      have ha : raw11842step0 = (fun i j => raw11842 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11842step0 raw11842; decide +kernel
      have hl : raw11842step0Labels = raw11842Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11842 raw11842Labels permutation161 permutation7
    mixedMoment B raw11842step0 raw11842step0Labels = mixedMoment B raw11842step1 raw11842step1Labels := by
      have ha : raw11842step1 = -raw11842step0 := by apply Matrix.ext; change ∀ i j, raw11842step1 i j = -(raw11842step0 i j); unfold raw11842step1 raw11842step0; decide +kernel
      have hl : raw11842step1Labels = raw11842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11842step1 raw11842step1Labels = mixedMoment B raw11842step2 raw11842step2Labels := by
      have ha : raw11842step2 = raw11842step1 := by apply Matrix.ext; unfold raw11842step2 raw11842step1; decide +kernel
      have hl : raw11842step1Labels = labelEmbedding1 ∘ raw11842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11842step1 raw11842step1Labels raw11842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical11843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11843 raw11843Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw11843 raw11843Labels = mixedMoment B raw11843step0 raw11843step0Labels := by
      have ha : raw11843step0 = (fun i j => raw11843 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11843step0 raw11843; decide +kernel
      have hl : raw11843step0Labels = raw11843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11843 raw11843Labels permutation161 permutation7
    mixedMoment B raw11843step0 raw11843step0Labels = mixedMoment B raw11843step1 raw11843step1Labels := by
      have ha : raw11843step1 = -raw11843step0 := by apply Matrix.ext; change ∀ i j, raw11843step1 i j = -(raw11843step0 i j); unfold raw11843step1 raw11843step0; decide +kernel
      have hl : raw11843step1Labels = raw11843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11843step1 raw11843step1Labels = mixedMoment B raw11843step2 raw11843step2Labels := by
      have ha : raw11843step2 = raw11843step1 := by apply Matrix.ext; unfold raw11843step2 raw11843step1; decide +kernel
      have hl : raw11843step1Labels = labelEmbedding1 ∘ raw11843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11843step1 raw11843step1Labels raw11843step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical11844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11844 raw11844Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11844 raw11844Labels = mixedMoment B raw11844step0 raw11844step0Labels := by
      have hz : ∀ j, raw11844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11844step0 = (fun i j => raw11844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11844step0 raw11844; decide +kernel
      have hl : raw11844step0Labels = raw11844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11844 raw11844Labels permutation434 hz
    mixedMoment B raw11844step0 raw11844step0Labels = mixedMoment B raw11844step1 raw11844step1Labels := by
      have ha : raw11844step1 = (fun i j => raw11844step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11844step1 raw11844step0; decide +kernel
      have hl : raw11844step1Labels = raw11844step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11844step0 raw11844step0Labels permutation35 permutation7
    mixedMoment B raw11844step1 raw11844step1Labels = mixedMoment B raw11844step2 raw11844step2Labels := by
      have ha : raw11844step2 = -raw11844step1 := by apply Matrix.ext; change ∀ i j, raw11844step2 i j = -(raw11844step1 i j); unfold raw11844step2 raw11844step1; decide +kernel
      have hl : raw11844step2Labels = raw11844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11844step2 raw11844step2Labels = mixedMoment B raw11844step3 raw11844step3Labels := by
      have ha : raw11844step3 = raw11844step2 := by apply Matrix.ext; unfold raw11844step3 raw11844step2; decide +kernel
      have hl : raw11844step2Labels = labelEmbedding1 ∘ raw11844step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11844step2 raw11844step2Labels raw11844step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical11845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11845 raw11845Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11845 raw11845Labels = mixedMoment B raw11845step0 raw11845step0Labels := by
      have hz : ∀ j, raw11845 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11845step0 = (fun i j => raw11845 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11845step0 raw11845; decide +kernel
      have hl : raw11845step0Labels = raw11845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11845 raw11845Labels permutation520 hz
    mixedMoment B raw11845step0 raw11845step0Labels = mixedMoment B raw11845step1 raw11845step1Labels := by
      have ha : raw11845step1 = (fun i j => raw11845step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11845step1 raw11845step0; decide +kernel
      have hl : raw11845step1Labels = raw11845step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11845step0 raw11845step0Labels permutation35 permutation7
    mixedMoment B raw11845step1 raw11845step1Labels = mixedMoment B raw11845step2 raw11845step2Labels := by
      have ha : raw11845step2 = -raw11845step1 := by apply Matrix.ext; change ∀ i j, raw11845step2 i j = -(raw11845step1 i j); unfold raw11845step2 raw11845step1; decide +kernel
      have hl : raw11845step2Labels = raw11845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11845step2 raw11845step2Labels = mixedMoment B raw11845step3 raw11845step3Labels := by
      have ha : raw11845step3 = raw11845step2 := by apply Matrix.ext; unfold raw11845step3 raw11845step2; decide +kernel
      have hl : raw11845step2Labels = labelEmbedding1 ∘ raw11845step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11845step2 raw11845step2Labels raw11845step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical11846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11846 raw11846Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11846 raw11846Labels = mixedMoment B raw11846step0 raw11846step0Labels := by
      have ha : raw11846step0 = (fun i j => raw11846 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11846step0 raw11846; decide +kernel
      have hl : raw11846step0Labels = raw11846Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11846 raw11846Labels permutation161 permutation7
    mixedMoment B raw11846step0 raw11846step0Labels = mixedMoment B raw11846step1 raw11846step1Labels := by
      have ha : raw11846step1 = -raw11846step0 := by apply Matrix.ext; change ∀ i j, raw11846step1 i j = -(raw11846step0 i j); unfold raw11846step1 raw11846step0; decide +kernel
      have hl : raw11846step1Labels = raw11846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11846step1 raw11846step1Labels = mixedMoment B raw11846step2 raw11846step2Labels := by
      have ha : raw11846step2 = raw11846step1 := by apply Matrix.ext; unfold raw11846step2 raw11846step1; decide +kernel
      have hl : raw11846step1Labels = labelEmbedding1 ∘ raw11846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11846step1 raw11846step1Labels raw11846step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical11847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11847 raw11847Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw11847 raw11847Labels = mixedMoment B raw11847step0 raw11847step0Labels := by
      have ha : raw11847step0 = (fun i j => raw11847 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11847step0 raw11847; decide +kernel
      have hl : raw11847step0Labels = raw11847Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11847 raw11847Labels permutation195 permutation5
    mixedMoment B raw11847step0 raw11847step0Labels = mixedMoment B raw11847step1 raw11847step1Labels := by
      have ha : raw11847step1 = -raw11847step0 := by apply Matrix.ext; change ∀ i j, raw11847step1 i j = -(raw11847step0 i j); unfold raw11847step1 raw11847step0; decide +kernel
      have hl : raw11847step1Labels = raw11847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11847step1 raw11847step1Labels = mixedMoment B raw11847step2 raw11847step2Labels := by
      have ha : raw11847step2 = raw11847step1 := by apply Matrix.ext; unfold raw11847step2 raw11847step1; decide +kernel
      have hl : raw11847step1Labels = labelEmbedding1 ∘ raw11847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11847step1 raw11847step1Labels raw11847step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3238 node3238Labels := by rfl

theorem canonical11848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11848 raw11848Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw11848 raw11848Labels = mixedMoment B raw11848step0 raw11848step0Labels := by
      have ha : raw11848step0 = (fun i j => raw11848 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11848step0 raw11848; decide +kernel
      have hl : raw11848step0Labels = raw11848Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11848 raw11848Labels permutation167 permutation7
    mixedMoment B raw11848step0 raw11848step0Labels = mixedMoment B raw11848step1 raw11848step1Labels := by
      have ha : raw11848step1 = -raw11848step0 := by apply Matrix.ext; change ∀ i j, raw11848step1 i j = -(raw11848step0 i j); unfold raw11848step1 raw11848step0; decide +kernel
      have hl : raw11848step1Labels = raw11848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11848step1 raw11848step1Labels = mixedMoment B raw11848step2 raw11848step2Labels := by
      have ha : raw11848step2 = raw11848step1 := by apply Matrix.ext; unfold raw11848step2 raw11848step1; decide +kernel
      have hl : raw11848step1Labels = labelEmbedding1 ∘ raw11848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11848step1 raw11848step1Labels raw11848step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical11849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11849 raw11849Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11849 raw11849Labels = mixedMoment B raw11849step0 raw11849step0Labels := by
      have ha : raw11849step0 = (fun i j => raw11849 (permutation362 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11849step0 raw11849; decide +kernel
      have hl : raw11849step0Labels = raw11849Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11849 raw11849Labels permutation362 permutation5
    mixedMoment B raw11849step0 raw11849step0Labels = mixedMoment B raw11849step1 raw11849step1Labels := by
      have ha : raw11849step1 = -raw11849step0 := by apply Matrix.ext; change ∀ i j, raw11849step1 i j = -(raw11849step0 i j); unfold raw11849step1 raw11849step0; decide +kernel
      have hl : raw11849step1Labels = raw11849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11849step1 raw11849step1Labels = mixedMoment B raw11849step2 raw11849step2Labels := by
      have ha : raw11849step2 = raw11849step1 := by apply Matrix.ext; unfold raw11849step2 raw11849step1; decide +kernel
      have hl : raw11849step1Labels = labelEmbedding1 ∘ raw11849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11849step1 raw11849step1Labels raw11849step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2833 node2833Labels := by rfl

theorem canonical11850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11850 raw11850Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw11850 raw11850Labels = mixedMoment B raw11850step0 raw11850step0Labels := by
      have hz : ∀ j, raw11850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11850step0 = (fun i j => raw11850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11850step0 raw11850; decide +kernel
      have hl : raw11850step0Labels = raw11850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11850 raw11850Labels permutation520 hz
    mixedMoment B raw11850step0 raw11850step0Labels = mixedMoment B raw11850step1 raw11850step1Labels := by
      have ha : raw11850step1 = (fun i j => raw11850step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11850step1 raw11850step0; decide +kernel
      have hl : raw11850step1Labels = raw11850step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11850step0 raw11850step0Labels permutation35 permutation7
    mixedMoment B raw11850step1 raw11850step1Labels = mixedMoment B raw11850step2 raw11850step2Labels := by
      have ha : raw11850step2 = -raw11850step1 := by apply Matrix.ext; change ∀ i j, raw11850step2 i j = -(raw11850step1 i j); unfold raw11850step2 raw11850step1; decide +kernel
      have hl : raw11850step2Labels = raw11850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11850step2 raw11850step2Labels = mixedMoment B raw11850step3 raw11850step3Labels := by
      have ha : raw11850step3 = raw11850step2 := by apply Matrix.ext; unfold raw11850step3 raw11850step2; decide +kernel
      have hl : raw11850step2Labels = labelEmbedding1 ∘ raw11850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11850step2 raw11850step2Labels raw11850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical11851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11851 raw11851Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11851 raw11851Labels = mixedMoment B raw11851step0 raw11851step0Labels := by
      have ha : raw11851step0 = (fun i j => raw11851 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11851step0 raw11851; decide +kernel
      have hl : raw11851step0Labels = raw11851Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11851 raw11851Labels permutation167 permutation7
    mixedMoment B raw11851step0 raw11851step0Labels = mixedMoment B raw11851step1 raw11851step1Labels := by
      have ha : raw11851step1 = -raw11851step0 := by apply Matrix.ext; change ∀ i j, raw11851step1 i j = -(raw11851step0 i j); unfold raw11851step1 raw11851step0; decide +kernel
      have hl : raw11851step1Labels = raw11851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11851step1 raw11851step1Labels = mixedMoment B raw11851step2 raw11851step2Labels := by
      have ha : raw11851step2 = raw11851step1 := by apply Matrix.ext; unfold raw11851step2 raw11851step1; decide +kernel
      have hl : raw11851step1Labels = labelEmbedding1 ∘ raw11851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11851step1 raw11851step1Labels raw11851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical11852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11852 raw11852Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw11852 raw11852Labels = mixedMoment B raw11852step0 raw11852step0Labels := by
      have ha : raw11852step0 = (fun i j => raw11852 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11852step0 raw11852; decide +kernel
      have hl : raw11852step0Labels = raw11852Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11852 raw11852Labels permutation194 permutation5
    mixedMoment B raw11852step0 raw11852step0Labels = mixedMoment B raw11852step1 raw11852step1Labels := by
      have ha : raw11852step1 = -raw11852step0 := by apply Matrix.ext; change ∀ i j, raw11852step1 i j = -(raw11852step0 i j); unfold raw11852step1 raw11852step0; decide +kernel
      have hl : raw11852step1Labels = raw11852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11852step1 raw11852step1Labels = mixedMoment B raw11852step2 raw11852step2Labels := by
      have ha : raw11852step2 = raw11852step1 := by apply Matrix.ext; unfold raw11852step2 raw11852step1; decide +kernel
      have hl : raw11852step1Labels = labelEmbedding1 ∘ raw11852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11852step1 raw11852step1Labels raw11852step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3238 node3238Labels := by rfl

theorem canonical11853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11853 raw11853Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw11853 raw11853Labels = mixedMoment B raw11853step0 raw11853step0Labels := by
      have ha : raw11853step0 = (fun i j => raw11853 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11853step0 raw11853; decide +kernel
      have hl : raw11853step0Labels = raw11853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11853 raw11853Labels permutation161 permutation7
    mixedMoment B raw11853step0 raw11853step0Labels = mixedMoment B raw11853step1 raw11853step1Labels := by
      have ha : raw11853step1 = -raw11853step0 := by apply Matrix.ext; change ∀ i j, raw11853step1 i j = -(raw11853step0 i j); unfold raw11853step1 raw11853step0; decide +kernel
      have hl : raw11853step1Labels = raw11853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11853step1 raw11853step1Labels = mixedMoment B raw11853step2 raw11853step2Labels := by
      have ha : raw11853step2 = raw11853step1 := by apply Matrix.ext; unfold raw11853step2 raw11853step1; decide +kernel
      have hl : raw11853step1Labels = labelEmbedding1 ∘ raw11853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11853step1 raw11853step1Labels raw11853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical11854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11854 raw11854Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw11854 raw11854Labels = mixedMoment B raw11854step0 raw11854step0Labels := by
      have ha : raw11854step0 = (fun i j => raw11854 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11854step0 raw11854; decide +kernel
      have hl : raw11854step0Labels = raw11854Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11854 raw11854Labels permutation361 permutation5
    mixedMoment B raw11854step0 raw11854step0Labels = mixedMoment B raw11854step1 raw11854step1Labels := by
      have ha : raw11854step1 = -raw11854step0 := by apply Matrix.ext; change ∀ i j, raw11854step1 i j = -(raw11854step0 i j); unfold raw11854step1 raw11854step0; decide +kernel
      have hl : raw11854step1Labels = raw11854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11854step1 raw11854step1Labels = mixedMoment B raw11854step2 raw11854step2Labels := by
      have ha : raw11854step2 = raw11854step1 := by apply Matrix.ext; unfold raw11854step2 raw11854step1; decide +kernel
      have hl : raw11854step1Labels = labelEmbedding1 ∘ raw11854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11854step1 raw11854step1Labels raw11854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2833 node2833Labels := by rfl

theorem canonical11855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11855 raw11855Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw11855 raw11855Labels = mixedMoment B raw11855step0 raw11855step0Labels := by
      have hz : ∀ j, raw11855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11855step0 = (fun i j => raw11855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11855step0 raw11855; decide +kernel
      have hl : raw11855step0Labels = raw11855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11855 raw11855Labels permutation434 hz
    mixedMoment B raw11855step0 raw11855step0Labels = mixedMoment B raw11855step1 raw11855step1Labels := by
      have ha : raw11855step1 = (fun i j => raw11855step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11855step1 raw11855step0; decide +kernel
      have hl : raw11855step1Labels = raw11855step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11855step0 raw11855step0Labels permutation35 permutation7
    mixedMoment B raw11855step1 raw11855step1Labels = mixedMoment B raw11855step2 raw11855step2Labels := by
      have ha : raw11855step2 = -raw11855step1 := by apply Matrix.ext; change ∀ i j, raw11855step2 i j = -(raw11855step1 i j); unfold raw11855step2 raw11855step1; decide +kernel
      have hl : raw11855step2Labels = raw11855step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11855step2 raw11855step2Labels = mixedMoment B raw11855step3 raw11855step3Labels := by
      have ha : raw11855step3 = raw11855step2 := by apply Matrix.ext; unfold raw11855step3 raw11855step2; decide +kernel
      have hl : raw11855step2Labels = labelEmbedding1 ∘ raw11855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11855step2 raw11855step2Labels raw11855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical11856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11856 raw11856Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11856 raw11856Labels = mixedMoment B raw11856step0 raw11856step0Labels := by
      have ha : raw11856step0 = (fun i j => raw11856 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11856step0 raw11856; decide +kernel
      have hl : raw11856step0Labels = raw11856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11856 raw11856Labels permutation161 permutation7
    mixedMoment B raw11856step0 raw11856step0Labels = mixedMoment B raw11856step1 raw11856step1Labels := by
      have ha : raw11856step1 = -raw11856step0 := by apply Matrix.ext; change ∀ i j, raw11856step1 i j = -(raw11856step0 i j); unfold raw11856step1 raw11856step0; decide +kernel
      have hl : raw11856step1Labels = raw11856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11856step1 raw11856step1Labels = mixedMoment B raw11856step2 raw11856step2Labels := by
      have ha : raw11856step2 = raw11856step1 := by apply Matrix.ext; unfold raw11856step2 raw11856step1; decide +kernel
      have hl : raw11856step1Labels = labelEmbedding1 ∘ raw11856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11856step1 raw11856step1Labels raw11856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical11857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11857 raw11857Labels = mixedMoment B node3241 node3241Labels := by
  calc
    mixedMoment B raw11857 raw11857Labels = mixedMoment B raw11857step0 raw11857step0Labels := by
      have ha : raw11857step0 = (fun i j => raw11857 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11857step0 raw11857; decide +kernel
      have hl : raw11857step0Labels = raw11857Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11857 raw11857Labels permutation176 permutation5
    mixedMoment B raw11857step0 raw11857step0Labels = mixedMoment B raw11857step1 raw11857step1Labels := by
      have ha : raw11857step1 = -raw11857step0 := by apply Matrix.ext; change ∀ i j, raw11857step1 i j = -(raw11857step0 i j); unfold raw11857step1 raw11857step0; decide +kernel
      have hl : raw11857step1Labels = raw11857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11857step1 raw11857step1Labels = mixedMoment B raw11857step2 raw11857step2Labels := by
      have ha : raw11857step2 = raw11857step1 := by apply Matrix.ext; unfold raw11857step2 raw11857step1; decide +kernel
      have hl : raw11857step1Labels = labelEmbedding1 ∘ raw11857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11857step1 raw11857step1Labels raw11857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3241 node3241Labels := by rfl

theorem canonical11858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11858 raw11858Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw11858 raw11858Labels = mixedMoment B raw11858step0 raw11858step0Labels := by
      have ha : raw11858step0 = (fun i j => raw11858 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11858step0 raw11858; decide +kernel
      have hl : raw11858step0Labels = raw11858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11858 raw11858Labels permutation161 permutation7
    mixedMoment B raw11858step0 raw11858step0Labels = mixedMoment B raw11858step1 raw11858step1Labels := by
      have ha : raw11858step1 = -raw11858step0 := by apply Matrix.ext; change ∀ i j, raw11858step1 i j = -(raw11858step0 i j); unfold raw11858step1 raw11858step0; decide +kernel
      have hl : raw11858step1Labels = raw11858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11858step1 raw11858step1Labels = mixedMoment B raw11858step2 raw11858step2Labels := by
      have ha : raw11858step2 = raw11858step1 := by apply Matrix.ext; unfold raw11858step2 raw11858step1; decide +kernel
      have hl : raw11858step1Labels = labelEmbedding1 ∘ raw11858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11858step1 raw11858step1Labels raw11858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

theorem canonical11859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11859 raw11859Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw11859 raw11859Labels = mixedMoment B raw11859step0 raw11859step0Labels := by
      have ha : raw11859step0 = (fun i j => raw11859 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11859step0 raw11859; decide +kernel
      have hl : raw11859step0Labels = raw11859Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11859 raw11859Labels permutation346 permutation5
    mixedMoment B raw11859step0 raw11859step0Labels = mixedMoment B raw11859step1 raw11859step1Labels := by
      have ha : raw11859step1 = -raw11859step0 := by apply Matrix.ext; change ∀ i j, raw11859step1 i j = -(raw11859step0 i j); unfold raw11859step1 raw11859step0; decide +kernel
      have hl : raw11859step1Labels = raw11859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11859step1 raw11859step1Labels = mixedMoment B raw11859step2 raw11859step2Labels := by
      have ha : raw11859step2 = raw11859step1 := by apply Matrix.ext; unfold raw11859step2 raw11859step1; decide +kernel
      have hl : raw11859step1Labels = labelEmbedding1 ∘ raw11859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11859step1 raw11859step1Labels raw11859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2836 node2836Labels := by rfl

theorem canonical11860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11860 raw11860Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11860 raw11860Labels = mixedMoment B raw11860step0 raw11860step0Labels := by
      have hz : ∀ j, raw11860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11860step0 = (fun i j => raw11860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11860step0 raw11860; decide +kernel
      have hl : raw11860step0Labels = raw11860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11860 raw11860Labels permutation434 hz
    mixedMoment B raw11860step0 raw11860step0Labels = mixedMoment B raw11860step1 raw11860step1Labels := by
      have ha : raw11860step1 = (fun i j => raw11860step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11860step1 raw11860step0; decide +kernel
      have hl : raw11860step1Labels = raw11860step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11860step0 raw11860step0Labels permutation35 permutation7
    mixedMoment B raw11860step1 raw11860step1Labels = mixedMoment B raw11860step2 raw11860step2Labels := by
      have ha : raw11860step2 = -raw11860step1 := by apply Matrix.ext; change ∀ i j, raw11860step2 i j = -(raw11860step1 i j); unfold raw11860step2 raw11860step1; decide +kernel
      have hl : raw11860step2Labels = raw11860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11860step2 raw11860step2Labels = mixedMoment B raw11860step3 raw11860step3Labels := by
      have ha : raw11860step3 = raw11860step2 := by apply Matrix.ext; unfold raw11860step3 raw11860step2; decide +kernel
      have hl : raw11860step2Labels = labelEmbedding1 ∘ raw11860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11860step2 raw11860step2Labels raw11860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical11861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11861 raw11861Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11861 raw11861Labels = mixedMoment B raw11861step0 raw11861step0Labels := by
      have hz : ∀ j, raw11861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11861step0 = (fun i j => raw11861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11861step0 raw11861; decide +kernel
      have hl : raw11861step0Labels = raw11861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11861 raw11861Labels permutation520 hz
    mixedMoment B raw11861step0 raw11861step0Labels = mixedMoment B raw11861step1 raw11861step1Labels := by
      have ha : raw11861step1 = (fun i j => raw11861step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11861step1 raw11861step0; decide +kernel
      have hl : raw11861step1Labels = raw11861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11861step0 raw11861step0Labels permutation35 permutation7
    mixedMoment B raw11861step1 raw11861step1Labels = mixedMoment B raw11861step2 raw11861step2Labels := by
      have ha : raw11861step2 = -raw11861step1 := by apply Matrix.ext; change ∀ i j, raw11861step2 i j = -(raw11861step1 i j); unfold raw11861step2 raw11861step1; decide +kernel
      have hl : raw11861step2Labels = raw11861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11861step2 raw11861step2Labels = mixedMoment B raw11861step3 raw11861step3Labels := by
      have ha : raw11861step3 = raw11861step2 := by apply Matrix.ext; unfold raw11861step3 raw11861step2; decide +kernel
      have hl : raw11861step2Labels = labelEmbedding1 ∘ raw11861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11861step2 raw11861step2Labels raw11861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

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

theorem sound3238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3238 node3238Labels = Sparse.eval nodeValue3238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3238) = mixedMoment B node3238 node3238Labels := rfl
  simpa [nodeValue3238, Sparse.eval] using hc.symm

theorem sound3239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3239 node3239Labels = Sparse.eval nodeValue3239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3239) = mixedMoment B node3239 node3239Labels := rfl
  simpa [nodeValue3239, Sparse.eval] using hc.symm

theorem sound3241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3241 node3241Labels = Sparse.eval nodeValue3241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3241) = mixedMoment B node3241 node3241Labels := rfl
  simpa [nodeValue3241, Sparse.eval] using hc.symm

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

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

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

theorem sound3461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3461 node3461Labels = Sparse.eval nodeValue3461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3461) = mixedMoment B node3461 node3461Labels := rfl
  simpa [nodeValue3461, Sparse.eval] using hc.symm

theorem sound3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3464 node3464Labels = Sparse.eval nodeValue3464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3464) = mixedMoment B node3464 node3464Labels := rfl
  simpa [nodeValue3464, Sparse.eval] using hc.symm

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

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3528 node3528Labels = Sparse.eval nodeValue3528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3528) = mixedMoment B node3528 node3528Labels := rfl
  simpa [nodeValue3528, Sparse.eval] using hc.symm

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

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3567 node3567Labels = Sparse.eval nodeValue3567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3567) = mixedMoment B node3567 node3567Labels := rfl
  simpa [nodeValue3567, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

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

theorem sourceEq701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm701 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA701 + difference 0 1) (sourceB701 + difference 1 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA701 + difference 0 1) (sourceB701 + difference 1 0) sourceC701) = raw11832 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11832; decide +kernel
    rw [ha]
    exact (canonical11832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA701 + difference 0 2) (sourceB701 + difference 2 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA701 + difference 0 2) (sourceB701 + difference 2 0) sourceC701) = raw11833 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11833; decide +kernel
    rw [ha]
    exact (canonical11833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA701 + difference 0 3) (sourceB701 + difference 3 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA701 + difference 0 3) (sourceB701 + difference 3 0) sourceC701) = raw11834 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11834; decide +kernel
    rw [ha]
    exact (canonical11834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA701 + difference 0 4) (sourceB701 + difference 4 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA701 + difference 0 4) (sourceB701 + difference 4 0) sourceC701) = raw11835 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11835; decide +kernel
    rw [ha]
    exact (canonical11835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA701 + difference 0 5) (sourceB701 + difference 5 0) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA701 + difference 0 5) (sourceB701 + difference 5 0) sourceC701) = raw11836 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11836; decide +kernel
    rw [ha]
    exact (canonical11836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA701 + difference 1 0) (sourceB701 + difference 0 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA701 + difference 1 0) (sourceB701 + difference 0 1) sourceC701) = raw11837 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11837; decide +kernel
    rw [ha]
    exact (canonical11837 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA701 + difference 1 2) (sourceB701 + difference 2 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA701 + difference 1 2) (sourceB701 + difference 2 1) sourceC701) = raw11838 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11838; decide +kernel
    rw [ha]
    exact (canonical11838 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA701 + difference 1 3) (sourceB701 + difference 3 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA701 + difference 1 3) (sourceB701 + difference 3 1) sourceC701) = raw11839 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11839; decide +kernel
    rw [ha]
    exact (canonical11839 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA701 + difference 1 4) (sourceB701 + difference 4 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA701 + difference 1 4) (sourceB701 + difference 4 1) sourceC701) = raw11840 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11840; decide +kernel
    rw [ha]
    exact (canonical11840 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA701 + difference 1 5) (sourceB701 + difference 5 1) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA701 + difference 1 5) (sourceB701 + difference 5 1) sourceC701) = raw11841 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11841; decide +kernel
    rw [ha]
    exact (canonical11841 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA701 + difference 2 0) (sourceB701 + difference 0 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA701 + difference 2 0) (sourceB701 + difference 0 2) sourceC701) = raw11842 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11842; decide +kernel
    rw [ha]
    exact (canonical11842 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA701 + difference 2 1) (sourceB701 + difference 1 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA701 + difference 2 1) (sourceB701 + difference 1 2) sourceC701) = raw11843 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11843; decide +kernel
    rw [ha]
    exact (canonical11843 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA701 + difference 2 3) (sourceB701 + difference 3 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA701 + difference 2 3) (sourceB701 + difference 3 2) sourceC701) = raw11844 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11844; decide +kernel
    rw [ha]
    exact (canonical11844 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA701 + difference 2 4) (sourceB701 + difference 4 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA701 + difference 2 4) (sourceB701 + difference 4 2) sourceC701) = raw11845 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11845; decide +kernel
    rw [ha]
    exact (canonical11845 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA701 + difference 2 5) (sourceB701 + difference 5 2) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA701 + difference 2 5) (sourceB701 + difference 5 2) sourceC701) = raw11846 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11846; decide +kernel
    rw [ha]
    exact (canonical11846 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA701 + difference 3 0) (sourceB701 + difference 0 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA701 + difference 3 0) (sourceB701 + difference 0 3) sourceC701) = raw11847 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11847; decide +kernel
    rw [ha]
    exact (canonical11847 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA701 + difference 3 1) (sourceB701 + difference 1 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA701 + difference 3 1) (sourceB701 + difference 1 3) sourceC701) = raw11848 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11848; decide +kernel
    rw [ha]
    exact (canonical11848 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA701 + difference 3 2) (sourceB701 + difference 2 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA701 + difference 3 2) (sourceB701 + difference 2 3) sourceC701) = raw11849 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11849; decide +kernel
    rw [ha]
    exact (canonical11849 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA701 + difference 3 4) (sourceB701 + difference 4 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA701 + difference 3 4) (sourceB701 + difference 4 3) sourceC701) = raw11850 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11850; decide +kernel
    rw [ha]
    exact (canonical11850 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA701 + difference 3 5) (sourceB701 + difference 5 3) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA701 + difference 3 5) (sourceB701 + difference 5 3) sourceC701) = raw11851 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11851; decide +kernel
    rw [ha]
    exact (canonical11851 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA701 + difference 4 0) (sourceB701 + difference 0 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA701 + difference 4 0) (sourceB701 + difference 0 4) sourceC701) = raw11852 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11852; decide +kernel
    rw [ha]
    exact (canonical11852 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA701 + difference 4 1) (sourceB701 + difference 1 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA701 + difference 4 1) (sourceB701 + difference 1 4) sourceC701) = raw11853 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11853; decide +kernel
    rw [ha]
    exact (canonical11853 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA701 + difference 4 2) (sourceB701 + difference 2 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA701 + difference 4 2) (sourceB701 + difference 2 4) sourceC701) = raw11854 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11854; decide +kernel
    rw [ha]
    exact (canonical11854 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA701 + difference 4 3) (sourceB701 + difference 3 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA701 + difference 4 3) (sourceB701 + difference 3 4) sourceC701) = raw11855 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11855; decide +kernel
    rw [ha]
    exact (canonical11855 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA701 + difference 4 5) (sourceB701 + difference 5 4) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA701 + difference 4 5) (sourceB701 + difference 5 4) sourceC701) = raw11856 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11856; decide +kernel
    rw [ha]
    exact (canonical11856 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA701 + difference 5 0) (sourceB701 + difference 0 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA701 + difference 5 0) (sourceB701 + difference 0 5) sourceC701) = raw11857 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11857; decide +kernel
    rw [ha]
    exact (canonical11857 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA701 + difference 5 1) (sourceB701 + difference 1 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA701 + difference 5 1) (sourceB701 + difference 1 5) sourceC701) = raw11858 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11858; decide +kernel
    rw [ha]
    exact (canonical11858 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA701 + difference 5 2) (sourceB701 + difference 2 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA701 + difference 5 2) (sourceB701 + difference 2 5) sourceC701) = raw11859 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11859; decide +kernel
    rw [ha]
    exact (canonical11859 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA701 + difference 5 3) (sourceB701 + difference 3 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA701 + difference 5 3) (sourceB701 + difference 3 5) sourceC701) = raw11860 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11860; decide +kernel
    rw [ha]
    exact (canonical11860 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA701 + difference 5 4) (sourceB701 + difference 4 5) sourceC701) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA701 + difference 5 4) (sourceB701 + difference 4 5) sourceC701) = raw11861 := by
      apply Matrix.ext; unfold tripleCharges sourceA701 sourceB701 sourceC701 difference raw11861; decide +kernel
    rw [ha]
    exact (canonical11861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA701 sourceB701 sourceC701
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm701, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck608 : Integer.Sparse.reindex keyMap MixedData.row608 = numericRow608 := by decide +kernel

theorem numericCheck608 (x : Master → ℝ) : Integer.Sparse.eval numericRow608 x =
    (864 : ℝ) * reducedSource608 x := by
  norm_num [numericRow608, reducedSource608, Integer.Sparse.eval, Sparse.eval, nodeValue2833, nodeValue2834, nodeValue2836, nodeValue3037, nodeValue3238, nodeValue3239, nodeValue3241, nodeValue3289, nodeValue3460, nodeValue3461, nodeValue3464, nodeValue3525, nodeValue3528, nodeValue3534, nodeValue3535, nodeValue3541, nodeValue3567, nodeValue3573, nodeValue3801, nodeValue3847, nodeValue3853]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource608 (mixedVector B) = 0 := by
  have h2833 : mixedVector B (Sum.inr 2833) = Sparse.eval nodeValue2833 (mixedVector B) := by
    change mixedMoment B node2833 node2833Labels = _
    exact sound2833 B hB hF
  have h2834 : mixedVector B (Sum.inr 2834) = Sparse.eval nodeValue2834 (mixedVector B) := by
    change mixedMoment B node2834 node2834Labels = _
    exact sound2834 B hB hF
  have h2836 : mixedVector B (Sum.inr 2836) = Sparse.eval nodeValue2836 (mixedVector B) := by
    change mixedMoment B node2836 node2836Labels = _
    exact sound2836 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  simpa only [sourceForm701, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2833, h2834, h2836, h3037, h3238, h3239, h3241, h3289, h3460, h3461, h3464, h3525, h3528, h3534, h3535, h3541, h3567, h3573, h3801, h3847, h3853, reducedSource608] using sourceEq701 B hB

theorem rowSound608_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row608 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck608, numericCheck608, reducedZero608 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e_oai
