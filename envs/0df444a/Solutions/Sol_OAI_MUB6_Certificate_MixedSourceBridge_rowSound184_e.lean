-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:08:25.77988+00:00
-- url     : https://prove2.me/submissions/7e8681ff-1df4-4639-90ba-88e74f672697

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3223_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3227_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5718 raw5718Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5718 raw5718Labels = mixedMoment B raw5718step0 raw5718step0Labels := by
      have hz : ∀ j, raw5718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5718step0 = (fun i j => raw5718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5718step0 raw5718; decide +kernel
      have hl : raw5718step0Labels = raw5718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5718 raw5718Labels permutation265 hz
    mixedMoment B raw5718step0 raw5718step0Labels = mixedMoment B raw5718step1 raw5718step1Labels := by
      have ha : raw5718step1 = (fun i j => raw5718step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5718step1 raw5718step0; decide +kernel
      have hl : raw5718step1Labels = raw5718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5718step0 raw5718step0Labels permutation32 permutation7
    mixedMoment B raw5718step1 raw5718step1Labels = mixedMoment B raw5718step2 raw5718step2Labels := by
      have ha : raw5718step2 = raw5718step1 := by apply Matrix.ext; unfold raw5718step2 raw5718step1; decide +kernel
      have hl : raw5718step1Labels = labelEmbedding1 ∘ raw5718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5718step1 raw5718step1Labels raw5718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical5719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5719 raw5719Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5719 raw5719Labels = mixedMoment B raw5719step0 raw5719step0Labels := by
      have hz : ∀ j, raw5719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5719step0 = (fun i j => raw5719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5719step0 raw5719; decide +kernel
      have hl : raw5719step0Labels = raw5719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5719 raw5719Labels permutation346 hz
    mixedMoment B raw5719step0 raw5719step0Labels = mixedMoment B raw5719step1 raw5719step1Labels := by
      have ha : raw5719step1 = (fun i j => raw5719step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5719step1 raw5719step0; decide +kernel
      have hl : raw5719step1Labels = raw5719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5719step0 raw5719step0Labels permutation32 permutation7
    mixedMoment B raw5719step1 raw5719step1Labels = mixedMoment B raw5719step2 raw5719step2Labels := by
      have ha : raw5719step2 = raw5719step1 := by apply Matrix.ext; unfold raw5719step2 raw5719step1; decide +kernel
      have hl : raw5719step1Labels = labelEmbedding1 ∘ raw5719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5719step1 raw5719step1Labels raw5719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical5720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5720 raw5720Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5720 raw5720Labels = mixedMoment B raw5720step0 raw5720step0Labels := by
      have hz : ∀ j, raw5720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5720step0 = (fun i j => raw5720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5720step0 raw5720; decide +kernel
      have hl : raw5720step0Labels = raw5720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5720 raw5720Labels permutation434 hz
    mixedMoment B raw5720step0 raw5720step0Labels = mixedMoment B raw5720step1 raw5720step1Labels := by
      have ha : raw5720step1 = (fun i j => raw5720step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5720step1 raw5720step0; decide +kernel
      have hl : raw5720step1Labels = raw5720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5720step0 raw5720step0Labels permutation32 permutation7
    mixedMoment B raw5720step1 raw5720step1Labels = mixedMoment B raw5720step2 raw5720step2Labels := by
      have ha : raw5720step2 = raw5720step1 := by apply Matrix.ext; unfold raw5720step2 raw5720step1; decide +kernel
      have hl : raw5720step1Labels = labelEmbedding1 ∘ raw5720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5720step1 raw5720step1Labels raw5720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical5721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5721 raw5721Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw5721 raw5721Labels = mixedMoment B raw5721step0 raw5721step0Labels := by
      have ha : raw5721step0 = (fun i j => raw5721 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5721step0 raw5721; decide +kernel
      have hl : raw5721step0Labels = raw5721Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5721 raw5721Labels permutation152 permutation7
    mixedMoment B raw5721step0 raw5721step0Labels = mixedMoment B raw5721step1 raw5721step1Labels := by
      have ha : raw5721step1 = raw5721step0 := by apply Matrix.ext; unfold raw5721step1 raw5721step0; decide +kernel
      have hl : raw5721step0Labels = labelEmbedding1 ∘ raw5721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5721step0 raw5721step0Labels raw5721step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

theorem canonical5722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5722 raw5722Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw5722 raw5722Labels = mixedMoment B raw5722step0 raw5722step0Labels := by
      have ha : raw5722step0 = (fun i j => raw5722 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5722step0 raw5722; decide +kernel
      have hl : raw5722step0Labels = raw5722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5722 raw5722Labels permutation152 permutation7
    mixedMoment B raw5722step0 raw5722step0Labels = mixedMoment B raw5722step1 raw5722step1Labels := by
      have ha : raw5722step1 = raw5722step0 := by apply Matrix.ext; unfold raw5722step1 raw5722step0; decide +kernel
      have hl : raw5722step0Labels = labelEmbedding1 ∘ raw5722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5722step0 raw5722step0Labels raw5722step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

theorem canonical5723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5723 raw5723Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5723 raw5723Labels = mixedMoment B raw5723step0 raw5723step0Labels := by
      have ha : raw5723step0 = (fun i j => raw5723 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5723step0 raw5723; decide +kernel
      have hl : raw5723step0Labels = raw5723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5723 raw5723Labels permutation263 permutation5
    mixedMoment B raw5723step0 raw5723step0Labels = mixedMoment B raw5723step1 raw5723step1Labels := by
      have ha : raw5723step1 = -raw5723step0 := by apply Matrix.ext; change ∀ i j, raw5723step1 i j = -(raw5723step0 i j); unfold raw5723step1 raw5723step0; decide +kernel
      have hl : raw5723step1Labels = raw5723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5723step1 raw5723step1Labels = mixedMoment B raw5723step2 raw5723step2Labels := by
      have ha : raw5723step2 = raw5723step1 := by apply Matrix.ext; unfold raw5723step2 raw5723step1; decide +kernel
      have hl : raw5723step1Labels = labelEmbedding1 ∘ raw5723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5723step1 raw5723step1Labels raw5723step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

theorem canonical5724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5724 raw5724Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5724 raw5724Labels = mixedMoment B raw5724step0 raw5724step0Labels := by
      have hz : ∀ j, raw5724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5724step0 = (fun i j => raw5724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5724step0 raw5724; decide +kernel
      have hl : raw5724step0Labels = raw5724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5724 raw5724Labels permutation346 hz
    mixedMoment B raw5724step0 raw5724step0Labels = mixedMoment B raw5724step1 raw5724step1Labels := by
      have ha : raw5724step1 = (fun i j => raw5724step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5724step1 raw5724step0; decide +kernel
      have hl : raw5724step1Labels = raw5724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5724step0 raw5724step0Labels permutation55 permutation5
    mixedMoment B raw5724step1 raw5724step1Labels = mixedMoment B raw5724step2 raw5724step2Labels := by
      have ha : raw5724step2 = -raw5724step1 := by apply Matrix.ext; change ∀ i j, raw5724step2 i j = -(raw5724step1 i j); unfold raw5724step2 raw5724step1; decide +kernel
      have hl : raw5724step2Labels = raw5724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5724step2 raw5724step2Labels = mixedMoment B raw5724step3 raw5724step3Labels := by
      have ha : raw5724step3 = raw5724step2 := by apply Matrix.ext; unfold raw5724step3 raw5724step2; decide +kernel
      have hl : raw5724step2Labels = labelEmbedding1 ∘ raw5724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5724step2 raw5724step2Labels raw5724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5725 raw5725Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5725 raw5725Labels = mixedMoment B raw5725step0 raw5725step0Labels := by
      have hz : ∀ j, raw5725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5725step0 = (fun i j => raw5725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5725step0 raw5725; decide +kernel
      have hl : raw5725step0Labels = raw5725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5725 raw5725Labels permutation434 hz
    mixedMoment B raw5725step0 raw5725step0Labels = mixedMoment B raw5725step1 raw5725step1Labels := by
      have ha : raw5725step1 = (fun i j => raw5725step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5725step1 raw5725step0; decide +kernel
      have hl : raw5725step1Labels = raw5725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5725step0 raw5725step0Labels permutation55 permutation5
    mixedMoment B raw5725step1 raw5725step1Labels = mixedMoment B raw5725step2 raw5725step2Labels := by
      have ha : raw5725step2 = -raw5725step1 := by apply Matrix.ext; change ∀ i j, raw5725step2 i j = -(raw5725step1 i j); unfold raw5725step2 raw5725step1; decide +kernel
      have hl : raw5725step2Labels = raw5725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5725step2 raw5725step2Labels = mixedMoment B raw5725step3 raw5725step3Labels := by
      have ha : raw5725step3 = raw5725step2 := by apply Matrix.ext; unfold raw5725step3 raw5725step2; decide +kernel
      have hl : raw5725step2Labels = labelEmbedding1 ∘ raw5725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5725step2 raw5725step2Labels raw5725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5726 raw5726Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5726 raw5726Labels = mixedMoment B raw5726step0 raw5726step0Labels := by
      have ha : raw5726step0 = (fun i j => raw5726 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5726step0 raw5726; decide +kernel
      have hl : raw5726step0Labels = raw5726Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5726 raw5726Labels permutation243 permutation5
    mixedMoment B raw5726step0 raw5726step0Labels = mixedMoment B raw5726step1 raw5726step1Labels := by
      have ha : raw5726step1 = -raw5726step0 := by apply Matrix.ext; change ∀ i j, raw5726step1 i j = -(raw5726step0 i j); unfold raw5726step1 raw5726step0; decide +kernel
      have hl : raw5726step1Labels = raw5726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5726step1 raw5726step1Labels = mixedMoment B raw5726step2 raw5726step2Labels := by
      have ha : raw5726step2 = raw5726step1 := by apply Matrix.ext; unfold raw5726step2 raw5726step1; decide +kernel
      have hl : raw5726step1Labels = labelEmbedding1 ∘ raw5726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5726step1 raw5726step1Labels raw5726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

theorem canonical5727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5727 raw5727Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5727 raw5727Labels = mixedMoment B raw5727step0 raw5727step0Labels := by
      have ha : raw5727step0 = (fun i j => raw5727 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5727step0 raw5727; decide +kernel
      have hl : raw5727step0Labels = raw5727Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5727 raw5727Labels permutation263 permutation5
    mixedMoment B raw5727step0 raw5727step0Labels = mixedMoment B raw5727step1 raw5727step1Labels := by
      have ha : raw5727step1 = -raw5727step0 := by apply Matrix.ext; change ∀ i j, raw5727step1 i j = -(raw5727step0 i j); unfold raw5727step1 raw5727step0; decide +kernel
      have hl : raw5727step1Labels = raw5727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5727step1 raw5727step1Labels = mixedMoment B raw5727step2 raw5727step2Labels := by
      have ha : raw5727step2 = raw5727step1 := by apply Matrix.ext; unfold raw5727step2 raw5727step1; decide +kernel
      have hl : raw5727step1Labels = labelEmbedding1 ∘ raw5727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5727step1 raw5727step1Labels raw5727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

theorem canonical5728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5728 raw5728Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5728 raw5728Labels = mixedMoment B raw5728step0 raw5728step0Labels := by
      have ha : raw5728step0 = (fun i j => raw5728 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5728step0 raw5728; decide +kernel
      have hl : raw5728step0Labels = raw5728Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5728 raw5728Labels permutation261 permutation5
    mixedMoment B raw5728step0 raw5728step0Labels = mixedMoment B raw5728step1 raw5728step1Labels := by
      have ha : raw5728step1 = -raw5728step0 := by apply Matrix.ext; change ∀ i j, raw5728step1 i j = -(raw5728step0 i j); unfold raw5728step1 raw5728step0; decide +kernel
      have hl : raw5728step1Labels = raw5728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5728step1 raw5728step1Labels = mixedMoment B raw5728step2 raw5728step2Labels := by
      have ha : raw5728step2 = raw5728step1 := by apply Matrix.ext; unfold raw5728step2 raw5728step1; decide +kernel
      have hl : raw5728step1Labels = labelEmbedding1 ∘ raw5728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5728step1 raw5728step1Labels raw5728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

theorem canonical5729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5729 raw5729Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5729 raw5729Labels = mixedMoment B raw5729step0 raw5729step0Labels := by
      have hz : ∀ j, raw5729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5729step0 = (fun i j => raw5729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5729step0 raw5729; decide +kernel
      have hl : raw5729step0Labels = raw5729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5729 raw5729Labels permutation265 hz
    mixedMoment B raw5729step0 raw5729step0Labels = mixedMoment B raw5729step1 raw5729step1Labels := by
      have ha : raw5729step1 = (fun i j => raw5729step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5729step1 raw5729step0; decide +kernel
      have hl : raw5729step1Labels = raw5729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5729step0 raw5729step0Labels permutation55 permutation5
    mixedMoment B raw5729step1 raw5729step1Labels = mixedMoment B raw5729step2 raw5729step2Labels := by
      have ha : raw5729step2 = -raw5729step1 := by apply Matrix.ext; change ∀ i j, raw5729step2 i j = -(raw5729step1 i j); unfold raw5729step2 raw5729step1; decide +kernel
      have hl : raw5729step2Labels = raw5729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5729step2 raw5729step2Labels = mixedMoment B raw5729step3 raw5729step3Labels := by
      have ha : raw5729step3 = raw5729step2 := by apply Matrix.ext; unfold raw5729step3 raw5729step2; decide +kernel
      have hl : raw5729step2Labels = labelEmbedding1 ∘ raw5729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5729step2 raw5729step2Labels raw5729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5730 raw5730Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5730 raw5730Labels = mixedMoment B raw5730step0 raw5730step0Labels := by
      have hz : ∀ j, raw5730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5730step0 = (fun i j => raw5730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5730step0 raw5730; decide +kernel
      have hl : raw5730step0Labels = raw5730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5730 raw5730Labels permutation434 hz
    mixedMoment B raw5730step0 raw5730step0Labels = mixedMoment B raw5730step1 raw5730step1Labels := by
      have ha : raw5730step1 = (fun i j => raw5730step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5730step1 raw5730step0; decide +kernel
      have hl : raw5730step1Labels = raw5730step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5730step0 raw5730step0Labels permutation54 permutation5
    mixedMoment B raw5730step1 raw5730step1Labels = mixedMoment B raw5730step2 raw5730step2Labels := by
      have ha : raw5730step2 = -raw5730step1 := by apply Matrix.ext; change ∀ i j, raw5730step2 i j = -(raw5730step1 i j); unfold raw5730step2 raw5730step1; decide +kernel
      have hl : raw5730step2Labels = raw5730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5730step2 raw5730step2Labels = mixedMoment B raw5730step3 raw5730step3Labels := by
      have ha : raw5730step3 = raw5730step2 := by apply Matrix.ext; unfold raw5730step3 raw5730step2; decide +kernel
      have hl : raw5730step2Labels = labelEmbedding1 ∘ raw5730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5730step2 raw5730step2Labels raw5730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5731 raw5731Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5731 raw5731Labels = mixedMoment B raw5731step0 raw5731step0Labels := by
      have ha : raw5731step0 = (fun i j => raw5731 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5731step0 raw5731; decide +kernel
      have hl : raw5731step0Labels = raw5731Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5731 raw5731Labels permutation241 permutation5
    mixedMoment B raw5731step0 raw5731step0Labels = mixedMoment B raw5731step1 raw5731step1Labels := by
      have ha : raw5731step1 = -raw5731step0 := by apply Matrix.ext; change ∀ i j, raw5731step1 i j = -(raw5731step0 i j); unfold raw5731step1 raw5731step0; decide +kernel
      have hl : raw5731step1Labels = raw5731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5731step1 raw5731step1Labels = mixedMoment B raw5731step2 raw5731step2Labels := by
      have ha : raw5731step2 = raw5731step1 := by apply Matrix.ext; unfold raw5731step2 raw5731step1; decide +kernel
      have hl : raw5731step1Labels = labelEmbedding1 ∘ raw5731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5731step1 raw5731step1Labels raw5731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

theorem canonical5732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5732 raw5732Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5732 raw5732Labels = mixedMoment B raw5732step0 raw5732step0Labels := by
      have ha : raw5732step0 = (fun i j => raw5732 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5732step0 raw5732; decide +kernel
      have hl : raw5732step0Labels = raw5732Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5732 raw5732Labels permutation261 permutation5
    mixedMoment B raw5732step0 raw5732step0Labels = mixedMoment B raw5732step1 raw5732step1Labels := by
      have ha : raw5732step1 = -raw5732step0 := by apply Matrix.ext; change ∀ i j, raw5732step1 i j = -(raw5732step0 i j); unfold raw5732step1 raw5732step0; decide +kernel
      have hl : raw5732step1Labels = raw5732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5732step1 raw5732step1Labels = mixedMoment B raw5732step2 raw5732step2Labels := by
      have ha : raw5732step2 = raw5732step1 := by apply Matrix.ext; unfold raw5732step2 raw5732step1; decide +kernel
      have hl : raw5732step1Labels = labelEmbedding1 ∘ raw5732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5732step1 raw5732step1Labels raw5732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

theorem canonical5733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5733 raw5733Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5733 raw5733Labels = mixedMoment B raw5733step0 raw5733step0Labels := by
      have ha : raw5733step0 = (fun i j => raw5733 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5733step0 raw5733; decide +kernel
      have hl : raw5733step0Labels = raw5733Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5733 raw5733Labels permutation260 permutation5
    mixedMoment B raw5733step0 raw5733step0Labels = mixedMoment B raw5733step1 raw5733step1Labels := by
      have ha : raw5733step1 = -raw5733step0 := by apply Matrix.ext; change ∀ i j, raw5733step1 i j = -(raw5733step0 i j); unfold raw5733step1 raw5733step0; decide +kernel
      have hl : raw5733step1Labels = raw5733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5733step1 raw5733step1Labels = mixedMoment B raw5733step2 raw5733step2Labels := by
      have ha : raw5733step2 = raw5733step1 := by apply Matrix.ext; unfold raw5733step2 raw5733step1; decide +kernel
      have hl : raw5733step1Labels = labelEmbedding1 ∘ raw5733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5733step1 raw5733step1Labels raw5733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

theorem canonical5734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5734 raw5734Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5734 raw5734Labels = mixedMoment B raw5734step0 raw5734step0Labels := by
      have hz : ∀ j, raw5734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5734step0 = (fun i j => raw5734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5734step0 raw5734; decide +kernel
      have hl : raw5734step0Labels = raw5734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5734 raw5734Labels permutation265 hz
    mixedMoment B raw5734step0 raw5734step0Labels = mixedMoment B raw5734step1 raw5734step1Labels := by
      have ha : raw5734step1 = (fun i j => raw5734step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5734step1 raw5734step0; decide +kernel
      have hl : raw5734step1Labels = raw5734step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5734step0 raw5734step0Labels permutation54 permutation5
    mixedMoment B raw5734step1 raw5734step1Labels = mixedMoment B raw5734step2 raw5734step2Labels := by
      have ha : raw5734step2 = -raw5734step1 := by apply Matrix.ext; change ∀ i j, raw5734step2 i j = -(raw5734step1 i j); unfold raw5734step2 raw5734step1; decide +kernel
      have hl : raw5734step2Labels = raw5734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5734step2 raw5734step2Labels = mixedMoment B raw5734step3 raw5734step3Labels := by
      have ha : raw5734step3 = raw5734step2 := by apply Matrix.ext; unfold raw5734step3 raw5734step2; decide +kernel
      have hl : raw5734step2Labels = labelEmbedding1 ∘ raw5734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5734step2 raw5734step2Labels raw5734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5735 raw5735Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5735 raw5735Labels = mixedMoment B raw5735step0 raw5735step0Labels := by
      have hz : ∀ j, raw5735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5735step0 = (fun i j => raw5735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5735step0 raw5735; decide +kernel
      have hl : raw5735step0Labels = raw5735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5735 raw5735Labels permutation346 hz
    mixedMoment B raw5735step0 raw5735step0Labels = mixedMoment B raw5735step1 raw5735step1Labels := by
      have ha : raw5735step1 = (fun i j => raw5735step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5735step1 raw5735step0; decide +kernel
      have hl : raw5735step1Labels = raw5735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5735step0 raw5735step0Labels permutation54 permutation5
    mixedMoment B raw5735step1 raw5735step1Labels = mixedMoment B raw5735step2 raw5735step2Labels := by
      have ha : raw5735step2 = -raw5735step1 := by apply Matrix.ext; change ∀ i j, raw5735step2 i j = -(raw5735step1 i j); unfold raw5735step2 raw5735step1; decide +kernel
      have hl : raw5735step2Labels = raw5735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5735step2 raw5735step2Labels = mixedMoment B raw5735step3 raw5735step3Labels := by
      have ha : raw5735step3 = raw5735step2 := by apply Matrix.ext; unfold raw5735step3 raw5735step2; decide +kernel
      have hl : raw5735step2Labels = labelEmbedding1 ∘ raw5735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5735step2 raw5735step2Labels raw5735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5736 raw5736Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5736 raw5736Labels = mixedMoment B raw5736step0 raw5736step0Labels := by
      have ha : raw5736step0 = (fun i j => raw5736 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5736step0 raw5736; decide +kernel
      have hl : raw5736step0Labels = raw5736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5736 raw5736Labels permutation240 permutation5
    mixedMoment B raw5736step0 raw5736step0Labels = mixedMoment B raw5736step1 raw5736step1Labels := by
      have ha : raw5736step1 = -raw5736step0 := by apply Matrix.ext; change ∀ i j, raw5736step1 i j = -(raw5736step0 i j); unfold raw5736step1 raw5736step0; decide +kernel
      have hl : raw5736step1Labels = raw5736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5736step1 raw5736step1Labels = mixedMoment B raw5736step2 raw5736step2Labels := by
      have ha : raw5736step2 = raw5736step1 := by apply Matrix.ext; unfold raw5736step2 raw5736step1; decide +kernel
      have hl : raw5736step1Labels = labelEmbedding1 ∘ raw5736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5736step1 raw5736step1Labels raw5736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

theorem canonical5737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5737 raw5737Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5737 raw5737Labels = mixedMoment B raw5737step0 raw5737step0Labels := by
      have ha : raw5737step0 = (fun i j => raw5737 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5737step0 raw5737; decide +kernel
      have hl : raw5737step0Labels = raw5737Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5737 raw5737Labels permutation260 permutation5
    mixedMoment B raw5737step0 raw5737step0Labels = mixedMoment B raw5737step1 raw5737step1Labels := by
      have ha : raw5737step1 = -raw5737step0 := by apply Matrix.ext; change ∀ i j, raw5737step1 i j = -(raw5737step0 i j); unfold raw5737step1 raw5737step0; decide +kernel
      have hl : raw5737step1Labels = raw5737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5737step1 raw5737step1Labels = mixedMoment B raw5737step2 raw5737step2Labels := by
      have ha : raw5737step2 = raw5737step1 := by apply Matrix.ext; unfold raw5737step2 raw5737step1; decide +kernel
      have hl : raw5737step1Labels = labelEmbedding1 ∘ raw5737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5737step1 raw5737step1Labels raw5737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

theorem canonical5738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5738 raw5738Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw5738 raw5738Labels = mixedMoment B raw5738step0 raw5738step0Labels := by
      have ha : raw5738step0 = (fun i j => raw5738 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5738step0 raw5738; decide +kernel
      have hl : raw5738step0Labels = raw5738Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5738 raw5738Labels permutation260 permutation5
    mixedMoment B raw5738step0 raw5738step0Labels = mixedMoment B raw5738step1 raw5738step1Labels := by
      have ha : raw5738step1 = -raw5738step0 := by apply Matrix.ext; change ∀ i j, raw5738step1 i j = -(raw5738step0 i j); unfold raw5738step1 raw5738step0; decide +kernel
      have hl : raw5738step1Labels = raw5738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5738step1 raw5738step1Labels = mixedMoment B raw5738step2 raw5738step2Labels := by
      have ha : raw5738step2 = raw5738step1 := by apply Matrix.ext; unfold raw5738step2 raw5738step1; decide +kernel
      have hl : raw5738step1Labels = labelEmbedding1 ∘ raw5738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5738step1 raw5738step1Labels raw5738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1366 node1366Labels := by rfl

theorem canonical5739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5739 raw5739Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5739 raw5739Labels = mixedMoment B raw5739step0 raw5739step0Labels := by
      have hz : ∀ j, raw5739 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5739step0 = (fun i j => raw5739 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5739step0 raw5739; decide +kernel
      have hl : raw5739step0Labels = raw5739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5739 raw5739Labels permutation265 hz
    mixedMoment B raw5739step0 raw5739step0Labels = mixedMoment B raw5739step1 raw5739step1Labels := by
      have ha : raw5739step1 = (fun i j => raw5739step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5739step1 raw5739step0; decide +kernel
      have hl : raw5739step1Labels = raw5739step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5739step0 raw5739step0Labels permutation54 permutation5
    mixedMoment B raw5739step1 raw5739step1Labels = mixedMoment B raw5739step2 raw5739step2Labels := by
      have ha : raw5739step2 = -raw5739step1 := by apply Matrix.ext; change ∀ i j, raw5739step2 i j = -(raw5739step1 i j); unfold raw5739step2 raw5739step1; decide +kernel
      have hl : raw5739step2Labels = raw5739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5739step2 raw5739step2Labels = mixedMoment B raw5739step3 raw5739step3Labels := by
      have ha : raw5739step3 = raw5739step2 := by apply Matrix.ext; unfold raw5739step3 raw5739step2; decide +kernel
      have hl : raw5739step2Labels = labelEmbedding1 ∘ raw5739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5739step2 raw5739step2Labels raw5739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical5740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5740 raw5740Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5740 raw5740Labels = mixedMoment B raw5740step0 raw5740step0Labels := by
      have hz : ∀ j, raw5740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5740step0 = (fun i j => raw5740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5740step0 raw5740; decide +kernel
      have hl : raw5740step0Labels = raw5740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5740 raw5740Labels permutation346 hz
    mixedMoment B raw5740step0 raw5740step0Labels = mixedMoment B raw5740step1 raw5740step1Labels := by
      have ha : raw5740step1 = (fun i j => raw5740step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5740step1 raw5740step0; decide +kernel
      have hl : raw5740step1Labels = raw5740step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5740step0 raw5740step0Labels permutation54 permutation5
    mixedMoment B raw5740step1 raw5740step1Labels = mixedMoment B raw5740step2 raw5740step2Labels := by
      have ha : raw5740step2 = -raw5740step1 := by apply Matrix.ext; change ∀ i j, raw5740step2 i j = -(raw5740step1 i j); unfold raw5740step2 raw5740step1; decide +kernel
      have hl : raw5740step2Labels = raw5740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5740step2 raw5740step2Labels = mixedMoment B raw5740step3 raw5740step3Labels := by
      have ha : raw5740step3 = raw5740step2 := by apply Matrix.ext; unfold raw5740step3 raw5740step2; decide +kernel
      have hl : raw5740step2Labels = labelEmbedding1 ∘ raw5740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5740step2 raw5740step2Labels raw5740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical5741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5741 raw5741Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5741 raw5741Labels = mixedMoment B raw5741step0 raw5741step0Labels := by
      have hz : ∀ j, raw5741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5741step0 = (fun i j => raw5741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5741step0 raw5741; decide +kernel
      have hl : raw5741step0Labels = raw5741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5741 raw5741Labels permutation434 hz
    mixedMoment B raw5741step0 raw5741step0Labels = mixedMoment B raw5741step1 raw5741step1Labels := by
      have ha : raw5741step1 = (fun i j => raw5741step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5741step1 raw5741step0; decide +kernel
      have hl : raw5741step1Labels = raw5741step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5741step0 raw5741step0Labels permutation54 permutation5
    mixedMoment B raw5741step1 raw5741step1Labels = mixedMoment B raw5741step2 raw5741step2Labels := by
      have ha : raw5741step2 = -raw5741step1 := by apply Matrix.ext; change ∀ i j, raw5741step2 i j = -(raw5741step1 i j); unfold raw5741step2 raw5741step1; decide +kernel
      have hl : raw5741step2Labels = raw5741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5741step2 raw5741step2Labels = mixedMoment B raw5741step3 raw5741step3Labels := by
      have ha : raw5741step3 = raw5741step2 := by apply Matrix.ext; unfold raw5741step3 raw5741step2; decide +kernel
      have hl : raw5741step2Labels = labelEmbedding1 ∘ raw5741step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5741step2 raw5741step2Labels raw5741step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical5742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5742 raw5742Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw5742 raw5742Labels = mixedMoment B raw5742step0 raw5742step0Labels := by
      have ha : raw5742step0 = (fun i j => raw5742 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5742step0 raw5742; decide +kernel
      have hl : raw5742step0Labels = raw5742Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5742 raw5742Labels permutation260 permutation5
    mixedMoment B raw5742step0 raw5742step0Labels = mixedMoment B raw5742step1 raw5742step1Labels := by
      have ha : raw5742step1 = -raw5742step0 := by apply Matrix.ext; change ∀ i j, raw5742step1 i j = -(raw5742step0 i j); unfold raw5742step1 raw5742step0; decide +kernel
      have hl : raw5742step1Labels = raw5742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5742step1 raw5742step1Labels = mixedMoment B raw5742step2 raw5742step2Labels := by
      have ha : raw5742step2 = raw5742step1 := by apply Matrix.ext; unfold raw5742step2 raw5742step1; decide +kernel
      have hl : raw5742step1Labels = labelEmbedding1 ∘ raw5742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5742step1 raw5742step1Labels raw5742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3155 node3155Labels := by rfl

theorem canonical5743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5743 raw5743Labels = mixedMoment B node1405 node1405Labels := by
  calc
    mixedMoment B raw5743 raw5743Labels = mixedMoment B raw5743step0 raw5743step0Labels := by
      have ha : raw5743step0 = (fun i j => raw5743 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5743step0 raw5743; decide +kernel
      have hl : raw5743step0Labels = raw5743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5743 raw5743Labels permutation240 permutation5
    mixedMoment B raw5743step0 raw5743step0Labels = mixedMoment B raw5743step1 raw5743step1Labels := by
      have ha : raw5743step1 = -raw5743step0 := by apply Matrix.ext; change ∀ i j, raw5743step1 i j = -(raw5743step0 i j); unfold raw5743step1 raw5743step0; decide +kernel
      have hl : raw5743step1Labels = raw5743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5743step1 raw5743step1Labels = mixedMoment B raw5743step2 raw5743step2Labels := by
      have ha : raw5743step2 = raw5743step1 := by apply Matrix.ext; unfold raw5743step2 raw5743step1; decide +kernel
      have hl : raw5743step1Labels = labelEmbedding1 ∘ raw5743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5743step1 raw5743step1Labels raw5743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1405 node1405Labels := by rfl

theorem canonical5744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5744 raw5744Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5744 raw5744Labels = mixedMoment B raw5744step0 raw5744step0Labels := by
      have hz : ∀ j, raw5744 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5744step0 = (fun i j => raw5744 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5744step0 raw5744; decide +kernel
      have hl : raw5744step0Labels = raw5744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5744 raw5744Labels permutation265 hz
    mixedMoment B raw5744step0 raw5744step0Labels = mixedMoment B raw5744step1 raw5744step1Labels := by
      have ha : raw5744step1 = (fun i j => raw5744step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5744step1 raw5744step0; decide +kernel
      have hl : raw5744step1Labels = raw5744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5744step0 raw5744step0Labels permutation32 permutation7
    mixedMoment B raw5744step1 raw5744step1Labels = mixedMoment B raw5744step2 raw5744step2Labels := by
      have ha : raw5744step2 = raw5744step1 := by apply Matrix.ext; unfold raw5744step2 raw5744step1; decide +kernel
      have hl : raw5744step1Labels = labelEmbedding1 ∘ raw5744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5744step1 raw5744step1Labels raw5744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical5745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5745 raw5745Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5745 raw5745Labels = mixedMoment B raw5745step0 raw5745step0Labels := by
      have hz : ∀ j, raw5745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5745step0 = (fun i j => raw5745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5745step0 raw5745; decide +kernel
      have hl : raw5745step0Labels = raw5745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5745 raw5745Labels permutation346 hz
    mixedMoment B raw5745step0 raw5745step0Labels = mixedMoment B raw5745step1 raw5745step1Labels := by
      have ha : raw5745step1 = (fun i j => raw5745step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5745step1 raw5745step0; decide +kernel
      have hl : raw5745step1Labels = raw5745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5745step0 raw5745step0Labels permutation32 permutation7
    mixedMoment B raw5745step1 raw5745step1Labels = mixedMoment B raw5745step2 raw5745step2Labels := by
      have ha : raw5745step2 = raw5745step1 := by apply Matrix.ext; unfold raw5745step2 raw5745step1; decide +kernel
      have hl : raw5745step1Labels = labelEmbedding1 ∘ raw5745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5745step1 raw5745step1Labels raw5745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical5746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5746 raw5746Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5746 raw5746Labels = mixedMoment B raw5746step0 raw5746step0Labels := by
      have hz : ∀ j, raw5746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5746step0 = (fun i j => raw5746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5746step0 raw5746; decide +kernel
      have hl : raw5746step0Labels = raw5746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5746 raw5746Labels permutation434 hz
    mixedMoment B raw5746step0 raw5746step0Labels = mixedMoment B raw5746step1 raw5746step1Labels := by
      have ha : raw5746step1 = (fun i j => raw5746step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5746step1 raw5746step0; decide +kernel
      have hl : raw5746step1Labels = raw5746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5746step0 raw5746step0Labels permutation32 permutation7
    mixedMoment B raw5746step1 raw5746step1Labels = mixedMoment B raw5746step2 raw5746step2Labels := by
      have ha : raw5746step2 = raw5746step1 := by apply Matrix.ext; unfold raw5746step2 raw5746step1; decide +kernel
      have hl : raw5746step1Labels = labelEmbedding1 ∘ raw5746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5746step1 raw5746step1Labels raw5746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical5747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5747 raw5747Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw5747 raw5747Labels = mixedMoment B raw5747step0 raw5747step0Labels := by
      have ha : raw5747step0 = (fun i j => raw5747 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5747step0 raw5747; decide +kernel
      have hl : raw5747step0Labels = raw5747Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5747 raw5747Labels permutation240 permutation5
    mixedMoment B raw5747step0 raw5747step0Labels = mixedMoment B raw5747step1 raw5747step1Labels := by
      have ha : raw5747step1 = -raw5747step0 := by apply Matrix.ext; change ∀ i j, raw5747step1 i j = -(raw5747step0 i j); unfold raw5747step1 raw5747step0; decide +kernel
      have hl : raw5747step1Labels = raw5747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5747step1 raw5747step1Labels = mixedMoment B raw5747step2 raw5747step2Labels := by
      have ha : raw5747step2 = raw5747step1 := by apply Matrix.ext; unfold raw5747step2 raw5747step1; decide +kernel
      have hl : raw5747step1Labels = labelEmbedding1 ∘ raw5747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5747step1 raw5747step1Labels raw5747step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3179 node3179Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = 0 := by
  exact mixedMoment_alpha B hF node1405 node1405Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1354 node1354Labels = Sparse.eval nodeValue1354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1354) = mixedMoment B node1354 node1354Labels := rfl
  simpa [nodeValue1354, Sparse.eval] using hc.symm

theorem sound1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1366 node1366Labels = Sparse.eval nodeValue1366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1366) = mixedMoment B node1366 node1366Labels := rfl
  simpa [nodeValue1366, Sparse.eval] using hc.symm

theorem sound1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = Sparse.eval nodeValue1405 (mixedVector B) := by
  simpa only [nodeValue1405, Sparse.eval_nil] using zero1405 B _hB _hF

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

theorem sound3058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3058 node3058Labels = Sparse.eval nodeValue3058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3058) = mixedMoment B node3058 node3058Labels := rfl
  simpa [nodeValue3058, Sparse.eval] using hc.symm

theorem sound3059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3059 node3059Labels = Sparse.eval nodeValue3059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3059) = mixedMoment B node3059 node3059Labels := rfl
  simpa [nodeValue3059, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

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

theorem sound3146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3146 node3146Labels = Sparse.eval nodeValue3146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3146) = mixedMoment B node3146 node3146Labels := rfl
  simpa [nodeValue3146, Sparse.eval] using hc.symm

theorem sound3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3155 node3155Labels = Sparse.eval nodeValue3155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3155) = mixedMoment B node3155 node3155Labels := rfl
  simpa [nodeValue3155, Sparse.eval] using hc.symm

theorem sound3165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3165 node3165Labels = Sparse.eval nodeValue3165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3165) = mixedMoment B node3165 node3165Labels := rfl
  simpa [nodeValue3165, Sparse.eval] using hc.symm

theorem sound3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3179 node3179Labels = Sparse.eval nodeValue3179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3179) = mixedMoment B node3179 node3179Labels := rfl
  simpa [nodeValue3179, Sparse.eval] using hc.symm

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

theorem sound3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3222 node3222Labels = Sparse.eval nodeValue3222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3222) = mixedMoment B node3222 node3222Labels := rfl
  simpa [nodeValue3222, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm214 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA214 + difference 0 1) (sourceB214 + difference 1 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 1) (sourceB214 + difference 1 0) sourceC214) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA214 + difference 0 2) (sourceB214 + difference 2 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 2) (sourceB214 + difference 2 0) sourceC214) = raw5719 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5719; decide +kernel
    rw [ha]
    exact (canonical5719 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA214 + difference 0 3) (sourceB214 + difference 3 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 3) (sourceB214 + difference 3 0) sourceC214) = raw5720 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5720; decide +kernel
    rw [ha]
    exact (canonical5720 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA214 + difference 0 4) (sourceB214 + difference 4 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA214 + difference 0 4) (sourceB214 + difference 4 0) sourceC214) = raw5721 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5721; decide +kernel
    rw [ha]
    exact (canonical5721 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA214 + difference 0 5) (sourceB214 + difference 5 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA214 + difference 0 5) (sourceB214 + difference 5 0) sourceC214) = raw5722 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5722; decide +kernel
    rw [ha]
    exact (canonical5722 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA214 + difference 1 0) (sourceB214 + difference 0 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 1 0) (sourceB214 + difference 0 1) sourceC214) = raw5723 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5723; decide +kernel
    rw [ha]
    exact (canonical5723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA214 + difference 1 2) (sourceB214 + difference 2 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 1 2) (sourceB214 + difference 2 1) sourceC214) = raw5724 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5724; decide +kernel
    rw [ha]
    exact (canonical5724 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA214 + difference 1 3) (sourceB214 + difference 3 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 1 3) (sourceB214 + difference 3 1) sourceC214) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA214 + difference 1 4) (sourceB214 + difference 4 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 1 4) (sourceB214 + difference 4 1) sourceC214) = raw5726 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5726; decide +kernel
    rw [ha]
    exact (canonical5726 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA214 + difference 1 5) (sourceB214 + difference 5 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 1 5) (sourceB214 + difference 5 1) sourceC214) = raw5727 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5727; decide +kernel
    rw [ha]
    exact (canonical5727 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA214 + difference 2 0) (sourceB214 + difference 0 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 2 0) (sourceB214 + difference 0 2) sourceC214) = raw5728 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5728; decide +kernel
    rw [ha]
    exact (canonical5728 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA214 + difference 2 1) (sourceB214 + difference 1 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 2 1) (sourceB214 + difference 1 2) sourceC214) = raw5729 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5729; decide +kernel
    rw [ha]
    exact (canonical5729 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA214 + difference 2 3) (sourceB214 + difference 3 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 2 3) (sourceB214 + difference 3 2) sourceC214) = raw5730 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5730; decide +kernel
    rw [ha]
    exact (canonical5730 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA214 + difference 2 4) (sourceB214 + difference 4 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 2 4) (sourceB214 + difference 4 2) sourceC214) = raw5731 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5731; decide +kernel
    rw [ha]
    exact (canonical5731 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA214 + difference 2 5) (sourceB214 + difference 5 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 2 5) (sourceB214 + difference 5 2) sourceC214) = raw5732 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5732; decide +kernel
    rw [ha]
    exact (canonical5732 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA214 + difference 3 0) (sourceB214 + difference 0 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 3 0) (sourceB214 + difference 0 3) sourceC214) = raw5733 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5733; decide +kernel
    rw [ha]
    exact (canonical5733 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA214 + difference 3 1) (sourceB214 + difference 1 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 3 1) (sourceB214 + difference 1 3) sourceC214) = raw5734 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5734; decide +kernel
    rw [ha]
    exact (canonical5734 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA214 + difference 3 2) (sourceB214 + difference 2 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 3 2) (sourceB214 + difference 2 3) sourceC214) = raw5735 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5735; decide +kernel
    rw [ha]
    exact (canonical5735 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA214 + difference 3 4) (sourceB214 + difference 4 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 3 4) (sourceB214 + difference 4 3) sourceC214) = raw5736 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5736; decide +kernel
    rw [ha]
    exact (canonical5736 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA214 + difference 3 5) (sourceB214 + difference 5 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 3 5) (sourceB214 + difference 5 3) sourceC214) = raw5737 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5737; decide +kernel
    rw [ha]
    exact (canonical5737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA214 + difference 4 0) (sourceB214 + difference 0 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA214 + difference 4 0) (sourceB214 + difference 0 4) sourceC214) = raw5738 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5738; decide +kernel
    rw [ha]
    exact (canonical5738 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA214 + difference 4 1) (sourceB214 + difference 1 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 1) (sourceB214 + difference 1 4) sourceC214) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA214 + difference 4 2) (sourceB214 + difference 2 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 2) (sourceB214 + difference 2 4) sourceC214) = raw5740 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5740; decide +kernel
    rw [ha]
    exact (canonical5740 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA214 + difference 4 3) (sourceB214 + difference 3 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 3) (sourceB214 + difference 3 4) sourceC214) = raw5741 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5741; decide +kernel
    rw [ha]
    exact (canonical5741 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA214 + difference 4 5) (sourceB214 + difference 5 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA214 + difference 4 5) (sourceB214 + difference 5 4) sourceC214) = raw5742 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5742; decide +kernel
    rw [ha]
    exact (canonical5742 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA214 + difference 5 0) (sourceB214 + difference 0 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA214 + difference 5 0) (sourceB214 + difference 0 5) sourceC214) = raw5743 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5743; decide +kernel
    rw [ha]
    exact (canonical5743 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA214 + difference 5 1) (sourceB214 + difference 1 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 1) (sourceB214 + difference 1 5) sourceC214) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA214 + difference 5 2) (sourceB214 + difference 2 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 2) (sourceB214 + difference 2 5) sourceC214) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA214 + difference 5 3) (sourceB214 + difference 3 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 3) (sourceB214 + difference 3 5) sourceC214) = raw5746 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5746; decide +kernel
    rw [ha]
    exact (canonical5746 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA214 + difference 5 4) (sourceB214 + difference 4 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA214 + difference 5 4) (sourceB214 + difference 4 5) sourceC214) = raw5747 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5747; decide +kernel
    rw [ha]
    exact (canonical5747 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA214 sourceB214 sourceC214
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm214, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck184 : Integer.Sparse.reindex keyMap MixedData.row184 = numericRow184 := by decide +kernel

theorem numericCheck184 (x : Master → ℝ) : Integer.Sparse.eval numericRow184 x =
    (1440 : ℝ) * reducedSource184 x := by
  norm_num [numericRow184, reducedSource184, Integer.Sparse.eval, Sparse.eval, nodeValue1354, nodeValue1366, nodeValue1405, nodeValue3058, nodeValue3059, nodeValue3077, nodeValue3146, nodeValue3155, nodeValue3165, nodeValue3179, nodeValue3222, nodeValue3223, nodeValue3227]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource184 (mixedVector B) = 0 := by
  have h1354 : mixedVector B (Sum.inr 1354) = Sparse.eval nodeValue1354 (mixedVector B) := by
    change mixedMoment B node1354 node1354Labels = _
    exact sound1354 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h1405 : mixedVector B (Sum.inr 1405) = Sparse.eval nodeValue1405 (mixedVector B) := by
    change mixedMoment B node1405 node1405Labels = _
    exact sound1405 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3059 : mixedVector B (Sum.inr 3059) = Sparse.eval nodeValue3059 (mixedVector B) := by
    change mixedMoment B node3059 node3059Labels = _
    exact sound3059 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3146 : mixedVector B (Sum.inr 3146) = Sparse.eval nodeValue3146 (mixedVector B) := by
    change mixedMoment B node3146 node3146Labels = _
    exact sound3146 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3165 : mixedVector B (Sum.inr 3165) = Sparse.eval nodeValue3165 (mixedVector B) := by
    change mixedMoment B node3165 node3165Labels = _
    exact sound3165 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223_e B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227_e B hB hF
  simpa only [sourceForm214, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1354, h1366, h1405, h3058, h3059, h3077, h3146, h3155, h3165, h3179, h3222, h3223, h3227, reducedSource184] using sourceEq214 B hB

theorem rowSound184_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row184 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck184, numericCheck184, reducedZero184 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e_oai
