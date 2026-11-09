-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:02:18.713244+00:00
-- url     : https://prove2.me/submissions/d11ade55-c2f8-4e84-a100-dc1a1d68051f

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11604 raw11604Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw11604 raw11604Labels = mixedMoment B raw11604step0 raw11604step0Labels := by
      have ha : raw11604step0 = (fun i j => raw11604 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11604step0 raw11604; decide +kernel
      have hl : raw11604step0Labels = raw11604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11604 raw11604Labels permutation160 permutation7
    mixedMoment B raw11604step0 raw11604step0Labels = mixedMoment B raw11604step1 raw11604step1Labels := by
      have ha : raw11604step1 = -raw11604step0 := by apply Matrix.ext; change ∀ i j, raw11604step1 i j = -(raw11604step0 i j); unfold raw11604step1 raw11604step0; decide +kernel
      have hl : raw11604step1Labels = raw11604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11604step1 raw11604step1Labels = mixedMoment B raw11604step2 raw11604step2Labels := by
      have ha : raw11604step2 = raw11604step1 := by apply Matrix.ext; unfold raw11604step2 raw11604step1; decide +kernel
      have hl : raw11604step1Labels = labelEmbedding1 ∘ raw11604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11604step1 raw11604step1Labels raw11604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical11605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11605 raw11605Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw11605 raw11605Labels = mixedMoment B raw11605step0 raw11605step0Labels := by
      have ha : raw11605step0 = (fun i j => raw11605 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11605step0 raw11605; decide +kernel
      have hl : raw11605step0Labels = raw11605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11605 raw11605Labels permutation160 permutation7
    mixedMoment B raw11605step0 raw11605step0Labels = mixedMoment B raw11605step1 raw11605step1Labels := by
      have ha : raw11605step1 = -raw11605step0 := by apply Matrix.ext; change ∀ i j, raw11605step1 i j = -(raw11605step0 i j); unfold raw11605step1 raw11605step0; decide +kernel
      have hl : raw11605step1Labels = raw11605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11605step1 raw11605step1Labels = mixedMoment B raw11605step2 raw11605step2Labels := by
      have ha : raw11605step2 = raw11605step1 := by apply Matrix.ext; unfold raw11605step2 raw11605step1; decide +kernel
      have hl : raw11605step1Labels = labelEmbedding1 ∘ raw11605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11605step1 raw11605step1Labels raw11605step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical11606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11606 raw11606Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11606 raw11606Labels = mixedMoment B raw11606step0 raw11606step0Labels := by
      have hz : ∀ j, raw11606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11606step0 = (fun i j => raw11606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11606step0 raw11606; decide +kernel
      have hl : raw11606step0Labels = raw11606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11606 raw11606Labels permutation434 hz
    mixedMoment B raw11606step0 raw11606step0Labels = mixedMoment B raw11606step1 raw11606step1Labels := by
      have ha : raw11606step1 = (fun i j => raw11606step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11606step1 raw11606step0; decide +kernel
      have hl : raw11606step1Labels = raw11606step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11606step0 raw11606step0Labels permutation34 permutation7
    mixedMoment B raw11606step1 raw11606step1Labels = mixedMoment B raw11606step2 raw11606step2Labels := by
      have ha : raw11606step2 = -raw11606step1 := by apply Matrix.ext; change ∀ i j, raw11606step2 i j = -(raw11606step1 i j); unfold raw11606step2 raw11606step1; decide +kernel
      have hl : raw11606step2Labels = raw11606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11606step2 raw11606step2Labels = mixedMoment B raw11606step3 raw11606step3Labels := by
      have ha : raw11606step3 = raw11606step2 := by apply Matrix.ext; unfold raw11606step3 raw11606step2; decide +kernel
      have hl : raw11606step2Labels = labelEmbedding1 ∘ raw11606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11606step2 raw11606step2Labels raw11606step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical11607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11607 raw11607Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11607 raw11607Labels = mixedMoment B raw11607step0 raw11607step0Labels := by
      have hz : ∀ j, raw11607 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11607step0 = (fun i j => raw11607 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11607step0 raw11607; decide +kernel
      have hl : raw11607step0Labels = raw11607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11607 raw11607Labels permutation520 hz
    mixedMoment B raw11607step0 raw11607step0Labels = mixedMoment B raw11607step1 raw11607step1Labels := by
      have ha : raw11607step1 = (fun i j => raw11607step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11607step1 raw11607step0; decide +kernel
      have hl : raw11607step1Labels = raw11607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11607step0 raw11607step0Labels permutation34 permutation7
    mixedMoment B raw11607step1 raw11607step1Labels = mixedMoment B raw11607step2 raw11607step2Labels := by
      have ha : raw11607step2 = -raw11607step1 := by apply Matrix.ext; change ∀ i j, raw11607step2 i j = -(raw11607step1 i j); unfold raw11607step2 raw11607step1; decide +kernel
      have hl : raw11607step2Labels = raw11607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11607step2 raw11607step2Labels = mixedMoment B raw11607step3 raw11607step3Labels := by
      have ha : raw11607step3 = raw11607step2 := by apply Matrix.ext; unfold raw11607step3 raw11607step2; decide +kernel
      have hl : raw11607step2Labels = labelEmbedding1 ∘ raw11607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11607step2 raw11607step2Labels raw11607step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical11608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11608 raw11608Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11608 raw11608Labels = mixedMoment B raw11608step0 raw11608step0Labels := by
      have ha : raw11608step0 = (fun i j => raw11608 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11608step0 raw11608; decide +kernel
      have hl : raw11608step0Labels = raw11608Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11608 raw11608Labels permutation160 permutation7
    mixedMoment B raw11608step0 raw11608step0Labels = mixedMoment B raw11608step1 raw11608step1Labels := by
      have ha : raw11608step1 = -raw11608step0 := by apply Matrix.ext; change ∀ i j, raw11608step1 i j = -(raw11608step0 i j); unfold raw11608step1 raw11608step0; decide +kernel
      have hl : raw11608step1Labels = raw11608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11608step1 raw11608step1Labels = mixedMoment B raw11608step2 raw11608step2Labels := by
      have ha : raw11608step2 = raw11608step1 := by apply Matrix.ext; unfold raw11608step2 raw11608step1; decide +kernel
      have hl : raw11608step1Labels = labelEmbedding1 ∘ raw11608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11608step1 raw11608step1Labels raw11608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical11609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11609 raw11609Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw11609 raw11609Labels = mixedMoment B raw11609step0 raw11609step0Labels := by
      have ha : raw11609step0 = (fun i j => raw11609 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11609step0 raw11609; decide +kernel
      have hl : raw11609step0Labels = raw11609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11609 raw11609Labels permutation197 permutation5
    mixedMoment B raw11609step0 raw11609step0Labels = mixedMoment B raw11609step1 raw11609step1Labels := by
      have ha : raw11609step1 = -raw11609step0 := by apply Matrix.ext; change ∀ i j, raw11609step1 i j = -(raw11609step0 i j); unfold raw11609step1 raw11609step0; decide +kernel
      have hl : raw11609step1Labels = raw11609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11609step1 raw11609step1Labels = mixedMoment B raw11609step2 raw11609step2Labels := by
      have ha : raw11609step2 = raw11609step1 := by apply Matrix.ext; unfold raw11609step2 raw11609step1; decide +kernel
      have hl : raw11609step1Labels = labelEmbedding1 ∘ raw11609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11609step1 raw11609step1Labels raw11609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical11610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11610 raw11610Labels = mixedMoment B node3566 node3566Labels := by
  calc
    mixedMoment B raw11610 raw11610Labels = mixedMoment B raw11610step0 raw11610step0Labels := by
      have ha : raw11610step0 = (fun i j => raw11610 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11610step0 raw11610; decide +kernel
      have hl : raw11610step0Labels = raw11610Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11610 raw11610Labels permutation160 permutation7
    mixedMoment B raw11610step0 raw11610step0Labels = mixedMoment B raw11610step1 raw11610step1Labels := by
      have ha : raw11610step1 = -raw11610step0 := by apply Matrix.ext; change ∀ i j, raw11610step1 i j = -(raw11610step0 i j); unfold raw11610step1 raw11610step0; decide +kernel
      have hl : raw11610step1Labels = raw11610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11610step1 raw11610step1Labels = mixedMoment B raw11610step2 raw11610step2Labels := by
      have ha : raw11610step2 = raw11610step1 := by apply Matrix.ext; unfold raw11610step2 raw11610step1; decide +kernel
      have hl : raw11610step1Labels = labelEmbedding1 ∘ raw11610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11610step1 raw11610step1Labels raw11610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3566 node3566Labels := by rfl

theorem canonical11611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11611 raw11611Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11611 raw11611Labels = mixedMoment B raw11611step0 raw11611step0Labels := by
      have hz : ∀ j, raw11611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11611step0 = (fun i j => raw11611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11611step0 raw11611; decide +kernel
      have hl : raw11611step0Labels = raw11611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11611 raw11611Labels permutation434 hz
    mixedMoment B raw11611step0 raw11611step0Labels = mixedMoment B raw11611step1 raw11611step1Labels := by
      have ha : raw11611step1 = (fun i j => raw11611step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11611step1 raw11611step0; decide +kernel
      have hl : raw11611step1Labels = raw11611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11611step0 raw11611step0Labels permutation34 permutation7
    mixedMoment B raw11611step1 raw11611step1Labels = mixedMoment B raw11611step2 raw11611step2Labels := by
      have ha : raw11611step2 = -raw11611step1 := by apply Matrix.ext; change ∀ i j, raw11611step2 i j = -(raw11611step1 i j); unfold raw11611step2 raw11611step1; decide +kernel
      have hl : raw11611step2Labels = raw11611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11611step2 raw11611step2Labels = mixedMoment B raw11611step3 raw11611step3Labels := by
      have ha : raw11611step3 = raw11611step2 := by apply Matrix.ext; unfold raw11611step3 raw11611step2; decide +kernel
      have hl : raw11611step2Labels = labelEmbedding1 ∘ raw11611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11611step2 raw11611step2Labels raw11611step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11612 raw11612Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11612 raw11612Labels = mixedMoment B raw11612step0 raw11612step0Labels := by
      have hz : ∀ j, raw11612 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11612step0 = (fun i j => raw11612 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11612step0 raw11612; decide +kernel
      have hl : raw11612step0Labels = raw11612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11612 raw11612Labels permutation520 hz
    mixedMoment B raw11612step0 raw11612step0Labels = mixedMoment B raw11612step1 raw11612step1Labels := by
      have ha : raw11612step1 = (fun i j => raw11612step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11612step1 raw11612step0; decide +kernel
      have hl : raw11612step1Labels = raw11612step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11612step0 raw11612step0Labels permutation34 permutation7
    mixedMoment B raw11612step1 raw11612step1Labels = mixedMoment B raw11612step2 raw11612step2Labels := by
      have ha : raw11612step2 = -raw11612step1 := by apply Matrix.ext; change ∀ i j, raw11612step2 i j = -(raw11612step1 i j); unfold raw11612step2 raw11612step1; decide +kernel
      have hl : raw11612step2Labels = raw11612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11612step2 raw11612step2Labels = mixedMoment B raw11612step3 raw11612step3Labels := by
      have ha : raw11612step3 = raw11612step2 := by apply Matrix.ext; unfold raw11612step3 raw11612step2; decide +kernel
      have hl : raw11612step2Labels = labelEmbedding1 ∘ raw11612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11612step2 raw11612step2Labels raw11612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11613 raw11613Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw11613 raw11613Labels = mixedMoment B raw11613step0 raw11613step0Labels := by
      have ha : raw11613step0 = (fun i j => raw11613 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11613step0 raw11613; decide +kernel
      have hl : raw11613step0Labels = raw11613Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11613 raw11613Labels permutation160 permutation7
    mixedMoment B raw11613step0 raw11613step0Labels = mixedMoment B raw11613step1 raw11613step1Labels := by
      have ha : raw11613step1 = -raw11613step0 := by apply Matrix.ext; change ∀ i j, raw11613step1 i j = -(raw11613step0 i j); unfold raw11613step1 raw11613step0; decide +kernel
      have hl : raw11613step1Labels = raw11613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11613step1 raw11613step1Labels = mixedMoment B raw11613step2 raw11613step2Labels := by
      have ha : raw11613step2 = raw11613step1 := by apply Matrix.ext; unfold raw11613step2 raw11613step1; decide +kernel
      have hl : raw11613step1Labels = labelEmbedding1 ∘ raw11613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11613step1 raw11613step1Labels raw11613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical11614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11614 raw11614Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw11614 raw11614Labels = mixedMoment B raw11614step0 raw11614step0Labels := by
      have ha : raw11614step0 = (fun i j => raw11614 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11614step0 raw11614; decide +kernel
      have hl : raw11614step0Labels = raw11614Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11614 raw11614Labels permutation160 permutation7
    mixedMoment B raw11614step0 raw11614step0Labels = mixedMoment B raw11614step1 raw11614step1Labels := by
      have ha : raw11614step1 = -raw11614step0 := by apply Matrix.ext; change ∀ i j, raw11614step1 i j = -(raw11614step0 i j); unfold raw11614step1 raw11614step0; decide +kernel
      have hl : raw11614step1Labels = raw11614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11614step1 raw11614step1Labels = mixedMoment B raw11614step2 raw11614step2Labels := by
      have ha : raw11614step2 = raw11614step1 := by apply Matrix.ext; unfold raw11614step2 raw11614step1; decide +kernel
      have hl : raw11614step1Labels = labelEmbedding1 ∘ raw11614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11614step1 raw11614step1Labels raw11614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical11615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11615 raw11615Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw11615 raw11615Labels = mixedMoment B raw11615step0 raw11615step0Labels := by
      have ha : raw11615step0 = (fun i j => raw11615 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11615step0 raw11615; decide +kernel
      have hl : raw11615step0Labels = raw11615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11615 raw11615Labels permutation160 permutation7
    mixedMoment B raw11615step0 raw11615step0Labels = mixedMoment B raw11615step1 raw11615step1Labels := by
      have ha : raw11615step1 = -raw11615step0 := by apply Matrix.ext; change ∀ i j, raw11615step1 i j = -(raw11615step0 i j); unfold raw11615step1 raw11615step0; decide +kernel
      have hl : raw11615step1Labels = raw11615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11615step1 raw11615step1Labels = mixedMoment B raw11615step2 raw11615step2Labels := by
      have ha : raw11615step2 = raw11615step1 := by apply Matrix.ext; unfold raw11615step2 raw11615step1; decide +kernel
      have hl : raw11615step1Labels = labelEmbedding1 ∘ raw11615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11615step1 raw11615step1Labels raw11615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical11616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11616 raw11616Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11616 raw11616Labels = mixedMoment B raw11616step0 raw11616step0Labels := by
      have hz : ∀ j, raw11616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11616step0 = (fun i j => raw11616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11616step0 raw11616; decide +kernel
      have hl : raw11616step0Labels = raw11616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11616 raw11616Labels permutation434 hz
    mixedMoment B raw11616step0 raw11616step0Labels = mixedMoment B raw11616step1 raw11616step1Labels := by
      have ha : raw11616step1 = (fun i j => raw11616step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11616step1 raw11616step0; decide +kernel
      have hl : raw11616step1Labels = raw11616step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11616step0 raw11616step0Labels permutation34 permutation7
    mixedMoment B raw11616step1 raw11616step1Labels = mixedMoment B raw11616step2 raw11616step2Labels := by
      have ha : raw11616step2 = -raw11616step1 := by apply Matrix.ext; change ∀ i j, raw11616step2 i j = -(raw11616step1 i j); unfold raw11616step2 raw11616step1; decide +kernel
      have hl : raw11616step2Labels = raw11616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11616step2 raw11616step2Labels = mixedMoment B raw11616step3 raw11616step3Labels := by
      have ha : raw11616step3 = raw11616step2 := by apply Matrix.ext; unfold raw11616step3 raw11616step2; decide +kernel
      have hl : raw11616step2Labels = labelEmbedding1 ∘ raw11616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11616step2 raw11616step2Labels raw11616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical11617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11617 raw11617Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11617 raw11617Labels = mixedMoment B raw11617step0 raw11617step0Labels := by
      have hz : ∀ j, raw11617 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11617step0 = (fun i j => raw11617 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11617step0 raw11617; decide +kernel
      have hl : raw11617step0Labels = raw11617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11617 raw11617Labels permutation520 hz
    mixedMoment B raw11617step0 raw11617step0Labels = mixedMoment B raw11617step1 raw11617step1Labels := by
      have ha : raw11617step1 = (fun i j => raw11617step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11617step1 raw11617step0; decide +kernel
      have hl : raw11617step1Labels = raw11617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11617step0 raw11617step0Labels permutation34 permutation7
    mixedMoment B raw11617step1 raw11617step1Labels = mixedMoment B raw11617step2 raw11617step2Labels := by
      have ha : raw11617step2 = -raw11617step1 := by apply Matrix.ext; change ∀ i j, raw11617step2 i j = -(raw11617step1 i j); unfold raw11617step2 raw11617step1; decide +kernel
      have hl : raw11617step2Labels = raw11617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11617step2 raw11617step2Labels = mixedMoment B raw11617step3 raw11617step3Labels := by
      have ha : raw11617step3 = raw11617step2 := by apply Matrix.ext; unfold raw11617step3 raw11617step2; decide +kernel
      have hl : raw11617step2Labels = labelEmbedding1 ∘ raw11617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11617step2 raw11617step2Labels raw11617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical11618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11618 raw11618Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11618 raw11618Labels = mixedMoment B raw11618step0 raw11618step0Labels := by
      have ha : raw11618step0 = (fun i j => raw11618 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11618step0 raw11618; decide +kernel
      have hl : raw11618step0Labels = raw11618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11618 raw11618Labels permutation160 permutation7
    mixedMoment B raw11618step0 raw11618step0Labels = mixedMoment B raw11618step1 raw11618step1Labels := by
      have ha : raw11618step1 = -raw11618step0 := by apply Matrix.ext; change ∀ i j, raw11618step1 i j = -(raw11618step0 i j); unfold raw11618step1 raw11618step0; decide +kernel
      have hl : raw11618step1Labels = raw11618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11618step1 raw11618step1Labels = mixedMoment B raw11618step2 raw11618step2Labels := by
      have ha : raw11618step2 = raw11618step1 := by apply Matrix.ext; unfold raw11618step2 raw11618step1; decide +kernel
      have hl : raw11618step1Labels = labelEmbedding1 ∘ raw11618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11618step1 raw11618step1Labels raw11618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical11619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11619 raw11619Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw11619 raw11619Labels = mixedMoment B raw11619step0 raw11619step0Labels := by
      have ha : raw11619step0 = (fun i j => raw11619 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11619step0 raw11619; decide +kernel
      have hl : raw11619step0Labels = raw11619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11619 raw11619Labels permutation195 permutation5
    mixedMoment B raw11619step0 raw11619step0Labels = mixedMoment B raw11619step1 raw11619step1Labels := by
      have ha : raw11619step1 = -raw11619step0 := by apply Matrix.ext; change ∀ i j, raw11619step1 i j = -(raw11619step0 i j); unfold raw11619step1 raw11619step0; decide +kernel
      have hl : raw11619step1Labels = raw11619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11619step1 raw11619step1Labels = mixedMoment B raw11619step2 raw11619step2Labels := by
      have ha : raw11619step2 = raw11619step1 := by apply Matrix.ext; unfold raw11619step2 raw11619step1; decide +kernel
      have hl : raw11619step1Labels = labelEmbedding1 ∘ raw11619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11619step1 raw11619step1Labels raw11619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

theorem canonical11620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11620 raw11620Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11620 raw11620Labels = mixedMoment B raw11620step0 raw11620step0Labels := by
      have ha : raw11620step0 = (fun i j => raw11620 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11620step0 raw11620; decide +kernel
      have hl : raw11620step0Labels = raw11620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11620 raw11620Labels permutation166 permutation7
    mixedMoment B raw11620step0 raw11620step0Labels = mixedMoment B raw11620step1 raw11620step1Labels := by
      have ha : raw11620step1 = -raw11620step0 := by apply Matrix.ext; change ∀ i j, raw11620step1 i j = -(raw11620step0 i j); unfold raw11620step1 raw11620step0; decide +kernel
      have hl : raw11620step1Labels = raw11620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11620step1 raw11620step1Labels = mixedMoment B raw11620step2 raw11620step2Labels := by
      have ha : raw11620step2 = raw11620step1 := by apply Matrix.ext; unfold raw11620step2 raw11620step1; decide +kernel
      have hl : raw11620step1Labels = labelEmbedding1 ∘ raw11620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11620step1 raw11620step1Labels raw11620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical11621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11621 raw11621Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw11621 raw11621Labels = mixedMoment B raw11621step0 raw11621step0Labels := by
      have ha : raw11621step0 = (fun i j => raw11621 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11621step0 raw11621; decide +kernel
      have hl : raw11621step0Labels = raw11621Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11621 raw11621Labels permutation166 permutation7
    mixedMoment B raw11621step0 raw11621step0Labels = mixedMoment B raw11621step1 raw11621step1Labels := by
      have ha : raw11621step1 = -raw11621step0 := by apply Matrix.ext; change ∀ i j, raw11621step1 i j = -(raw11621step0 i j); unfold raw11621step1 raw11621step0; decide +kernel
      have hl : raw11621step1Labels = raw11621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11621step1 raw11621step1Labels = mixedMoment B raw11621step2 raw11621step2Labels := by
      have ha : raw11621step2 = raw11621step1 := by apply Matrix.ext; unfold raw11621step2 raw11621step1; decide +kernel
      have hl : raw11621step1Labels = labelEmbedding1 ∘ raw11621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11621step1 raw11621step1Labels raw11621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

theorem canonical11622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11622 raw11622Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw11622 raw11622Labels = mixedMoment B raw11622step0 raw11622step0Labels := by
      have hz : ∀ j, raw11622 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11622step0 = (fun i j => raw11622 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11622step0 raw11622; decide +kernel
      have hl : raw11622step0Labels = raw11622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11622 raw11622Labels permutation520 hz
    mixedMoment B raw11622step0 raw11622step0Labels = mixedMoment B raw11622step1 raw11622step1Labels := by
      have ha : raw11622step1 = (fun i j => raw11622step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11622step1 raw11622step0; decide +kernel
      have hl : raw11622step1Labels = raw11622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11622step0 raw11622step0Labels permutation34 permutation7
    mixedMoment B raw11622step1 raw11622step1Labels = mixedMoment B raw11622step2 raw11622step2Labels := by
      have ha : raw11622step2 = -raw11622step1 := by apply Matrix.ext; change ∀ i j, raw11622step2 i j = -(raw11622step1 i j); unfold raw11622step2 raw11622step1; decide +kernel
      have hl : raw11622step2Labels = raw11622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11622step2 raw11622step2Labels = mixedMoment B raw11622step3 raw11622step3Labels := by
      have ha : raw11622step3 = raw11622step2 := by apply Matrix.ext; unfold raw11622step3 raw11622step2; decide +kernel
      have hl : raw11622step2Labels = labelEmbedding1 ∘ raw11622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11622step2 raw11622step2Labels raw11622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical11623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11623 raw11623Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11623 raw11623Labels = mixedMoment B raw11623step0 raw11623step0Labels := by
      have ha : raw11623step0 = (fun i j => raw11623 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11623step0 raw11623; decide +kernel
      have hl : raw11623step0Labels = raw11623Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11623 raw11623Labels permutation166 permutation7
    mixedMoment B raw11623step0 raw11623step0Labels = mixedMoment B raw11623step1 raw11623step1Labels := by
      have ha : raw11623step1 = -raw11623step0 := by apply Matrix.ext; change ∀ i j, raw11623step1 i j = -(raw11623step0 i j); unfold raw11623step1 raw11623step0; decide +kernel
      have hl : raw11623step1Labels = raw11623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11623step1 raw11623step1Labels = mixedMoment B raw11623step2 raw11623step2Labels := by
      have ha : raw11623step2 = raw11623step1 := by apply Matrix.ext; unfold raw11623step2 raw11623step1; decide +kernel
      have hl : raw11623step1Labels = labelEmbedding1 ∘ raw11623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11623step1 raw11623step1Labels raw11623step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical11624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11624 raw11624Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw11624 raw11624Labels = mixedMoment B raw11624step0 raw11624step0Labels := by
      have ha : raw11624step0 = (fun i j => raw11624 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11624step0 raw11624; decide +kernel
      have hl : raw11624step0Labels = raw11624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11624 raw11624Labels permutation194 permutation5
    mixedMoment B raw11624step0 raw11624step0Labels = mixedMoment B raw11624step1 raw11624step1Labels := by
      have ha : raw11624step1 = -raw11624step0 := by apply Matrix.ext; change ∀ i j, raw11624step1 i j = -(raw11624step0 i j); unfold raw11624step1 raw11624step0; decide +kernel
      have hl : raw11624step1Labels = raw11624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11624step1 raw11624step1Labels = mixedMoment B raw11624step2 raw11624step2Labels := by
      have ha : raw11624step2 = raw11624step1 := by apply Matrix.ext; unfold raw11624step2 raw11624step1; decide +kernel
      have hl : raw11624step1Labels = labelEmbedding1 ∘ raw11624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11624step1 raw11624step1Labels raw11624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

theorem canonical11625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11625 raw11625Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11625 raw11625Labels = mixedMoment B raw11625step0 raw11625step0Labels := by
      have ha : raw11625step0 = (fun i j => raw11625 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11625step0 raw11625; decide +kernel
      have hl : raw11625step0Labels = raw11625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11625 raw11625Labels permutation160 permutation7
    mixedMoment B raw11625step0 raw11625step0Labels = mixedMoment B raw11625step1 raw11625step1Labels := by
      have ha : raw11625step1 = -raw11625step0 := by apply Matrix.ext; change ∀ i j, raw11625step1 i j = -(raw11625step0 i j); unfold raw11625step1 raw11625step0; decide +kernel
      have hl : raw11625step1Labels = raw11625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11625step1 raw11625step1Labels = mixedMoment B raw11625step2 raw11625step2Labels := by
      have ha : raw11625step2 = raw11625step1 := by apply Matrix.ext; unfold raw11625step2 raw11625step1; decide +kernel
      have hl : raw11625step1Labels = labelEmbedding1 ∘ raw11625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11625step1 raw11625step1Labels raw11625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical11626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11626 raw11626Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw11626 raw11626Labels = mixedMoment B raw11626step0 raw11626step0Labels := by
      have ha : raw11626step0 = (fun i j => raw11626 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11626step0 raw11626; decide +kernel
      have hl : raw11626step0Labels = raw11626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11626 raw11626Labels permutation160 permutation7
    mixedMoment B raw11626step0 raw11626step0Labels = mixedMoment B raw11626step1 raw11626step1Labels := by
      have ha : raw11626step1 = -raw11626step0 := by apply Matrix.ext; change ∀ i j, raw11626step1 i j = -(raw11626step0 i j); unfold raw11626step1 raw11626step0; decide +kernel
      have hl : raw11626step1Labels = raw11626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11626step1 raw11626step1Labels = mixedMoment B raw11626step2 raw11626step2Labels := by
      have ha : raw11626step2 = raw11626step1 := by apply Matrix.ext; unfold raw11626step2 raw11626step1; decide +kernel
      have hl : raw11626step1Labels = labelEmbedding1 ∘ raw11626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11626step1 raw11626step1Labels raw11626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

theorem canonical11627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11627 raw11627Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw11627 raw11627Labels = mixedMoment B raw11627step0 raw11627step0Labels := by
      have hz : ∀ j, raw11627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11627step0 = (fun i j => raw11627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11627step0 raw11627; decide +kernel
      have hl : raw11627step0Labels = raw11627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11627 raw11627Labels permutation434 hz
    mixedMoment B raw11627step0 raw11627step0Labels = mixedMoment B raw11627step1 raw11627step1Labels := by
      have ha : raw11627step1 = (fun i j => raw11627step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11627step1 raw11627step0; decide +kernel
      have hl : raw11627step1Labels = raw11627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11627step0 raw11627step0Labels permutation34 permutation7
    mixedMoment B raw11627step1 raw11627step1Labels = mixedMoment B raw11627step2 raw11627step2Labels := by
      have ha : raw11627step2 = -raw11627step1 := by apply Matrix.ext; change ∀ i j, raw11627step2 i j = -(raw11627step1 i j); unfold raw11627step2 raw11627step1; decide +kernel
      have hl : raw11627step2Labels = raw11627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11627step2 raw11627step2Labels = mixedMoment B raw11627step3 raw11627step3Labels := by
      have ha : raw11627step3 = raw11627step2 := by apply Matrix.ext; unfold raw11627step3 raw11627step2; decide +kernel
      have hl : raw11627step2Labels = labelEmbedding1 ∘ raw11627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11627step2 raw11627step2Labels raw11627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical11628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11628 raw11628Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11628 raw11628Labels = mixedMoment B raw11628step0 raw11628step0Labels := by
      have ha : raw11628step0 = (fun i j => raw11628 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11628step0 raw11628; decide +kernel
      have hl : raw11628step0Labels = raw11628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11628 raw11628Labels permutation160 permutation7
    mixedMoment B raw11628step0 raw11628step0Labels = mixedMoment B raw11628step1 raw11628step1Labels := by
      have ha : raw11628step1 = -raw11628step0 := by apply Matrix.ext; change ∀ i j, raw11628step1 i j = -(raw11628step0 i j); unfold raw11628step1 raw11628step0; decide +kernel
      have hl : raw11628step1Labels = raw11628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11628step1 raw11628step1Labels = mixedMoment B raw11628step2 raw11628step2Labels := by
      have ha : raw11628step2 = raw11628step1 := by apply Matrix.ext; unfold raw11628step2 raw11628step1; decide +kernel
      have hl : raw11628step1Labels = labelEmbedding1 ∘ raw11628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11628step1 raw11628step1Labels raw11628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical11629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11629 raw11629Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw11629 raw11629Labels = mixedMoment B raw11629step0 raw11629step0Labels := by
      have ha : raw11629step0 = (fun i j => raw11629 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11629step0 raw11629; decide +kernel
      have hl : raw11629step0Labels = raw11629Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11629 raw11629Labels permutation160 permutation7
    mixedMoment B raw11629step0 raw11629step0Labels = mixedMoment B raw11629step1 raw11629step1Labels := by
      have ha : raw11629step1 = -raw11629step0 := by apply Matrix.ext; change ∀ i j, raw11629step1 i j = -(raw11629step0 i j); unfold raw11629step1 raw11629step0; decide +kernel
      have hl : raw11629step1Labels = raw11629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11629step1 raw11629step1Labels = mixedMoment B raw11629step2 raw11629step2Labels := by
      have ha : raw11629step2 = raw11629step1 := by apply Matrix.ext; unfold raw11629step2 raw11629step1; decide +kernel
      have hl : raw11629step1Labels = labelEmbedding1 ∘ raw11629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11629step1 raw11629step1Labels raw11629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical11630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11630 raw11630Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw11630 raw11630Labels = mixedMoment B raw11630step0 raw11630step0Labels := by
      have ha : raw11630step0 = (fun i j => raw11630 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11630step0 raw11630; decide +kernel
      have hl : raw11630step0Labels = raw11630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11630 raw11630Labels permutation160 permutation7
    mixedMoment B raw11630step0 raw11630step0Labels = mixedMoment B raw11630step1 raw11630step1Labels := by
      have ha : raw11630step1 = -raw11630step0 := by apply Matrix.ext; change ∀ i j, raw11630step1 i j = -(raw11630step0 i j); unfold raw11630step1 raw11630step0; decide +kernel
      have hl : raw11630step1Labels = raw11630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11630step1 raw11630step1Labels = mixedMoment B raw11630step2 raw11630step2Labels := by
      have ha : raw11630step2 = raw11630step1 := by apply Matrix.ext; unfold raw11630step2 raw11630step1; decide +kernel
      have hl : raw11630step1Labels = labelEmbedding1 ∘ raw11630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11630step1 raw11630step1Labels raw11630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical11631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11631 raw11631Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw11631 raw11631Labels = mixedMoment B raw11631step0 raw11631step0Labels := by
      have ha : raw11631step0 = (fun i j => raw11631 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11631step0 raw11631; decide +kernel
      have hl : raw11631step0Labels = raw11631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11631 raw11631Labels permutation160 permutation7
    mixedMoment B raw11631step0 raw11631step0Labels = mixedMoment B raw11631step1 raw11631step1Labels := by
      have ha : raw11631step1 = -raw11631step0 := by apply Matrix.ext; change ∀ i j, raw11631step1 i j = -(raw11631step0 i j); unfold raw11631step1 raw11631step0; decide +kernel
      have hl : raw11631step1Labels = raw11631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11631step1 raw11631step1Labels = mixedMoment B raw11631step2 raw11631step2Labels := by
      have ha : raw11631step2 = raw11631step1 := by apply Matrix.ext; unfold raw11631step2 raw11631step1; decide +kernel
      have hl : raw11631step1Labels = labelEmbedding1 ∘ raw11631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11631step1 raw11631step1Labels raw11631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical11632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11632 raw11632Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11632 raw11632Labels = mixedMoment B raw11632step0 raw11632step0Labels := by
      have hz : ∀ j, raw11632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11632step0 = (fun i j => raw11632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11632step0 raw11632; decide +kernel
      have hl : raw11632step0Labels = raw11632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11632 raw11632Labels permutation434 hz
    mixedMoment B raw11632step0 raw11632step0Labels = mixedMoment B raw11632step1 raw11632step1Labels := by
      have ha : raw11632step1 = (fun i j => raw11632step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11632step1 raw11632step0; decide +kernel
      have hl : raw11632step1Labels = raw11632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11632step0 raw11632step0Labels permutation34 permutation7
    mixedMoment B raw11632step1 raw11632step1Labels = mixedMoment B raw11632step2 raw11632step2Labels := by
      have ha : raw11632step2 = -raw11632step1 := by apply Matrix.ext; change ∀ i j, raw11632step2 i j = -(raw11632step1 i j); unfold raw11632step2 raw11632step1; decide +kernel
      have hl : raw11632step2Labels = raw11632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11632step2 raw11632step2Labels = mixedMoment B raw11632step3 raw11632step3Labels := by
      have ha : raw11632step3 = raw11632step2 := by apply Matrix.ext; unfold raw11632step3 raw11632step2; decide +kernel
      have hl : raw11632step2Labels = labelEmbedding1 ∘ raw11632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11632step2 raw11632step2Labels raw11632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical11633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11633 raw11633Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11633 raw11633Labels = mixedMoment B raw11633step0 raw11633step0Labels := by
      have hz : ∀ j, raw11633 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11633step0 = (fun i j => raw11633 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11633step0 raw11633; decide +kernel
      have hl : raw11633step0Labels = raw11633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11633 raw11633Labels permutation520 hz
    mixedMoment B raw11633step0 raw11633step0Labels = mixedMoment B raw11633step1 raw11633step1Labels := by
      have ha : raw11633step1 = (fun i j => raw11633step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11633step1 raw11633step0; decide +kernel
      have hl : raw11633step1Labels = raw11633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11633step0 raw11633step0Labels permutation34 permutation7
    mixedMoment B raw11633step1 raw11633step1Labels = mixedMoment B raw11633step2 raw11633step2Labels := by
      have ha : raw11633step2 = -raw11633step1 := by apply Matrix.ext; change ∀ i j, raw11633step2 i j = -(raw11633step1 i j); unfold raw11633step2 raw11633step1; decide +kernel
      have hl : raw11633step2Labels = raw11633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11633step2 raw11633step2Labels = mixedMoment B raw11633step3 raw11633step3Labels := by
      have ha : raw11633step3 = raw11633step2 := by apply Matrix.ext; unfold raw11633step3 raw11633step2; decide +kernel
      have hl : raw11633step2Labels = labelEmbedding1 ∘ raw11633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11633step2 raw11633step2Labels raw11633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

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

theorem sound3285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3285 node3285Labels = Sparse.eval nodeValue3285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3285) = mixedMoment B node3285 node3285Labels := rfl
  simpa [nodeValue3285, Sparse.eval] using hc.symm

theorem sound3286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3286 node3286Labels = Sparse.eval nodeValue3286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3286) = mixedMoment B node3286 node3286Labels := rfl
  simpa [nodeValue3286, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

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

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3527 node3527Labels = Sparse.eval nodeValue3527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3527) = mixedMoment B node3527 node3527Labels := rfl
  simpa [nodeValue3527, Sparse.eval] using hc.symm

theorem sound3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3528 node3528Labels = Sparse.eval nodeValue3528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3528) = mixedMoment B node3528 node3528Labels := rfl
  simpa [nodeValue3528, Sparse.eval] using hc.symm

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

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3566 node3566Labels = Sparse.eval nodeValue3566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3566) = mixedMoment B node3566 node3566Labels := rfl
  simpa [nodeValue3566, Sparse.eval] using hc.symm

theorem sound3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3567 node3567Labels = Sparse.eval nodeValue3567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3567) = mixedMoment B node3567 node3567Labels := rfl
  simpa [nodeValue3567, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

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

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

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

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

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

theorem sourceEq684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm684 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA684 + difference 0 1) (sourceB684 + difference 1 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA684 + difference 0 1) (sourceB684 + difference 1 0) sourceC684) = raw11604 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11604; decide +kernel
    rw [ha]
    exact (canonical11604 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA684 + difference 0 2) (sourceB684 + difference 2 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA684 + difference 0 2) (sourceB684 + difference 2 0) sourceC684) = raw11605 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11605; decide +kernel
    rw [ha]
    exact (canonical11605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA684 + difference 0 3) (sourceB684 + difference 3 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA684 + difference 0 3) (sourceB684 + difference 3 0) sourceC684) = raw11606 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11606; decide +kernel
    rw [ha]
    exact (canonical11606 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA684 + difference 0 4) (sourceB684 + difference 4 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA684 + difference 0 4) (sourceB684 + difference 4 0) sourceC684) = raw11607 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11607; decide +kernel
    rw [ha]
    exact (canonical11607 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA684 + difference 0 5) (sourceB684 + difference 5 0) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA684 + difference 0 5) (sourceB684 + difference 5 0) sourceC684) = raw11608 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11608; decide +kernel
    rw [ha]
    exact (canonical11608 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA684 + difference 1 0) (sourceB684 + difference 0 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA684 + difference 1 0) (sourceB684 + difference 0 1) sourceC684) = raw11609 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11609; decide +kernel
    rw [ha]
    exact (canonical11609 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA684 + difference 1 2) (sourceB684 + difference 2 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA684 + difference 1 2) (sourceB684 + difference 2 1) sourceC684) = raw11610 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11610; decide +kernel
    rw [ha]
    exact (canonical11610 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA684 + difference 1 3) (sourceB684 + difference 3 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA684 + difference 1 3) (sourceB684 + difference 3 1) sourceC684) = raw11611 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11611; decide +kernel
    rw [ha]
    exact (canonical11611 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA684 + difference 1 4) (sourceB684 + difference 4 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA684 + difference 1 4) (sourceB684 + difference 4 1) sourceC684) = raw11612 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11612; decide +kernel
    rw [ha]
    exact (canonical11612 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA684 + difference 1 5) (sourceB684 + difference 5 1) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA684 + difference 1 5) (sourceB684 + difference 5 1) sourceC684) = raw11613 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11613; decide +kernel
    rw [ha]
    exact (canonical11613 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA684 + difference 2 0) (sourceB684 + difference 0 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA684 + difference 2 0) (sourceB684 + difference 0 2) sourceC684) = raw11614 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11614; decide +kernel
    rw [ha]
    exact (canonical11614 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA684 + difference 2 1) (sourceB684 + difference 1 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA684 + difference 2 1) (sourceB684 + difference 1 2) sourceC684) = raw11615 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11615; decide +kernel
    rw [ha]
    exact (canonical11615 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA684 + difference 2 3) (sourceB684 + difference 3 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA684 + difference 2 3) (sourceB684 + difference 3 2) sourceC684) = raw11616 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11616; decide +kernel
    rw [ha]
    exact (canonical11616 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA684 + difference 2 4) (sourceB684 + difference 4 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA684 + difference 2 4) (sourceB684 + difference 4 2) sourceC684) = raw11617 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11617; decide +kernel
    rw [ha]
    exact (canonical11617 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA684 + difference 2 5) (sourceB684 + difference 5 2) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA684 + difference 2 5) (sourceB684 + difference 5 2) sourceC684) = raw11618 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11618; decide +kernel
    rw [ha]
    exact (canonical11618 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA684 + difference 3 0) (sourceB684 + difference 0 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA684 + difference 3 0) (sourceB684 + difference 0 3) sourceC684) = raw11619 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11619; decide +kernel
    rw [ha]
    exact (canonical11619 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA684 + difference 3 1) (sourceB684 + difference 1 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA684 + difference 3 1) (sourceB684 + difference 1 3) sourceC684) = raw11620 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11620; decide +kernel
    rw [ha]
    exact (canonical11620 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA684 + difference 3 2) (sourceB684 + difference 2 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA684 + difference 3 2) (sourceB684 + difference 2 3) sourceC684) = raw11621 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11621; decide +kernel
    rw [ha]
    exact (canonical11621 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA684 + difference 3 4) (sourceB684 + difference 4 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA684 + difference 3 4) (sourceB684 + difference 4 3) sourceC684) = raw11622 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11622; decide +kernel
    rw [ha]
    exact (canonical11622 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA684 + difference 3 5) (sourceB684 + difference 5 3) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA684 + difference 3 5) (sourceB684 + difference 5 3) sourceC684) = raw11623 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11623; decide +kernel
    rw [ha]
    exact (canonical11623 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA684 + difference 4 0) (sourceB684 + difference 0 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA684 + difference 4 0) (sourceB684 + difference 0 4) sourceC684) = raw11624 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11624; decide +kernel
    rw [ha]
    exact (canonical11624 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA684 + difference 4 1) (sourceB684 + difference 1 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA684 + difference 4 1) (sourceB684 + difference 1 4) sourceC684) = raw11625 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11625; decide +kernel
    rw [ha]
    exact (canonical11625 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA684 + difference 4 2) (sourceB684 + difference 2 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA684 + difference 4 2) (sourceB684 + difference 2 4) sourceC684) = raw11626 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11626; decide +kernel
    rw [ha]
    exact (canonical11626 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA684 + difference 4 3) (sourceB684 + difference 3 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA684 + difference 4 3) (sourceB684 + difference 3 4) sourceC684) = raw11627 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11627; decide +kernel
    rw [ha]
    exact (canonical11627 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA684 + difference 4 5) (sourceB684 + difference 5 4) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA684 + difference 4 5) (sourceB684 + difference 5 4) sourceC684) = raw11628 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11628; decide +kernel
    rw [ha]
    exact (canonical11628 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA684 + difference 5 0) (sourceB684 + difference 0 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA684 + difference 5 0) (sourceB684 + difference 0 5) sourceC684) = raw11629 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11629; decide +kernel
    rw [ha]
    exact (canonical11629 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA684 + difference 5 1) (sourceB684 + difference 1 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA684 + difference 5 1) (sourceB684 + difference 1 5) sourceC684) = raw11630 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11630; decide +kernel
    rw [ha]
    exact (canonical11630 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA684 + difference 5 2) (sourceB684 + difference 2 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA684 + difference 5 2) (sourceB684 + difference 2 5) sourceC684) = raw11631 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11631; decide +kernel
    rw [ha]
    exact (canonical11631 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA684 + difference 5 3) (sourceB684 + difference 3 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA684 + difference 5 3) (sourceB684 + difference 3 5) sourceC684) = raw11632 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11632; decide +kernel
    rw [ha]
    exact (canonical11632 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA684 + difference 5 4) (sourceB684 + difference 4 5) sourceC684) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA684 + difference 5 4) (sourceB684 + difference 4 5) sourceC684) = raw11633 := by
      apply Matrix.ext; unfold tripleCharges sourceA684 sourceB684 sourceC684 difference raw11633; decide +kernel
    rw [ha]
    exact (canonical11633 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA684 sourceB684 sourceC684
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm684, Integer.Sparse.eval]
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

theorem reindexCheck592 : Integer.Sparse.reindex keyMap MixedData.row592 = numericRow592 := by decide +kernel

theorem numericCheck592 (x : Master → ℝ) : Integer.Sparse.eval numericRow592 x =
    (4320 : ℝ) * reducedSource592 x := by
  norm_num [numericRow592, reducedSource592, Integer.Sparse.eval, Sparse.eval, nodeValue3285, nodeValue3286, nodeValue3288, nodeValue3289, nodeValue3459, nodeValue3460, nodeValue3463, nodeValue3524, nodeValue3526, nodeValue3527, nodeValue3528, nodeValue3533, nodeValue3534, nodeValue3540, nodeValue3566, nodeValue3567, nodeValue3572, nodeValue3800, nodeValue3846, nodeValue3847, nodeValue3852] <;> ring

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

theorem reducedZero592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource592 (mixedVector B) = 0 := by
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3527 : mixedVector B (Sum.inr 3527) = Sparse.eval nodeValue3527 (mixedVector B) := by
    change mixedMoment B node3527 node3527Labels = _
    exact sound3527 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3566 : mixedVector B (Sum.inr 3566) = Sparse.eval nodeValue3566 (mixedVector B) := by
    change mixedMoment B node3566 node3566Labels = _
    exact sound3566 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  simpa only [sourceForm684, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3285, h3286, h3288, h3289, h3459, h3460, h3463, h3524, h3526, h3527, h3528, h3533, h3534, h3540, h3566, h3567, h3572, h3800, h3846, h3847, h3852, reducedSource592] using sourceEq684 B hB

theorem rowSound592_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row592 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck592, numericCheck592, reducedZero592 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e_oai
