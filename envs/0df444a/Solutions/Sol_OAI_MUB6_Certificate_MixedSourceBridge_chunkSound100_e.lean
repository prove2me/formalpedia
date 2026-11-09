-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:30:39.820857+00:00
-- url     : https://prove2.me/submissions/ea0e7b0d-c746-4ed4-ba51-404602e4e602

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14360 raw14360Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14360 raw14360Labels = mixedMoment B raw14360step0 raw14360step0Labels := by
      have hz : ∀ j, raw14360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14360step0 = (fun i j => raw14360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14360step0 raw14360; decide +kernel
      have hl : raw14360step0Labels = raw14360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14360 raw14360Labels permutation346 hz
    mixedMoment B raw14360step0 raw14360step0Labels = mixedMoment B raw14360step1 raw14360step1Labels := by
      have hz : ∀ i, raw14360step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14360step1 = (fun i j => raw14360step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14360step1 raw14360step0; decide +kernel
      have hl : raw14360step1Labels = (fun j => raw14360step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14360step0 raw14360step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical14365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14365 raw14365Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw14365 raw14365Labels = mixedMoment B raw14365step0 raw14365step0Labels := by
      have hz : ∀ i, raw14365 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14365step0 = (fun i j => raw14365 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14365step0 raw14365; decide +kernel
      have hl : raw14365step0Labels = (fun j => raw14365Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14365 raw14365Labels permutation6 hz
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical14366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14366 raw14366Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14366 raw14366Labels = mixedMoment B raw14366step0 raw14366step0Labels := by
      have hz : ∀ j, raw14366 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14366step0 = (fun i j => raw14366 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14366step0 raw14366; decide +kernel
      have hl : raw14366step0Labels = raw14366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366 raw14366Labels permutation520 hz
    mixedMoment B raw14366step0 raw14366step0Labels = mixedMoment B raw14366step1 raw14366step1Labels := by
      have hz : ∀ j, raw14366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14366step1 = (fun i j => raw14366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14366step1 raw14366step0; decide +kernel
      have hl : raw14366step1Labels = raw14366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366step0 raw14366step0Labels permutation56 hz
    mixedMoment B raw14366step1 raw14366step1Labels = mixedMoment B raw14366step2 raw14366step2Labels := by
      have hz : ∀ i, raw14366step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14366step2 = (fun i j => raw14366step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14366step2 raw14366step1; decide +kernel
      have hl : raw14366step2Labels = (fun j => raw14366step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14366step1 raw14366step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical14367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14367 raw14367Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14367 raw14367Labels = mixedMoment B raw14367step0 raw14367step0Labels := by
      have hz : ∀ j, raw14367 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14367step0 = (fun i j => raw14367 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14367step0 raw14367; decide +kernel
      have hl : raw14367step0Labels = raw14367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367 raw14367Labels permutation590 hz
    mixedMoment B raw14367step0 raw14367step0Labels = mixedMoment B raw14367step1 raw14367step1Labels := by
      have hz : ∀ j, raw14367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14367step1 = (fun i j => raw14367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14367step1 raw14367step0; decide +kernel
      have hl : raw14367step1Labels = raw14367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367step0 raw14367step0Labels permutation56 hz
    mixedMoment B raw14367step1 raw14367step1Labels = mixedMoment B raw14367step2 raw14367step2Labels := by
      have hz : ∀ i, raw14367step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14367step2 = (fun i j => raw14367step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14367step2 raw14367step1; decide +kernel
      have hl : raw14367step2Labels = (fun j => raw14367step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14367step1 raw14367step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical14368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14368 raw14368Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14368 raw14368Labels = mixedMoment B raw14368step0 raw14368step0Labels := by
      have hz : ∀ j, raw14368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14368step0 = (fun i j => raw14368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14368step0 raw14368; decide +kernel
      have hl : raw14368step0Labels = raw14368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368 raw14368Labels permutation346 hz
    mixedMoment B raw14368step0 raw14368step0Labels = mixedMoment B raw14368step1 raw14368step1Labels := by
      have hz : ∀ j, raw14368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14368step1 = (fun i j => raw14368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14368step1 raw14368step0; decide +kernel
      have hl : raw14368step1Labels = raw14368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368step0 raw14368step0Labels permutation56 hz
    mixedMoment B raw14368step1 raw14368step1Labels = mixedMoment B raw14368step2 raw14368step2Labels := by
      have hz : ∀ i, raw14368step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14368step2 = (fun i j => raw14368step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14368step2 raw14368step1; decide +kernel
      have hl : raw14368step2Labels = (fun j => raw14368step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14368step1 raw14368step1Labels permutation6 hz
    mixedMoment B raw14368step2 raw14368step2Labels = mixedMoment B raw14368step3 raw14368step3Labels := by
      have ha : raw14368step3 = (fun i j => raw14368step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14368step3 raw14368step2; decide +kernel
      have hl : raw14368step3Labels = raw14368step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14368step2 raw14368step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical14373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14373 raw14373Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14373 raw14373Labels = mixedMoment B raw14373step0 raw14373step0Labels := by
      have hz : ∀ j, raw14373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14373step0 = (fun i j => raw14373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14373step0 raw14373; decide +kernel
      have hl : raw14373step0Labels = raw14373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373 raw14373Labels permutation346 hz
    mixedMoment B raw14373step0 raw14373step0Labels = mixedMoment B raw14373step1 raw14373step1Labels := by
      have hz : ∀ j, raw14373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14373step1 = (fun i j => raw14373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14373step1 raw14373step0; decide +kernel
      have hl : raw14373step1Labels = raw14373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373step0 raw14373step0Labels permutation56 hz
    mixedMoment B raw14373step1 raw14373step1Labels = mixedMoment B raw14373step2 raw14373step2Labels := by
      have hz : ∀ i, raw14373step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14373step2 = (fun i j => raw14373step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14373step2 raw14373step1; decide +kernel
      have hl : raw14373step2Labels = (fun j => raw14373step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14373step1 raw14373step1Labels permutation6 hz
    mixedMoment B raw14373step2 raw14373step2Labels = mixedMoment B raw14373step3 raw14373step3Labels := by
      have ha : raw14373step3 = (fun i j => raw14373step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14373step3 raw14373step2; decide +kernel
      have hl : raw14373step3Labels = raw14373step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14373step2 raw14373step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem canonical20089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20089 raw20089Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20089 raw20089Labels = mixedMoment B raw20089step0 raw20089step0Labels := by
      have hz : ∀ j, raw20089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20089step0 = (fun i j => raw20089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20089step0 raw20089; decide +kernel
      have hl : raw20089step0Labels = raw20089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089 raw20089Labels permutation434 hz
    mixedMoment B raw20089step0 raw20089step0Labels = mixedMoment B raw20089step1 raw20089step1Labels := by
      have hz : ∀ j, raw20089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20089step1 = (fun i j => raw20089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20089step1 raw20089step0; decide +kernel
      have hl : raw20089step1Labels = raw20089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089step0 raw20089step0Labels permutation80 hz
    _ = mixedMoment B node940 node940Labels := by rfl

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

theorem canonical20109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20109 raw20109Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw20109 raw20109Labels = mixedMoment B raw20109step0 raw20109step0Labels := by
      have hz : ∀ j, raw20109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20109step0 = (fun i j => raw20109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20109step0 raw20109; decide +kernel
      have hl : raw20109step0Labels = raw20109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20109 raw20109Labels permutation346 hz
    _ = mixedMoment B node931 node931Labels := by rfl

theorem canonical20113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20113 raw20113Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw20113 raw20113Labels = mixedMoment B raw20113step0 raw20113step0Labels := by
      have hz : ∀ j, raw20113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20113step0 = (fun i j => raw20113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20113step0 raw20113; decide +kernel
      have hl : raw20113step0Labels = raw20113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20113 raw20113Labels permutation346 hz
    _ = mixedMoment B node914 node914Labels := by rfl

theorem canonical20137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20137 raw20137Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw20137 raw20137Labels = mixedMoment B raw20137step0 raw20137step0Labels := by
      have hz : ∀ j, raw20137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20137step0 = (fun i j => raw20137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20137step0 raw20137; decide +kernel
      have hl : raw20137step0Labels = raw20137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20137 raw20137Labels permutation346 hz
    mixedMoment B raw20137step0 raw20137step0Labels = mixedMoment B raw20137step1 raw20137step1Labels := by
      have ha : raw20137step1 = (fun i j => raw20137step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20137step1 raw20137step0; decide +kernel
      have hl : raw20137step1Labels = raw20137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20137step0 raw20137step0Labels permutation34 permutation2
    _ = mixedMoment B node925 node925Labels := by rfl

theorem canonical20142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20142 raw20142Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20142 raw20142Labels = mixedMoment B raw20142step0 raw20142step0Labels := by
      have hz : ∀ j, raw20142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20142step0 = (fun i j => raw20142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20142step0 raw20142; decide +kernel
      have hl : raw20142step0Labels = raw20142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142 raw20142Labels permutation520 hz
    mixedMoment B raw20142step0 raw20142step0Labels = mixedMoment B raw20142step1 raw20142step1Labels := by
      have hz : ∀ j, raw20142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20142step1 = (fun i j => raw20142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20142step1 raw20142step0; decide +kernel
      have hl : raw20142step1Labels = raw20142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step0 raw20142step0Labels permutation80 hz
    mixedMoment B raw20142step1 raw20142step1Labels = mixedMoment B raw20142step2 raw20142step2Labels := by
      have hz : ∀ j, raw20142step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20142step2 = (fun i j => raw20142step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20142step2 raw20142step1; decide +kernel
      have hl : raw20142step2Labels = raw20142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step1 raw20142step1Labels permutation14 hz
    mixedMoment B raw20142step2 raw20142step2Labels = mixedMoment B raw20142step3 raw20142step3Labels := by
      have ha : raw20142step3 = (fun i j => raw20142step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20142step3 raw20142step2; decide +kernel
      have hl : raw20142step3Labels = raw20142step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20142step2 raw20142step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical20191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20191 raw20191Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw20191 raw20191Labels = mixedMoment B raw20191step0 raw20191step0Labels := by
      have ha : raw20191step0 = (fun i j => raw20191 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20191step0 raw20191; decide +kernel
      have hl : raw20191step0Labels = raw20191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20191 raw20191Labels permutation160 permutation2
    _ = mixedMoment B node905 node905Labels := by rfl

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

theorem canonical20218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20218 raw20218Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw20218 raw20218Labels = mixedMoment B raw20218step0 raw20218step0Labels := by
      have ha : raw20218step0 = (fun i j => raw20218 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20218step0 raw20218; decide +kernel
      have hl : raw20218step0Labels = raw20218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20218 raw20218Labels permutation158 permutation2
    _ = mixedMoment B node909 node909Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23784 raw23784Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23784 raw23784Labels = mixedMoment B raw23784step0 raw23784step0Labels := by
      have hz : ∀ j, raw23784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23784step0 = (fun i j => raw23784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23784step0 raw23784; decide +kernel
      have hl : raw23784step0Labels = raw23784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784 raw23784Labels permutation434 hz
    mixedMoment B raw23784step0 raw23784step0Labels = mixedMoment B raw23784step1 raw23784step1Labels := by
      have hz : ∀ j, raw23784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23784step1 = (fun i j => raw23784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23784step1 raw23784step0; decide +kernel
      have hl : raw23784step1Labels = raw23784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784step0 raw23784step0Labels permutation56 hz
    mixedMoment B raw23784step1 raw23784step1Labels = mixedMoment B raw23784step2 raw23784step2Labels := by
      have hz : ∀ i, raw23784step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23784step2 = (fun i j => raw23784step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23784step2 raw23784step1; decide +kernel
      have hl : raw23784step2Labels = (fun j => raw23784step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23784step1 raw23784step1Labels permutation6 hz
    mixedMoment B raw23784step2 raw23784step2Labels = mixedMoment B raw23784step3 raw23784step3Labels := by
      have ha : raw23784step3 = (fun i j => raw23784step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23784step3 raw23784step2; decide +kernel
      have hl : raw23784step3Labels = raw23784step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23784step2 raw23784step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26357 raw26357Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw26357 raw26357Labels = mixedMoment B raw26357step0 raw26357step0Labels := by
      have hz : ∀ j, raw26357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26357step0 = (fun i j => raw26357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26357step0 raw26357; decide +kernel
      have hl : raw26357step0Labels = raw26357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26357 raw26357Labels permutation265 hz
    mixedMoment B raw26357step0 raw26357step0Labels = mixedMoment B raw26357step1 raw26357step1Labels := by
      have hz : ∀ i, raw26357step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26357step1 = (fun i j => raw26357step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26357step1 raw26357step0; decide +kernel
      have hl : raw26357step1Labels = (fun j => raw26357step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26357step0 raw26357step0Labels permutation6 hz
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical26358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26358 raw26358Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26358 raw26358Labels = mixedMoment B raw26358step0 raw26358step0Labels := by
      have hz : ∀ i, raw26358 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26358step0 = (fun i j => raw26358 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26358step0 raw26358; decide +kernel
      have hl : raw26358step0Labels = (fun j => raw26358Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26358 raw26358Labels permutation6 hz
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical26359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26359 raw26359Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26359 raw26359Labels = mixedMoment B raw26359step0 raw26359step0Labels := by
      have hz : ∀ j, raw26359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26359step0 = (fun i j => raw26359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26359step0 raw26359; decide +kernel
      have hl : raw26359step0Labels = raw26359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359 raw26359Labels permutation520 hz
    mixedMoment B raw26359step0 raw26359step0Labels = mixedMoment B raw26359step1 raw26359step1Labels := by
      have hz : ∀ j, raw26359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26359step1 = (fun i j => raw26359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26359step1 raw26359step0; decide +kernel
      have hl : raw26359step1Labels = raw26359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359step0 raw26359step0Labels permutation56 hz
    mixedMoment B raw26359step1 raw26359step1Labels = mixedMoment B raw26359step2 raw26359step2Labels := by
      have hz : ∀ i, raw26359step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26359step2 = (fun i j => raw26359step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26359step2 raw26359step1; decide +kernel
      have hl : raw26359step2Labels = (fun j => raw26359step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26359step1 raw26359step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem canonical27293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27293 raw27293Labels = mixedMoment B node4056 node4056Labels := by
  calc
    mixedMoment B raw27293 raw27293Labels = mixedMoment B raw27293step0 raw27293step0Labels := by
      have hz : ∀ i, raw27293 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27293step0 = (fun i j => raw27293 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27293step0 raw27293; decide +kernel
      have hl : raw27293step0Labels = (fun j => raw27293Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27293 raw27293Labels permutation6 hz
    _ = mixedMoment B node4056 node4056Labels := by rfl

theorem canonical27294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27294 raw27294Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27294 raw27294Labels = mixedMoment B raw27294step0 raw27294step0Labels := by
      have hz : ∀ j, raw27294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27294step0 = (fun i j => raw27294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27294step0 raw27294; decide +kernel
      have hl : raw27294step0Labels = raw27294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27294 raw27294Labels permutation434 hz
    mixedMoment B raw27294step0 raw27294step0Labels = mixedMoment B raw27294step1 raw27294step1Labels := by
      have hz : ∀ i, raw27294step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27294step1 = (fun i j => raw27294step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27294step1 raw27294step0; decide +kernel
      have hl : raw27294step1Labels = (fun j => raw27294step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27294step0 raw27294step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical27295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27295 raw27295Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27295 raw27295Labels = mixedMoment B raw27295step0 raw27295step0Labels := by
      have hz : ∀ j, raw27295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27295step0 = (fun i j => raw27295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27295step0 raw27295; decide +kernel
      have hl : raw27295step0Labels = raw27295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27295 raw27295Labels permutation520 hz
    mixedMoment B raw27295step0 raw27295step0Labels = mixedMoment B raw27295step1 raw27295step1Labels := by
      have hz : ∀ i, raw27295step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27295step1 = (fun i j => raw27295step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27295step1 raw27295step0; decide +kernel
      have hl : raw27295step1Labels = (fun j => raw27295step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27295step0 raw27295step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical27296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27296 raw27296Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27296 raw27296Labels = mixedMoment B raw27296step0 raw27296step0Labels := by
      have hz : ∀ j, raw27296 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27296step0 = (fun i j => raw27296 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27296step0 raw27296; decide +kernel
      have hl : raw27296step0Labels = raw27296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27296 raw27296Labels permutation590 hz
    mixedMoment B raw27296step0 raw27296step0Labels = mixedMoment B raw27296step1 raw27296step1Labels := by
      have hz : ∀ i, raw27296step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27296step1 = (fun i j => raw27296step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27296step1 raw27296step0; decide +kernel
      have hl : raw27296step1Labels = (fun j => raw27296step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27296step0 raw27296step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical27297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27297 raw27297Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27297 raw27297Labels = mixedMoment B raw27297step0 raw27297step0Labels := by
      have hz : ∀ j, raw27297 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27297step0 = (fun i j => raw27297 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27297step0 raw27297; decide +kernel
      have hl : raw27297step0Labels = raw27297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27297 raw27297Labels permutation265 hz
    mixedMoment B raw27297step0 raw27297step0Labels = mixedMoment B raw27297step1 raw27297step1Labels := by
      have hz : ∀ i, raw27297step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27297step1 = (fun i j => raw27297step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27297step1 raw27297step0; decide +kernel
      have hl : raw27297step1Labels = (fun j => raw27297step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27297step0 raw27297step0Labels permutation6 hz
    mixedMoment B raw27297step1 raw27297step1Labels = mixedMoment B raw27297step2 raw27297step2Labels := by
      have ha : raw27297step2 = (fun i j => raw27297step1 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27297step2 raw27297step1; decide +kernel
      have hl : raw27297step2Labels = raw27297step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27297step1 raw27297step1Labels permutation41 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical27298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27298 raw27298Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27298 raw27298Labels = mixedMoment B raw27298step0 raw27298step0Labels := by
      have hz : ∀ i, raw27298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27298step0 = (fun i j => raw27298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27298step0 raw27298; decide +kernel
      have hl : raw27298step0Labels = (fun j => raw27298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27298 raw27298Labels permutation6 hz
    mixedMoment B raw27298step0 raw27298step0Labels = mixedMoment B raw27298step1 raw27298step1Labels := by
      have ha : raw27298step1 = (fun i j => raw27298step0 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27298step1 raw27298step0; decide +kernel
      have hl : raw27298step1Labels = raw27298step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27298step0 raw27298step0Labels permutation161 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical27299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27299 raw27299Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27299 raw27299Labels = mixedMoment B raw27299step0 raw27299step0Labels := by
      have hz : ∀ j, raw27299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27299step0 = (fun i j => raw27299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27299step0 raw27299; decide +kernel
      have hl : raw27299step0Labels = raw27299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27299 raw27299Labels permutation434 hz
    mixedMoment B raw27299step0 raw27299step0Labels = mixedMoment B raw27299step1 raw27299step1Labels := by
      have hz : ∀ j, raw27299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27299step1 = (fun i j => raw27299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27299step1 raw27299step0; decide +kernel
      have hl : raw27299step1Labels = raw27299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27299step0 raw27299step0Labels permutation56 hz
    mixedMoment B raw27299step1 raw27299step1Labels = mixedMoment B raw27299step2 raw27299step2Labels := by
      have hz : ∀ i, raw27299step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27299step2 = (fun i j => raw27299step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27299step2 raw27299step1; decide +kernel
      have hl : raw27299step2Labels = (fun j => raw27299step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27299step1 raw27299step1Labels permutation6 hz
    mixedMoment B raw27299step2 raw27299step2Labels = mixedMoment B raw27299step3 raw27299step3Labels := by
      have ha : raw27299step3 = (fun i j => raw27299step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27299step3 raw27299step2; decide +kernel
      have hl : raw27299step3Labels = raw27299step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27299step2 raw27299step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27300 raw27300Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27300 raw27300Labels = mixedMoment B raw27300step0 raw27300step0Labels := by
      have hz : ∀ j, raw27300 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27300step0 = (fun i j => raw27300 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27300step0 raw27300; decide +kernel
      have hl : raw27300step0Labels = raw27300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27300 raw27300Labels permutation520 hz
    mixedMoment B raw27300step0 raw27300step0Labels = mixedMoment B raw27300step1 raw27300step1Labels := by
      have hz : ∀ j, raw27300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27300step1 = (fun i j => raw27300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27300step1 raw27300step0; decide +kernel
      have hl : raw27300step1Labels = raw27300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27300step0 raw27300step0Labels permutation56 hz
    mixedMoment B raw27300step1 raw27300step1Labels = mixedMoment B raw27300step2 raw27300step2Labels := by
      have hz : ∀ i, raw27300step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27300step2 = (fun i j => raw27300step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27300step2 raw27300step1; decide +kernel
      have hl : raw27300step2Labels = (fun j => raw27300step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27300step1 raw27300step1Labels permutation6 hz
    mixedMoment B raw27300step2 raw27300step2Labels = mixedMoment B raw27300step3 raw27300step3Labels := by
      have ha : raw27300step3 = (fun i j => raw27300step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27300step3 raw27300step2; decide +kernel
      have hl : raw27300step3Labels = raw27300step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27300step2 raw27300step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27301 raw27301Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27301 raw27301Labels = mixedMoment B raw27301step0 raw27301step0Labels := by
      have hz : ∀ j, raw27301 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27301step0 = (fun i j => raw27301 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27301step0 raw27301; decide +kernel
      have hl : raw27301step0Labels = raw27301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27301 raw27301Labels permutation590 hz
    mixedMoment B raw27301step0 raw27301step0Labels = mixedMoment B raw27301step1 raw27301step1Labels := by
      have hz : ∀ j, raw27301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27301step1 = (fun i j => raw27301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27301step1 raw27301step0; decide +kernel
      have hl : raw27301step1Labels = raw27301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27301step0 raw27301step0Labels permutation56 hz
    mixedMoment B raw27301step1 raw27301step1Labels = mixedMoment B raw27301step2 raw27301step2Labels := by
      have hz : ∀ i, raw27301step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27301step2 = (fun i j => raw27301step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27301step2 raw27301step1; decide +kernel
      have hl : raw27301step2Labels = (fun j => raw27301step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27301step1 raw27301step1Labels permutation6 hz
    mixedMoment B raw27301step2 raw27301step2Labels = mixedMoment B raw27301step3 raw27301step3Labels := by
      have ha : raw27301step3 = (fun i j => raw27301step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27301step3 raw27301step2; decide +kernel
      have hl : raw27301step3Labels = raw27301step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27301step2 raw27301step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27302 raw27302Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27302 raw27302Labels = mixedMoment B raw27302step0 raw27302step0Labels := by
      have hz : ∀ j, raw27302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27302step0 = (fun i j => raw27302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27302step0 raw27302; decide +kernel
      have hl : raw27302step0Labels = raw27302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27302 raw27302Labels permutation265 hz
    mixedMoment B raw27302step0 raw27302step0Labels = mixedMoment B raw27302step1 raw27302step1Labels := by
      have hz : ∀ i, raw27302step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27302step1 = (fun i j => raw27302step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27302step1 raw27302step0; decide +kernel
      have hl : raw27302step1Labels = (fun j => raw27302step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27302step0 raw27302step0Labels permutation6 hz
    mixedMoment B raw27302step1 raw27302step1Labels = mixedMoment B raw27302step2 raw27302step2Labels := by
      have ha : raw27302step2 = (fun i j => raw27302step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27302step2 raw27302step1; decide +kernel
      have hl : raw27302step2Labels = raw27302step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27302step1 raw27302step1Labels permutation35 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical27303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27303 raw27303Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27303 raw27303Labels = mixedMoment B raw27303step0 raw27303step0Labels := by
      have hz : ∀ i, raw27303 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27303step0 = (fun i j => raw27303 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27303step0 raw27303; decide +kernel
      have hl : raw27303step0Labels = (fun j => raw27303Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27303 raw27303Labels permutation6 hz
    mixedMoment B raw27303step0 raw27303step0Labels = mixedMoment B raw27303step1 raw27303step1Labels := by
      have ha : raw27303step1 = (fun i j => raw27303step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27303step1 raw27303step0; decide +kernel
      have hl : raw27303step1Labels = raw27303step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27303step0 raw27303step0Labels permutation155 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical27304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27304 raw27304Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27304 raw27304Labels = mixedMoment B raw27304step0 raw27304step0Labels := by
      have hz : ∀ j, raw27304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27304step0 = (fun i j => raw27304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27304step0 raw27304; decide +kernel
      have hl : raw27304step0Labels = raw27304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27304 raw27304Labels permutation520 hz
    mixedMoment B raw27304step0 raw27304step0Labels = mixedMoment B raw27304step1 raw27304step1Labels := by
      have hz : ∀ j, raw27304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27304step1 = (fun i j => raw27304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27304step1 raw27304step0; decide +kernel
      have hl : raw27304step1Labels = raw27304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27304step0 raw27304step0Labels permutation56 hz
    mixedMoment B raw27304step1 raw27304step1Labels = mixedMoment B raw27304step2 raw27304step2Labels := by
      have hz : ∀ i, raw27304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27304step2 = (fun i j => raw27304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27304step2 raw27304step1; decide +kernel
      have hl : raw27304step2Labels = (fun j => raw27304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27304step1 raw27304step1Labels permutation6 hz
    mixedMoment B raw27304step2 raw27304step2Labels = mixedMoment B raw27304step3 raw27304step3Labels := by
      have ha : raw27304step3 = (fun i j => raw27304step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27304step3 raw27304step2; decide +kernel
      have hl : raw27304step3Labels = raw27304step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27304step2 raw27304step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27305 raw27305Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27305 raw27305Labels = mixedMoment B raw27305step0 raw27305step0Labels := by
      have hz : ∀ j, raw27305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27305step0 = (fun i j => raw27305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27305step0 raw27305; decide +kernel
      have hl : raw27305step0Labels = raw27305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27305 raw27305Labels permutation590 hz
    mixedMoment B raw27305step0 raw27305step0Labels = mixedMoment B raw27305step1 raw27305step1Labels := by
      have hz : ∀ j, raw27305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27305step1 = (fun i j => raw27305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27305step1 raw27305step0; decide +kernel
      have hl : raw27305step1Labels = raw27305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27305step0 raw27305step0Labels permutation56 hz
    mixedMoment B raw27305step1 raw27305step1Labels = mixedMoment B raw27305step2 raw27305step2Labels := by
      have hz : ∀ i, raw27305step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27305step2 = (fun i j => raw27305step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27305step2 raw27305step1; decide +kernel
      have hl : raw27305step2Labels = (fun j => raw27305step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27305step1 raw27305step1Labels permutation6 hz
    mixedMoment B raw27305step2 raw27305step2Labels = mixedMoment B raw27305step3 raw27305step3Labels := by
      have ha : raw27305step3 = (fun i j => raw27305step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27305step3 raw27305step2; decide +kernel
      have hl : raw27305step3Labels = raw27305step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27305step2 raw27305step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27306 raw27306Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27306 raw27306Labels = mixedMoment B raw27306step0 raw27306step0Labels := by
      have hz : ∀ j, raw27306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27306step0 = (fun i j => raw27306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27306step0 raw27306; decide +kernel
      have hl : raw27306step0Labels = raw27306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27306 raw27306Labels permutation265 hz
    mixedMoment B raw27306step0 raw27306step0Labels = mixedMoment B raw27306step1 raw27306step1Labels := by
      have hz : ∀ i, raw27306step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27306step1 = (fun i j => raw27306step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27306step1 raw27306step0; decide +kernel
      have hl : raw27306step1Labels = (fun j => raw27306step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27306step0 raw27306step0Labels permutation6 hz
    mixedMoment B raw27306step1 raw27306step1Labels = mixedMoment B raw27306step2 raw27306step2Labels := by
      have ha : raw27306step2 = (fun i j => raw27306step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27306step2 raw27306step1; decide +kernel
      have hl : raw27306step2Labels = raw27306step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27306step1 raw27306step1Labels permutation33 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

theorem canonical27307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27307 raw27307Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27307 raw27307Labels = mixedMoment B raw27307step0 raw27307step0Labels := by
      have hz : ∀ i, raw27307 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27307step0 = (fun i j => raw27307 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27307step0 raw27307; decide +kernel
      have hl : raw27307step0Labels = (fun j => raw27307Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27307 raw27307Labels permutation6 hz
    mixedMoment B raw27307step0 raw27307step0Labels = mixedMoment B raw27307step1 raw27307step1Labels := by
      have ha : raw27307step1 = (fun i j => raw27307step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27307step1 raw27307step0; decide +kernel
      have hl : raw27307step1Labels = raw27307step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27307step0 raw27307step0Labels permutation153 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

theorem canonical27308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27308 raw27308Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27308 raw27308Labels = mixedMoment B raw27308step0 raw27308step0Labels := by
      have hz : ∀ j, raw27308 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27308step0 = (fun i j => raw27308 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27308step0 raw27308; decide +kernel
      have hl : raw27308step0Labels = raw27308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27308 raw27308Labels permutation590 hz
    mixedMoment B raw27308step0 raw27308step0Labels = mixedMoment B raw27308step1 raw27308step1Labels := by
      have hz : ∀ j, raw27308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27308step1 = (fun i j => raw27308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27308step1 raw27308step0; decide +kernel
      have hl : raw27308step1Labels = raw27308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27308step0 raw27308step0Labels permutation56 hz
    mixedMoment B raw27308step1 raw27308step1Labels = mixedMoment B raw27308step2 raw27308step2Labels := by
      have hz : ∀ i, raw27308step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27308step2 = (fun i j => raw27308step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27308step2 raw27308step1; decide +kernel
      have hl : raw27308step2Labels = (fun j => raw27308step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27308step1 raw27308step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical27309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27309 raw27309Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw27309 raw27309Labels = mixedMoment B raw27309step0 raw27309step0Labels := by
      have hz : ∀ j, raw27309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27309step0 = (fun i j => raw27309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27309step0 raw27309; decide +kernel
      have hl : raw27309step0Labels = raw27309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309 raw27309Labels permutation434 hz
    mixedMoment B raw27309step0 raw27309step0Labels = mixedMoment B raw27309step1 raw27309step1Labels := by
      have hz : ∀ j, raw27309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27309step1 = (fun i j => raw27309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27309step1 raw27309step0; decide +kernel
      have hl : raw27309step1Labels = raw27309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309step0 raw27309step0Labels permutation80 hz
    _ = mixedMoment B node1820 node1820Labels := by rfl

theorem canonical27310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27310 raw27310Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw27310 raw27310Labels = mixedMoment B raw27310step0 raw27310step0Labels := by
      have hz : ∀ j, raw27310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27310step0 = (fun i j => raw27310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27310step0 raw27310; decide +kernel
      have hl : raw27310step0Labels = raw27310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27310 raw27310Labels permutation434 hz
    _ = mixedMoment B node1971 node1971Labels := by rfl

theorem canonical27311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27311 raw27311Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw27311 raw27311Labels = mixedMoment B raw27311step0 raw27311step0Labels := by
      have hz : ∀ j, raw27311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27311step0 = (fun i j => raw27311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27311step0 raw27311; decide +kernel
      have hl : raw27311step0Labels = raw27311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27311 raw27311Labels permutation346 hz
    _ = mixedMoment B node1971 node1971Labels := by rfl

theorem canonical27312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27312 raw27312Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw27312 raw27312Labels = mixedMoment B raw27312step0 raw27312step0Labels := by
      have hz : ∀ j, raw27312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27312step0 = (fun i j => raw27312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27312step0 raw27312; decide +kernel
      have hl : raw27312step0Labels = raw27312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312 raw27312Labels permutation434 hz
    mixedMoment B raw27312step0 raw27312step0Labels = mixedMoment B raw27312step1 raw27312step1Labels := by
      have hz : ∀ j, raw27312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27312step1 = (fun i j => raw27312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27312step1 raw27312step0; decide +kernel
      have hl : raw27312step1Labels = raw27312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312step0 raw27312step0Labels permutation80 hz
    mixedMoment B raw27312step1 raw27312step1Labels = mixedMoment B raw27312step2 raw27312step2Labels := by
      have ha : raw27312step2 = (fun i j => raw27312step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27312step2 raw27312step1; decide +kernel
      have hl : raw27312step2Labels = raw27312step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27312step1 raw27312step1Labels permutation9 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical27313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27313 raw27313Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27313 raw27313Labels = mixedMoment B raw27313step0 raw27313step0Labels := by
      have hz : ∀ j, raw27313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27313step0 = (fun i j => raw27313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27313step0 raw27313; decide +kernel
      have hl : raw27313step0Labels = raw27313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27313 raw27313Labels permutation434 hz
    mixedMoment B raw27313step0 raw27313step0Labels = mixedMoment B raw27313step1 raw27313step1Labels := by
      have hz : ∀ j, raw27313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27313step1 = (fun i j => raw27313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27313step1 raw27313step0; decide +kernel
      have hl : raw27313step1Labels = raw27313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27313step0 raw27313step0Labels permutation80 hz
    mixedMoment B raw27313step1 raw27313step1Labels = mixedMoment B raw27313step2 raw27313step2Labels := by
      have ha : raw27313step2 = (fun i j => raw27313step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27313step2 raw27313step1; decide +kernel
      have hl : raw27313step2Labels = raw27313step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27313step1 raw27313step1Labels permutation31 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical27314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27314 raw27314Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw27314 raw27314Labels = mixedMoment B raw27314step0 raw27314step0Labels := by
      have hz : ∀ j, raw27314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27314step0 = (fun i j => raw27314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27314step0 raw27314; decide +kernel
      have hl : raw27314step0Labels = raw27314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27314 raw27314Labels permutation434 hz
    mixedMoment B raw27314step0 raw27314step0Labels = mixedMoment B raw27314step1 raw27314step1Labels := by
      have hz : ∀ j, raw27314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27314step1 = (fun i j => raw27314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27314step1 raw27314step0; decide +kernel
      have hl : raw27314step1Labels = raw27314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27314step0 raw27314step0Labels permutation80 hz
    mixedMoment B raw27314step1 raw27314step1Labels = mixedMoment B raw27314step2 raw27314step2Labels := by
      have ha : raw27314step2 = (fun i j => raw27314step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27314step2 raw27314step1; decide +kernel
      have hl : raw27314step2Labels = raw27314step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27314step1 raw27314step1Labels permutation27 permutation2
    _ = mixedMoment B node2282 node2282Labels := by rfl

theorem canonical27315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27315 raw27315Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27315 raw27315Labels = mixedMoment B raw27315step0 raw27315step0Labels := by
      have hz : ∀ j, raw27315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27315step0 = (fun i j => raw27315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27315step0 raw27315; decide +kernel
      have hl : raw27315step0Labels = raw27315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27315 raw27315Labels permutation434 hz
    mixedMoment B raw27315step0 raw27315step0Labels = mixedMoment B raw27315step1 raw27315step1Labels := by
      have ha : raw27315step1 = (fun i j => raw27315step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27315step1 raw27315step0; decide +kernel
      have hl : raw27315step1Labels = raw27315step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27315step0 raw27315step0Labels permutation36 permutation4
    mixedMoment B raw27315step1 raw27315step1Labels = mixedMoment B raw27315step2 raw27315step2Labels := by
      have ha : raw27315step2 = -raw27315step1 := by apply Matrix.ext; change ∀ i j, raw27315step2 i j = -(raw27315step1 i j); unfold raw27315step2 raw27315step1; decide +kernel
      have hl : raw27315step2Labels = raw27315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical27316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27316 raw27316Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27316 raw27316Labels = mixedMoment B raw27316step0 raw27316step0Labels := by
      have hz : ∀ j, raw27316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27316step0 = (fun i j => raw27316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27316step0 raw27316; decide +kernel
      have hl : raw27316step0Labels = raw27316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27316 raw27316Labels permutation346 hz
    mixedMoment B raw27316step0 raw27316step0Labels = mixedMoment B raw27316step1 raw27316step1Labels := by
      have ha : raw27316step1 = (fun i j => raw27316step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27316step1 raw27316step0; decide +kernel
      have hl : raw27316step1Labels = raw27316step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27316step0 raw27316step0Labels permutation36 permutation4
    mixedMoment B raw27316step1 raw27316step1Labels = mixedMoment B raw27316step2 raw27316step2Labels := by
      have ha : raw27316step2 = -raw27316step1 := by apply Matrix.ext; change ∀ i j, raw27316step2 i j = -(raw27316step1 i j); unfold raw27316step2 raw27316step1; decide +kernel
      have hl : raw27316step2Labels = raw27316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical27317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27317 raw27317Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw27317 raw27317Labels = mixedMoment B raw27317step0 raw27317step0Labels := by
      have hz : ∀ j, raw27317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27317step0 = (fun i j => raw27317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27317step0 raw27317; decide +kernel
      have hl : raw27317step0Labels = raw27317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27317 raw27317Labels permutation434 hz
    mixedMoment B raw27317step0 raw27317step0Labels = mixedMoment B raw27317step1 raw27317step1Labels := by
      have hz : ∀ j, raw27317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27317step1 = (fun i j => raw27317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27317step1 raw27317step0; decide +kernel
      have hl : raw27317step1Labels = raw27317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27317step0 raw27317step0Labels permutation80 hz
    mixedMoment B raw27317step1 raw27317step1Labels = mixedMoment B raw27317step2 raw27317step2Labels := by
      have ha : raw27317step2 = (fun i j => raw27317step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27317step2 raw27317step1; decide +kernel
      have hl : raw27317step2Labels = raw27317step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27317step1 raw27317step1Labels permutation9 permutation4
    mixedMoment B raw27317step2 raw27317step2Labels = mixedMoment B raw27317step3 raw27317step3Labels := by
      have ha : raw27317step3 = -raw27317step2 := by apply Matrix.ext; change ∀ i j, raw27317step3 i j = -(raw27317step2 i j); unfold raw27317step3 raw27317step2; decide +kernel
      have hl : raw27317step3Labels = raw27317step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2222 node2222Labels := by rfl

theorem canonical27318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27318 raw27318Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw27318 raw27318Labels = mixedMoment B raw27318step0 raw27318step0Labels := by
      have hz : ∀ j, raw27318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27318step0 = (fun i j => raw27318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27318step0 raw27318; decide +kernel
      have hl : raw27318step0Labels = raw27318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318 raw27318Labels permutation434 hz
    mixedMoment B raw27318step0 raw27318step0Labels = mixedMoment B raw27318step1 raw27318step1Labels := by
      have hz : ∀ j, raw27318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27318step1 = (fun i j => raw27318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27318step1 raw27318step0; decide +kernel
      have hl : raw27318step1Labels = raw27318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318step0 raw27318step0Labels permutation80 hz
    mixedMoment B raw27318step1 raw27318step1Labels = mixedMoment B raw27318step2 raw27318step2Labels := by
      have ha : raw27318step2 = (fun i j => raw27318step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27318step2 raw27318step1; decide +kernel
      have hl : raw27318step2Labels = raw27318step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27318step1 raw27318step1Labels permutation9 permutation4
    mixedMoment B raw27318step2 raw27318step2Labels = mixedMoment B raw27318step3 raw27318step3Labels := by
      have ha : raw27318step3 = -raw27318step2 := by apply Matrix.ext; change ∀ i j, raw27318step3 i j = -(raw27318step2 i j); unfold raw27318step3 raw27318step2; decide +kernel
      have hl : raw27318step3Labels = raw27318step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27320 raw27320Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw27320 raw27320Labels = mixedMoment B raw27320step0 raw27320step0Labels := by
      have hz : ∀ j, raw27320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27320step0 = (fun i j => raw27320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27320step0 raw27320; decide +kernel
      have hl : raw27320step0Labels = raw27320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27320 raw27320Labels permutation346 hz
    _ = mixedMoment B node1813 node1813Labels := by rfl

theorem canonical27321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27321 raw27321Labels = mixedMoment B node1965 node1965Labels := by
  calc
    _ = mixedMoment B node1965 node1965Labels := by rfl

theorem canonical27322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27322 raw27322Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw27322 raw27322Labels = mixedMoment B raw27322step0 raw27322step0Labels := by
      have hz : ∀ j, raw27322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27322step0 = (fun i j => raw27322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27322step0 raw27322; decide +kernel
      have hl : raw27322step0Labels = raw27322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27322 raw27322Labels permutation346 hz
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical27323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27323 raw27323Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw27323 raw27323Labels = mixedMoment B raw27323step0 raw27323step0Labels := by
      have hz : ∀ j, raw27323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27323step0 = (fun i j => raw27323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27323step0 raw27323; decide +kernel
      have hl : raw27323step0Labels = raw27323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27323 raw27323Labels permutation346 hz
    _ = mixedMoment B node1797 node1797Labels := by rfl

theorem canonical27324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27324 raw27324Labels = mixedMoment B node1957 node1957Labels := by
  calc
    _ = mixedMoment B node1957 node1957Labels := by rfl

theorem canonical27325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27325 raw27325Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27325 raw27325Labels = mixedMoment B raw27325step0 raw27325step0Labels := by
      have hz : ∀ j, raw27325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27325step0 = (fun i j => raw27325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27325step0 raw27325; decide +kernel
      have hl : raw27325step0Labels = raw27325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27325 raw27325Labels permutation346 hz
    _ = mixedMoment B node1980 node1980Labels := by rfl

theorem canonical27326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27326 raw27326Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw27326 raw27326Labels = mixedMoment B raw27326step0 raw27326step0Labels := by
      have hz : ∀ j, raw27326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27326step0 = (fun i j => raw27326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27326step0 raw27326; decide +kernel
      have hl : raw27326step0Labels = raw27326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27326 raw27326Labels permutation346 hz
    mixedMoment B raw27326step0 raw27326step0Labels = mixedMoment B raw27326step1 raw27326step1Labels := by
      have ha : raw27326step1 = (fun i j => raw27326step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27326step1 raw27326step0; decide +kernel
      have hl : raw27326step1Labels = raw27326step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27326step0 raw27326step0Labels permutation33 permutation2
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical27327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27327 raw27327Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw27327 raw27327Labels = mixedMoment B raw27327step0 raw27327step0Labels := by
      have hz : ∀ j, raw27327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27327step0 = (fun i j => raw27327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27327step0 raw27327; decide +kernel
      have hl : raw27327step0Labels = raw27327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27327 raw27327Labels permutation346 hz
    mixedMoment B raw27327step0 raw27327step0Labels = mixedMoment B raw27327step1 raw27327step1Labels := by
      have ha : raw27327step1 = (fun i j => raw27327step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27327step1 raw27327step0; decide +kernel
      have hl : raw27327step1Labels = raw27327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27327step0 raw27327step0Labels permutation149 permutation2
    mixedMoment B raw27327step1 raw27327step1Labels = mixedMoment B raw27327step2 raw27327step2Labels := by
      have ha : raw27327step2 = -raw27327step1 := by apply Matrix.ext; change ∀ i j, raw27327step2 i j = -(raw27327step1 i j); unfold raw27327step2 raw27327step1; decide +kernel
      have hl : raw27327step2Labels = raw27327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical27328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27328 raw27328Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27328 raw27328Labels = mixedMoment B raw27328step0 raw27328step0Labels := by
      have hz : ∀ j, raw27328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27328step0 = (fun i j => raw27328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27328step0 raw27328; decide +kernel
      have hl : raw27328step0Labels = raw27328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27328 raw27328Labels permutation346 hz
    mixedMoment B raw27328step0 raw27328step0Labels = mixedMoment B raw27328step1 raw27328step1Labels := by
      have ha : raw27328step1 = (fun i j => raw27328step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27328step1 raw27328step0; decide +kernel
      have hl : raw27328step1Labels = raw27328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27328step0 raw27328step0Labels permutation149 permutation2
    mixedMoment B raw27328step1 raw27328step1Labels = mixedMoment B raw27328step2 raw27328step2Labels := by
      have ha : raw27328step2 = -raw27328step1 := by apply Matrix.ext; change ∀ i j, raw27328step2 i j = -(raw27328step1 i j); unfold raw27328step2 raw27328step1; decide +kernel
      have hl : raw27328step2Labels = raw27328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical27329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27329 raw27329Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw27329 raw27329Labels = mixedMoment B raw27329step0 raw27329step0Labels := by
      have ha : raw27329step0 = (fun i j => raw27329 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27329step0 raw27329; decide +kernel
      have hl : raw27329step0Labels = raw27329Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27329 raw27329Labels permutation644 permutation2
    mixedMoment B raw27329step0 raw27329step0Labels = mixedMoment B raw27329step1 raw27329step1Labels := by
      have ha : raw27329step1 = -raw27329step0 := by apply Matrix.ext; change ∀ i j, raw27329step1 i j = -(raw27329step0 i j); unfold raw27329step1 raw27329step0; decide +kernel
      have hl : raw27329step1Labels = raw27329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1976 node1976Labels := by rfl

theorem canonical27330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27330 raw27330Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27330 raw27330Labels = mixedMoment B raw27330step0 raw27330step0Labels := by
      have hz : ∀ j, raw27330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27330step0 = (fun i j => raw27330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27330step0 raw27330; decide +kernel
      have hl : raw27330step0Labels = raw27330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27330 raw27330Labels permutation346 hz
    mixedMoment B raw27330step0 raw27330step0Labels = mixedMoment B raw27330step1 raw27330step1Labels := by
      have ha : raw27330step1 = (fun i j => raw27330step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27330step1 raw27330step0; decide +kernel
      have hl : raw27330step1Labels = raw27330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27330step0 raw27330step0Labels permutation151 permutation2
    mixedMoment B raw27330step1 raw27330step1Labels = mixedMoment B raw27330step2 raw27330step2Labels := by
      have ha : raw27330step2 = -raw27330step1 := by apply Matrix.ext; change ∀ i j, raw27330step2 i j = -(raw27330step1 i j); unfold raw27330step2 raw27330step1; decide +kernel
      have hl : raw27330step2Labels = raw27330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical27331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27331 raw27331Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw27331 raw27331Labels = mixedMoment B raw27331step0 raw27331step0Labels := by
      have hz : ∀ j, raw27331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27331step0 = (fun i j => raw27331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27331step0 raw27331; decide +kernel
      have hl : raw27331step0Labels = raw27331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27331 raw27331Labels permutation346 hz
    mixedMoment B raw27331step0 raw27331step0Labels = mixedMoment B raw27331step1 raw27331step1Labels := by
      have ha : raw27331step1 = (fun i j => raw27331step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27331step1 raw27331step0; decide +kernel
      have hl : raw27331step1Labels = raw27331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27331step0 raw27331step0Labels permutation149 permutation2
    mixedMoment B raw27331step1 raw27331step1Labels = mixedMoment B raw27331step2 raw27331step2Labels := by
      have ha : raw27331step2 = -raw27331step1 := by apply Matrix.ext; change ∀ i j, raw27331step2 i j = -(raw27331step1 i j); unfold raw27331step2 raw27331step1; decide +kernel
      have hl : raw27331step2Labels = raw27331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1828 node1828Labels := by rfl

theorem canonical27332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27332 raw27332Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw27332 raw27332Labels = mixedMoment B raw27332step0 raw27332step0Labels := by
      have hz : ∀ j, raw27332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27332step0 = (fun i j => raw27332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27332step0 raw27332; decide +kernel
      have hl : raw27332step0Labels = raw27332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27332 raw27332Labels permutation346 hz
    mixedMoment B raw27332step0 raw27332step0Labels = mixedMoment B raw27332step1 raw27332step1Labels := by
      have ha : raw27332step1 = (fun i j => raw27332step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27332step1 raw27332step0; decide +kernel
      have hl : raw27332step1Labels = raw27332step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27332step0 raw27332step0Labels permutation149 permutation2
    mixedMoment B raw27332step1 raw27332step1Labels = mixedMoment B raw27332step2 raw27332step2Labels := by
      have ha : raw27332step2 = -raw27332step1 := by apply Matrix.ext; change ∀ i j, raw27332step2 i j = -(raw27332step1 i j); unfold raw27332step2 raw27332step1; decide +kernel
      have hl : raw27332step2Labels = raw27332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node949 node949Labels := by rfl

theorem canonical27333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27333 raw27333Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw27333 raw27333Labels = mixedMoment B raw27333step0 raw27333step0Labels := by
      have hz : ∀ j, raw27333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27333step0 = (fun i j => raw27333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27333step0 raw27333; decide +kernel
      have hl : raw27333step0Labels = raw27333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27333 raw27333Labels permutation346 hz
    mixedMoment B raw27333step0 raw27333step0Labels = mixedMoment B raw27333step1 raw27333step1Labels := by
      have hz : ∀ j, raw27333step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27333step1 = (fun i j => raw27333step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27333step1 raw27333step0; decide +kernel
      have hl : raw27333step1Labels = raw27333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27333step0 raw27333step0Labels permutation32 hz
    mixedMoment B raw27333step1 raw27333step1Labels = mixedMoment B raw27333step2 raw27333step2Labels := by
      have ha : raw27333step2 = (fun i j => raw27333step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27333step2 raw27333step1; decide +kernel
      have hl : raw27333step2Labels = raw27333step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27333step1 raw27333step1Labels permutation26 permutation0
    mixedMoment B raw27333step2 raw27333step2Labels = mixedMoment B raw27333step3 raw27333step3Labels := by
      have ha : raw27333step3 = -raw27333step2 := by apply Matrix.ext; change ∀ i j, raw27333step3 i j = -(raw27333step2 i j); unfold raw27333step3 raw27333step2; decide +kernel
      have hl : raw27333step3Labels = raw27333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical27339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27339 raw27339Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27339 raw27339Labels = mixedMoment B raw27339step0 raw27339step0Labels := by
      have hz : ∀ j, raw27339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27339step0 = (fun i j => raw27339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27339step0 raw27339; decide +kernel
      have hl : raw27339step0Labels = raw27339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27339 raw27339Labels permutation346 hz
    mixedMoment B raw27339step0 raw27339step0Labels = mixedMoment B raw27339step1 raw27339step1Labels := by
      have ha : raw27339step1 = (fun i j => raw27339step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27339step1 raw27339step0; decide +kernel
      have hl : raw27339step1Labels = raw27339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27339step0 raw27339step0Labels permutation151 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27340 raw27340Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27340 raw27340Labels = mixedMoment B raw27340step0 raw27340step0Labels := by
      have hz : ∀ j, raw27340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27340step0 = (fun i j => raw27340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27340step0 raw27340; decide +kernel
      have hl : raw27340step0Labels = raw27340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27340 raw27340Labels permutation346 hz
    mixedMoment B raw27340step0 raw27340step0Labels = mixedMoment B raw27340step1 raw27340step1Labels := by
      have ha : raw27340step1 = (fun i j => raw27340step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27340step1 raw27340step0; decide +kernel
      have hl : raw27340step1Labels = raw27340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27340step0 raw27340step0Labels permutation147 permutation2
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical27341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27341 raw27341Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw27341 raw27341Labels = mixedMoment B raw27341step0 raw27341step0Labels := by
      have ha : raw27341step0 = (fun i j => raw27341 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27341step0 raw27341; decide +kernel
      have hl : raw27341step0Labels = raw27341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27341 raw27341Labels permutation668 permutation2
    _ = mixedMoment B node2219 node2219Labels := by rfl

theorem canonical27342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27342 raw27342Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw27342 raw27342Labels = mixedMoment B raw27342step0 raw27342step0Labels := by
      have hz : ∀ j, raw27342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27342step0 = (fun i j => raw27342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27342step0 raw27342; decide +kernel
      have hl : raw27342step0Labels = raw27342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27342 raw27342Labels permutation346 hz
    mixedMoment B raw27342step0 raw27342step0Labels = mixedMoment B raw27342step1 raw27342step1Labels := by
      have ha : raw27342step1 = (fun i j => raw27342step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27342step1 raw27342step0; decide +kernel
      have hl : raw27342step1Labels = raw27342step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27342step0 raw27342step0Labels permutation146 permutation2
    _ = mixedMoment B node2221 node2221Labels := by rfl

theorem canonical27343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27343 raw27343Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27343 raw27343Labels = mixedMoment B raw27343step0 raw27343step0Labels := by
      have hz : ∀ j, raw27343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27343step0 = (fun i j => raw27343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27343step0 raw27343; decide +kernel
      have hl : raw27343step0Labels = raw27343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27343 raw27343Labels permutation346 hz
    mixedMoment B raw27343step0 raw27343step0Labels = mixedMoment B raw27343step1 raw27343step1Labels := by
      have ha : raw27343step1 = (fun i j => raw27343step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27343step1 raw27343step0; decide +kernel
      have hl : raw27343step1Labels = raw27343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27343step0 raw27343step0Labels permutation32 permutation4
    mixedMoment B raw27343step1 raw27343step1Labels = mixedMoment B raw27343step2 raw27343step2Labels := by
      have ha : raw27343step2 = -raw27343step1 := by apply Matrix.ext; change ∀ i j, raw27343step2 i j = -(raw27343step1 i j); unfold raw27343step2 raw27343step1; decide +kernel
      have hl : raw27343step2Labels = raw27343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27344 raw27344Labels = mixedMoment B node1808 node1808Labels := by
  calc
    mixedMoment B raw27344 raw27344Labels = mixedMoment B raw27344step0 raw27344step0Labels := by
      have hz : ∀ j, raw27344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27344step0 = (fun i j => raw27344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27344step0 raw27344; decide +kernel
      have hl : raw27344step0Labels = raw27344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27344 raw27344Labels permutation346 hz
    mixedMoment B raw27344step0 raw27344step0Labels = mixedMoment B raw27344step1 raw27344step1Labels := by
      have ha : raw27344step1 = (fun i j => raw27344step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27344step1 raw27344step0; decide +kernel
      have hl : raw27344step1Labels = raw27344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27344step0 raw27344step0Labels permutation34 permutation2
    _ = mixedMoment B node1808 node1808Labels := by rfl

theorem canonical27345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27345 raw27345Labels = mixedMoment B node1961 node1961Labels := by
  calc
    mixedMoment B raw27345 raw27345Labels = mixedMoment B raw27345step0 raw27345step0Labels := by
      have ha : raw27345step0 = (fun i j => raw27345 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27345step0 raw27345; decide +kernel
      have hl : raw27345step0Labels = raw27345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27345 raw27345Labels permutation154 permutation2
    _ = mixedMoment B node1961 node1961Labels := by rfl

theorem canonical27346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27346 raw27346Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw27346 raw27346Labels = mixedMoment B raw27346step0 raw27346step0Labels := by
      have hz : ∀ j, raw27346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27346step0 = (fun i j => raw27346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27346step0 raw27346; decide +kernel
      have hl : raw27346step0Labels = raw27346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27346 raw27346Labels permutation346 hz
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical27347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27347 raw27347Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw27347 raw27347Labels = mixedMoment B raw27347step0 raw27347step0Labels := by
      have hz : ∀ j, raw27347 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27347step0 = (fun i j => raw27347 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27347step0 raw27347; decide +kernel
      have hl : raw27347step0Labels = raw27347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27347 raw27347Labels permutation520 hz
    mixedMoment B raw27347step0 raw27347step0Labels = mixedMoment B raw27347step1 raw27347step1Labels := by
      have hz : ∀ j, raw27347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27347step1 = (fun i j => raw27347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27347step1 raw27347step0; decide +kernel
      have hl : raw27347step1Labels = raw27347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27347step0 raw27347step0Labels permutation80 hz
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical27348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27348 raw27348Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw27348 raw27348Labels = mixedMoment B raw27348step0 raw27348step0Labels := by
      have hz : ∀ j, raw27348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27348step0 = (fun i j => raw27348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27348step0 raw27348; decide +kernel
      have hl : raw27348step0Labels = raw27348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27348 raw27348Labels permutation346 hz
    mixedMoment B raw27348step0 raw27348step0Labels = mixedMoment B raw27348step1 raw27348step1Labels := by
      have ha : raw27348step1 = (fun i j => raw27348step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27348step1 raw27348step0; decide +kernel
      have hl : raw27348step1Labels = raw27348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27348step0 raw27348step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical27349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27349 raw27349Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw27349 raw27349Labels = mixedMoment B raw27349step0 raw27349step0Labels := by
      have hz : ∀ j, raw27349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27349step0 = (fun i j => raw27349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27349step0 raw27349; decide +kernel
      have hl : raw27349step0Labels = raw27349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27349 raw27349Labels permutation346 hz
    mixedMoment B raw27349step0 raw27349step0Labels = mixedMoment B raw27349step1 raw27349step1Labels := by
      have ha : raw27349step1 = (fun i j => raw27349step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27349step1 raw27349step0; decide +kernel
      have hl : raw27349step1Labels = raw27349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27349step0 raw27349step0Labels permutation149 permutation2
    mixedMoment B raw27349step1 raw27349step1Labels = mixedMoment B raw27349step2 raw27349step2Labels := by
      have ha : raw27349step2 = -raw27349step1 := by apply Matrix.ext; change ∀ i j, raw27349step2 i j = -(raw27349step1 i j); unfold raw27349step2 raw27349step1; decide +kernel
      have hl : raw27349step2Labels = raw27349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical27350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27350 raw27350Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw27350 raw27350Labels = mixedMoment B raw27350step0 raw27350step0Labels := by
      have hz : ∀ j, raw27350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27350step0 = (fun i j => raw27350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27350step0 raw27350; decide +kernel
      have hl : raw27350step0Labels = raw27350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27350 raw27350Labels permutation346 hz
    mixedMoment B raw27350step0 raw27350step0Labels = mixedMoment B raw27350step1 raw27350step1Labels := by
      have ha : raw27350step1 = (fun i j => raw27350step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27350step1 raw27350step0; decide +kernel
      have hl : raw27350step1Labels = raw27350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27350step0 raw27350step0Labels permutation149 permutation2
    mixedMoment B raw27350step1 raw27350step1Labels = mixedMoment B raw27350step2 raw27350step2Labels := by
      have ha : raw27350step2 = -raw27350step1 := by apply Matrix.ext; change ∀ i j, raw27350step2 i j = -(raw27350step1 i j); unfold raw27350step2 raw27350step1; decide +kernel
      have hl : raw27350step2Labels = raw27350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

theorem canonical27351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27351 raw27351Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw27351 raw27351Labels = mixedMoment B raw27351step0 raw27351step0Labels := by
      have ha : raw27351step0 = (fun i j => raw27351 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27351step0 raw27351; decide +kernel
      have hl : raw27351step0Labels = raw27351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27351 raw27351Labels permutation680 permutation2
    mixedMoment B raw27351step0 raw27351step0Labels = mixedMoment B raw27351step1 raw27351step1Labels := by
      have ha : raw27351step1 = -raw27351step0 := by apply Matrix.ext; change ∀ i j, raw27351step1 i j = -(raw27351step0 i j); unfold raw27351step1 raw27351step0; decide +kernel
      have hl : raw27351step1Labels = raw27351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2430 node2430Labels := by rfl

theorem canonical27352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27352 raw27352Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw27352 raw27352Labels = mixedMoment B raw27352step0 raw27352step0Labels := by
      have hz : ∀ j, raw27352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27352step0 = (fun i j => raw27352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27352step0 raw27352; decide +kernel
      have hl : raw27352step0Labels = raw27352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27352 raw27352Labels permutation346 hz
    mixedMoment B raw27352step0 raw27352step0Labels = mixedMoment B raw27352step1 raw27352step1Labels := by
      have ha : raw27352step1 = (fun i j => raw27352step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27352step1 raw27352step0; decide +kernel
      have hl : raw27352step1Labels = raw27352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27352step0 raw27352step0Labels permutation151 permutation2
    mixedMoment B raw27352step1 raw27352step1Labels = mixedMoment B raw27352step2 raw27352step2Labels := by
      have ha : raw27352step2 = -raw27352step1 := by apply Matrix.ext; change ∀ i j, raw27352step2 i j = -(raw27352step1 i j); unfold raw27352step2 raw27352step1; decide +kernel
      have hl : raw27352step2Labels = raw27352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

theorem canonical27353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27353 raw27353Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw27353 raw27353Labels = mixedMoment B raw27353step0 raw27353step0Labels := by
      have hz : ∀ j, raw27353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27353step0 = (fun i j => raw27353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27353step0 raw27353; decide +kernel
      have hl : raw27353step0Labels = raw27353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27353 raw27353Labels permutation346 hz
    mixedMoment B raw27353step0 raw27353step0Labels = mixedMoment B raw27353step1 raw27353step1Labels := by
      have ha : raw27353step1 = (fun i j => raw27353step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27353step1 raw27353step0; decide +kernel
      have hl : raw27353step1Labels = raw27353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27353step0 raw27353step0Labels permutation149 permutation2
    mixedMoment B raw27353step1 raw27353step1Labels = mixedMoment B raw27353step2 raw27353step2Labels := by
      have ha : raw27353step2 = -raw27353step1 := by apply Matrix.ext; change ∀ i j, raw27353step2 i j = -(raw27353step1 i j); unfold raw27353step2 raw27353step1; decide +kernel
      have hl : raw27353step2Labels = raw27353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

theorem canonical27354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27354 raw27354Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw27354 raw27354Labels = mixedMoment B raw27354step0 raw27354step0Labels := by
      have hz : ∀ j, raw27354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27354step0 = (fun i j => raw27354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27354step0 raw27354; decide +kernel
      have hl : raw27354step0Labels = raw27354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27354 raw27354Labels permutation346 hz
    mixedMoment B raw27354step0 raw27354step0Labels = mixedMoment B raw27354step1 raw27354step1Labels := by
      have ha : raw27354step1 = (fun i j => raw27354step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27354step1 raw27354step0; decide +kernel
      have hl : raw27354step1Labels = raw27354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27354step0 raw27354step0Labels permutation149 permutation2
    mixedMoment B raw27354step1 raw27354step1Labels = mixedMoment B raw27354step2 raw27354step2Labels := by
      have ha : raw27354step2 = -raw27354step1 := by apply Matrix.ext; change ∀ i j, raw27354step2 i j = -(raw27354step1 i j); unfold raw27354step2 raw27354step1; decide +kernel
      have hl : raw27354step2Labels = raw27354step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1137 node1137Labels := by rfl

theorem canonical27355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27355 raw27355Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27355 raw27355Labels = mixedMoment B raw27355step0 raw27355step0Labels := by
      have hz : ∀ j, raw27355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27355step0 = (fun i j => raw27355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27355step0 raw27355; decide +kernel
      have hl : raw27355step0Labels = raw27355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27355 raw27355Labels permutation346 hz
    mixedMoment B raw27355step0 raw27355step0Labels = mixedMoment B raw27355step1 raw27355step1Labels := by
      have hz : ∀ j, raw27355step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27355step1 = (fun i j => raw27355step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27355step1 raw27355step0; decide +kernel
      have hl : raw27355step1Labels = raw27355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27355step0 raw27355step0Labels permutation32 hz
    mixedMoment B raw27355step1 raw27355step1Labels = mixedMoment B raw27355step2 raw27355step2Labels := by
      have ha : raw27355step2 = (fun i j => raw27355step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27355step2 raw27355step1; decide +kernel
      have hl : raw27355step2Labels = raw27355step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27355step1 raw27355step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical27356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27356 raw27356Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw27356 raw27356Labels = mixedMoment B raw27356step0 raw27356step0Labels := by
      have hz : ∀ j, raw27356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27356step0 = (fun i j => raw27356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27356step0 raw27356; decide +kernel
      have hl : raw27356step0Labels = raw27356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27356 raw27356Labels permutation346 hz
    mixedMoment B raw27356step0 raw27356step0Labels = mixedMoment B raw27356step1 raw27356step1Labels := by
      have ha : raw27356step1 = (fun i j => raw27356step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27356step1 raw27356step0; decide +kernel
      have hl : raw27356step1Labels = raw27356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27356step0 raw27356step0Labels permutation35 permutation4
    mixedMoment B raw27356step1 raw27356step1Labels = mixedMoment B raw27356step2 raw27356step2Labels := by
      have ha : raw27356step2 = -raw27356step1 := by apply Matrix.ext; change ∀ i j, raw27356step2 i j = -(raw27356step1 i j); unfold raw27356step2 raw27356step1; decide +kernel
      have hl : raw27356step2Labels = raw27356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical27357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27357 raw27357Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw27357 raw27357Labels = mixedMoment B raw27357step0 raw27357step0Labels := by
      have hz : ∀ j, raw27357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27357step0 = (fun i j => raw27357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27357step0 raw27357; decide +kernel
      have hl : raw27357step0Labels = raw27357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27357 raw27357Labels permutation346 hz
    mixedMoment B raw27357step0 raw27357step0Labels = mixedMoment B raw27357step1 raw27357step1Labels := by
      have ha : raw27357step1 = (fun i j => raw27357step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27357step1 raw27357step0; decide +kernel
      have hl : raw27357step1Labels = raw27357step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27357step0 raw27357step0Labels permutation148 permutation2
    _ = mixedMoment B node3472 node3472Labels := by rfl

theorem canonical27358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27358 raw27358Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw27358 raw27358Labels = mixedMoment B raw27358step0 raw27358step0Labels := by
      have ha : raw27358step0 = (fun i j => raw27358 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27358step0 raw27358; decide +kernel
      have hl : raw27358step0Labels = raw27358Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27358 raw27358Labels permutation679 permutation2
    _ = mixedMoment B node3437 node3437Labels := by rfl

theorem canonical27359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27359 raw27359Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27359 raw27359Labels = mixedMoment B raw27359step0 raw27359step0Labels := by
      have hz : ∀ j, raw27359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27359step0 = (fun i j => raw27359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27359step0 raw27359; decide +kernel
      have hl : raw27359step0Labels = raw27359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27359 raw27359Labels permutation346 hz
    mixedMoment B raw27359step0 raw27359step0Labels = mixedMoment B raw27359step1 raw27359step1Labels := by
      have ha : raw27359step1 = (fun i j => raw27359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27359step1 raw27359step0; decide +kernel
      have hl : raw27359step1Labels = raw27359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27359step0 raw27359step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27360 raw27360Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw27360 raw27360Labels = mixedMoment B raw27360step0 raw27360step0Labels := by
      have hz : ∀ j, raw27360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27360step0 = (fun i j => raw27360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27360step0 raw27360; decide +kernel
      have hl : raw27360step0Labels = raw27360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27360 raw27360Labels permutation346 hz
    mixedMoment B raw27360step0 raw27360step0Labels = mixedMoment B raw27360step1 raw27360step1Labels := by
      have ha : raw27360step1 = (fun i j => raw27360step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27360step1 raw27360step0; decide +kernel
      have hl : raw27360step1Labels = raw27360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27360step0 raw27360step0Labels permutation148 permutation2
    _ = mixedMoment B node3358 node3358Labels := by rfl

theorem canonical27361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27361 raw27361Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw27361 raw27361Labels = mixedMoment B raw27361step0 raw27361step0Labels := by
      have hz : ∀ j, raw27361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27361step0 = (fun i j => raw27361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27361step0 raw27361; decide +kernel
      have hl : raw27361step0Labels = raw27361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27361 raw27361Labels permutation346 hz
    mixedMoment B raw27361step0 raw27361step0Labels = mixedMoment B raw27361step1 raw27361step1Labels := by
      have ha : raw27361step1 = (fun i j => raw27361step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27361step1 raw27361step0; decide +kernel
      have hl : raw27361step1Labels = raw27361step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27361step0 raw27361step0Labels permutation148 permutation2
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical27362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27362 raw27362Labels = mixedMoment B node1910 node1910Labels := by
  calc
    mixedMoment B raw27362 raw27362Labels = mixedMoment B raw27362step0 raw27362step0Labels := by
      have ha : raw27362step0 = (fun i j => raw27362 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27362step0 raw27362; decide +kernel
      have hl : raw27362step0Labels = raw27362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27362 raw27362Labels permutation165 permutation4
    mixedMoment B raw27362step0 raw27362step0Labels = mixedMoment B raw27362step1 raw27362step1Labels := by
      have ha : raw27362step1 = -raw27362step0 := by apply Matrix.ext; change ∀ i j, raw27362step1 i j = -(raw27362step0 i j); unfold raw27362step1 raw27362step0; decide +kernel
      have hl : raw27362step1Labels = raw27362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1910 node1910Labels := by rfl

theorem canonical27363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27363 raw27363Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw27363 raw27363Labels = mixedMoment B raw27363step0 raw27363step0Labels := by
      have hz : ∀ j, raw27363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27363step0 = (fun i j => raw27363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27363step0 raw27363; decide +kernel
      have hl : raw27363step0Labels = raw27363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27363 raw27363Labels permutation346 hz
    mixedMoment B raw27363step0 raw27363step0Labels = mixedMoment B raw27363step1 raw27363step1Labels := by
      have ha : raw27363step1 = (fun i j => raw27363step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27363step1 raw27363step0; decide +kernel
      have hl : raw27363step1Labels = raw27363step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27363step0 raw27363step0Labels permutation35 permutation4
    mixedMoment B raw27363step1 raw27363step1Labels = mixedMoment B raw27363step2 raw27363step2Labels := by
      have ha : raw27363step2 = -raw27363step1 := by apply Matrix.ext; change ∀ i j, raw27363step2 i j = -(raw27363step1 i j); unfold raw27363step2 raw27363step1; decide +kernel
      have hl : raw27363step2Labels = raw27363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

theorem canonical27364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27364 raw27364Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw27364 raw27364Labels = mixedMoment B raw27364step0 raw27364step0Labels := by
      have hz : ∀ j, raw27364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27364step0 = (fun i j => raw27364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27364step0 raw27364; decide +kernel
      have hl : raw27364step0Labels = raw27364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27364 raw27364Labels permutation346 hz
    mixedMoment B raw27364step0 raw27364step0Labels = mixedMoment B raw27364step1 raw27364step1Labels := by
      have ha : raw27364step1 = (fun i j => raw27364step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27364step1 raw27364step0; decide +kernel
      have hl : raw27364step1Labels = raw27364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27364step0 raw27364step0Labels permutation35 permutation4
    mixedMoment B raw27364step1 raw27364step1Labels = mixedMoment B raw27364step2 raw27364step2Labels := by
      have ha : raw27364step2 = -raw27364step1 := by apply Matrix.ext; change ∀ i j, raw27364step2 i j = -(raw27364step1 i j); unfold raw27364step2 raw27364step1; decide +kernel
      have hl : raw27364step2Labels = raw27364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical27365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27365 raw27365Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw27365 raw27365Labels = mixedMoment B raw27365step0 raw27365step0Labels := by
      have hz : ∀ j, raw27365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27365step0 = (fun i j => raw27365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27365step0 raw27365; decide +kernel
      have hl : raw27365step0Labels = raw27365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27365 raw27365Labels permutation346 hz
    mixedMoment B raw27365step0 raw27365step0Labels = mixedMoment B raw27365step1 raw27365step1Labels := by
      have ha : raw27365step1 = (fun i j => raw27365step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27365step1 raw27365step0; decide +kernel
      have hl : raw27365step1Labels = raw27365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27365step0 raw27365step0Labels permutation34 permutation4
    mixedMoment B raw27365step1 raw27365step1Labels = mixedMoment B raw27365step2 raw27365step2Labels := by
      have ha : raw27365step2 = -raw27365step1 := by apply Matrix.ext; change ∀ i j, raw27365step2 i j = -(raw27365step1 i j); unfold raw27365step2 raw27365step1; decide +kernel
      have hl : raw27365step2Labels = raw27365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1917 node1917Labels := by rfl

theorem canonical27366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27366 raw27366Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27366 raw27366Labels = mixedMoment B raw27366step0 raw27366step0Labels := by
      have hz : ∀ j, raw27366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27366step0 = (fun i j => raw27366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27366step0 raw27366; decide +kernel
      have hl : raw27366step0Labels = raw27366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27366 raw27366Labels permutation346 hz
    mixedMoment B raw27366step0 raw27366step0Labels = mixedMoment B raw27366step1 raw27366step1Labels := by
      have ha : raw27366step1 = (fun i j => raw27366step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27366step1 raw27366step0; decide +kernel
      have hl : raw27366step1Labels = raw27366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27366step0 raw27366step0Labels permutation44 permutation4
    mixedMoment B raw27366step1 raw27366step1Labels = mixedMoment B raw27366step2 raw27366step2Labels := by
      have ha : raw27366step2 = -raw27366step1 := by apply Matrix.ext; change ∀ i j, raw27366step2 i j = -(raw27366step1 i j); unfold raw27366step2 raw27366step1; decide +kernel
      have hl : raw27366step2Labels = raw27366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27367 raw27367Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw27367 raw27367Labels = mixedMoment B raw27367step0 raw27367step0Labels := by
      have ha : raw27367step0 = (fun i j => raw27367 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27367step0 raw27367; decide +kernel
      have hl : raw27367step0Labels = raw27367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27367 raw27367Labels permutation164 permutation4
    mixedMoment B raw27367step0 raw27367step0Labels = mixedMoment B raw27367step1 raw27367step1Labels := by
      have ha : raw27367step1 = -raw27367step0 := by apply Matrix.ext; change ∀ i j, raw27367step1 i j = -(raw27367step0 i j); unfold raw27367step1 raw27367step0; decide +kernel
      have hl : raw27367step1Labels = raw27367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical27368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27368 raw27368Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw27368 raw27368Labels = mixedMoment B raw27368step0 raw27368step0Labels := by
      have hz : ∀ j, raw27368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27368step0 = (fun i j => raw27368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27368step0 raw27368; decide +kernel
      have hl : raw27368step0Labels = raw27368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27368 raw27368Labels permutation346 hz
    mixedMoment B raw27368step0 raw27368step0Labels = mixedMoment B raw27368step1 raw27368step1Labels := by
      have ha : raw27368step1 = (fun i j => raw27368step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27368step1 raw27368step0; decide +kernel
      have hl : raw27368step1Labels = raw27368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27368step0 raw27368step0Labels permutation34 permutation4
    mixedMoment B raw27368step1 raw27368step1Labels = mixedMoment B raw27368step2 raw27368step2Labels := by
      have ha : raw27368step2 = -raw27368step1 := by apply Matrix.ext; change ∀ i j, raw27368step2 i j = -(raw27368step1 i j); unfold raw27368step2 raw27368step1; decide +kernel
      have hl : raw27368step2Labels = raw27368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical27369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27369 raw27369Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw27369 raw27369Labels = mixedMoment B raw27369step0 raw27369step0Labels := by
      have ha : raw27369step0 = (fun i j => raw27369 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27369step0 raw27369; decide +kernel
      have hl : raw27369step0Labels = raw27369Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27369 raw27369Labels permutation160 permutation2
    _ = mixedMoment B node1790 node1790Labels := by rfl

theorem canonical27370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27370 raw27370Labels = mixedMoment B node2009 node2009Labels := by
  calc
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical27371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27371 raw27371Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27371 raw27371Labels = mixedMoment B raw27371step0 raw27371step0Labels := by
      have ha : raw27371step0 = (fun i j => raw27371 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27371step0 raw27371; decide +kernel
      have hl : raw27371step0Labels = raw27371Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27371 raw27371Labels permutation160 permutation2
    _ = mixedMoment B node1973 node1973Labels := by rfl

theorem canonical27372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27372 raw27372Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27372 raw27372Labels = mixedMoment B raw27372step0 raw27372step0Labels := by
      have hz : ∀ j, raw27372 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27372step0 = (fun i j => raw27372 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27372step0 raw27372; decide +kernel
      have hl : raw27372step0Labels = raw27372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27372 raw27372Labels permutation520 hz
    mixedMoment B raw27372step0 raw27372step0Labels = mixedMoment B raw27372step1 raw27372step1Labels := by
      have ha : raw27372step1 = (fun i j => raw27372step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27372step1 raw27372step0; decide +kernel
      have hl : raw27372step1Labels = raw27372step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27372step0 raw27372step0Labels permutation34 permutation2
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical27373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27373 raw27373Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw27373 raw27373Labels = mixedMoment B raw27373step0 raw27373step0Labels := by
      have ha : raw27373step0 = (fun i j => raw27373 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27373step0 raw27373; decide +kernel
      have hl : raw27373step0Labels = raw27373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27373 raw27373Labels permutation160 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical27374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27374 raw27374Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw27374 raw27374Labels = mixedMoment B raw27374step0 raw27374step0Labels := by
      have ha : raw27374step0 = (fun i j => raw27374 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27374step0 raw27374; decide +kernel
      have hl : raw27374step0Labels = raw27374Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27374 raw27374Labels permutation686 permutation2
    mixedMoment B raw27374step0 raw27374step0Labels = mixedMoment B raw27374step1 raw27374step1Labels := by
      have ha : raw27374step1 = -raw27374step0 := by apply Matrix.ext; change ∀ i j, raw27374step1 i j = -(raw27374step0 i j); unfold raw27374step1 raw27374step0; decide +kernel
      have hl : raw27374step1Labels = raw27374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical27375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27375 raw27375Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw27375 raw27375Labels = mixedMoment B raw27375step0 raw27375step0Labels := by
      have ha : raw27375step0 = (fun i j => raw27375 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27375step0 raw27375; decide +kernel
      have hl : raw27375step0Labels = raw27375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27375 raw27375Labels permutation686 permutation2
    mixedMoment B raw27375step0 raw27375step0Labels = mixedMoment B raw27375step1 raw27375step1Labels := by
      have ha : raw27375step1 = -raw27375step0 := by apply Matrix.ext; change ∀ i j, raw27375step1 i j = -(raw27375step0 i j); unfold raw27375step1 raw27375step0; decide +kernel
      have hl : raw27375step1Labels = raw27375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2440 node2440Labels := by rfl

theorem canonical27376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27376 raw27376Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw27376 raw27376Labels = mixedMoment B raw27376step0 raw27376step0Labels := by
      have ha : raw27376step0 = (fun i j => raw27376 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27376step0 raw27376; decide +kernel
      have hl : raw27376step0Labels = raw27376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27376 raw27376Labels permutation686 permutation2
    mixedMoment B raw27376step0 raw27376step0Labels = mixedMoment B raw27376step1 raw27376step1Labels := by
      have ha : raw27376step1 = -raw27376step0 := by apply Matrix.ext; change ∀ i j, raw27376step1 i j = -(raw27376step0 i j); unfold raw27376step1 raw27376step0; decide +kernel
      have hl : raw27376step1Labels = raw27376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

theorem canonical27377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27377 raw27377Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw27377 raw27377Labels = mixedMoment B raw27377step0 raw27377step0Labels := by
      have ha : raw27377step0 = (fun i j => raw27377 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27377step0 raw27377; decide +kernel
      have hl : raw27377step0Labels = raw27377Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27377 raw27377Labels permutation686 permutation2
    mixedMoment B raw27377step0 raw27377step0Labels = mixedMoment B raw27377step1 raw27377step1Labels := by
      have ha : raw27377step1 = -raw27377step0 := by apply Matrix.ext; change ∀ i j, raw27377step1 i j = -(raw27377step0 i j); unfold raw27377step1 raw27377step0; decide +kernel
      have hl : raw27377step1Labels = raw27377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1116 node1116Labels := by rfl

theorem canonical27378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27378 raw27378Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw27378 raw27378Labels = mixedMoment B raw27378step0 raw27378step0Labels := by
      have ha : raw27378step0 = (fun i j => raw27378 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27378step0 raw27378; decide +kernel
      have hl : raw27378step0Labels = raw27378Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27378 raw27378Labels permutation674 permutation2
    _ = mixedMoment B node3466 node3466Labels := by rfl

theorem canonical27379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27379 raw27379Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27379 raw27379Labels = mixedMoment B raw27379step0 raw27379step0Labels := by
      have hz : ∀ j, raw27379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27379step0 = (fun i j => raw27379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27379step0 raw27379; decide +kernel
      have hl : raw27379step0Labels = raw27379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27379 raw27379Labels permutation434 hz
    mixedMoment B raw27379step0 raw27379step0Labels = mixedMoment B raw27379step1 raw27379step1Labels := by
      have ha : raw27379step1 = (fun i j => raw27379step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27379step1 raw27379step0; decide +kernel
      have hl : raw27379step1Labels = raw27379step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27379step0 raw27379step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27380 raw27380Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw27380 raw27380Labels = mixedMoment B raw27380step0 raw27380step0Labels := by
      have ha : raw27380step0 = (fun i j => raw27380 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27380step0 raw27380; decide +kernel
      have hl : raw27380step0Labels = raw27380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27380 raw27380Labels permutation682 permutation2
    _ = mixedMoment B node3350 node3350Labels := by rfl

theorem canonical27381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27381 raw27381Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw27381 raw27381Labels = mixedMoment B raw27381step0 raw27381step0Labels := by
      have ha : raw27381step0 = (fun i j => raw27381 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27381step0 raw27381; decide +kernel
      have hl : raw27381step0Labels = raw27381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27381 raw27381Labels permutation682 permutation2
    _ = mixedMoment B node1940 node1940Labels := by rfl

theorem canonical27385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27385 raw27385Labels = mixedMoment B node1793 node1793Labels := by
  calc
    mixedMoment B raw27385 raw27385Labels = mixedMoment B raw27385step0 raw27385step0Labels := by
      have ha : raw27385step0 = (fun i j => raw27385 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27385step0 raw27385; decide +kernel
      have hl : raw27385step0Labels = raw27385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27385 raw27385Labels permutation158 permutation2
    _ = mixedMoment B node1793 node1793Labels := by rfl

theorem canonical27386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27386 raw27386Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw27386 raw27386Labels = mixedMoment B raw27386step0 raw27386step0Labels := by
      have ha : raw27386step0 = (fun i j => raw27386 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27386step0 raw27386; decide +kernel
      have hl : raw27386step0Labels = raw27386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27386 raw27386Labels permutation158 permutation2
    _ = mixedMoment B node1976 node1976Labels := by rfl

theorem canonical27387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27387 raw27387Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw27387 raw27387Labels = mixedMoment B raw27387step0 raw27387step0Labels := by
      have ha : raw27387step0 = (fun i j => raw27387 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27387step0 raw27387; decide +kernel
      have hl : raw27387step0Labels = raw27387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27387 raw27387Labels permutation158 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3327 raw3327Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3327 raw3327Labels = mixedMoment B raw3327step0 raw3327step0Labels := by
      have hz : ∀ j, raw3327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3327step0 = (fun i j => raw3327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3327step0 raw3327; decide +kernel
      have hl : raw3327step0Labels = raw3327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327 raw3327Labels permutation434 hz
    mixedMoment B raw3327step0 raw3327step0Labels = mixedMoment B raw3327step1 raw3327step1Labels := by
      have hz : ∀ j, raw3327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3327step1 = (fun i j => raw3327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3327step1 raw3327step0; decide +kernel
      have hl : raw3327step1Labels = raw3327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327step0 raw3327step0Labels permutation56 hz
    mixedMoment B raw3327step1 raw3327step1Labels = mixedMoment B raw3327step2 raw3327step2Labels := by
      have hz : ∀ i, raw3327step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3327step2 = (fun i j => raw3327step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3327step2 raw3327step1; decide +kernel
      have hl : raw3327step2Labels = (fun j => raw3327step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3327step1 raw3327step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3529 raw3529Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3529 raw3529Labels = mixedMoment B raw3529step0 raw3529step0Labels := by
      have hz : ∀ j, raw3529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3529step0 = (fun i j => raw3529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3529step0 raw3529; decide +kernel
      have hl : raw3529step0Labels = raw3529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529 raw3529Labels permutation434 hz
    mixedMoment B raw3529step0 raw3529step0Labels = mixedMoment B raw3529step1 raw3529step1Labels := by
      have hz : ∀ j, raw3529step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3529step1 = (fun i j => raw3529step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3529step1 raw3529step0; decide +kernel
      have hl : raw3529step1Labels = raw3529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529step0 raw3529step0Labels permutation80 hz
    _ = mixedMoment B node2063 node2063Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3630 raw3630Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3630 raw3630Labels = mixedMoment B raw3630step0 raw3630step0Labels := by
      have hz : ∀ j, raw3630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3630step0 = (fun i j => raw3630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3630step0 raw3630; decide +kernel
      have hl : raw3630step0Labels = raw3630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630 raw3630Labels permutation590 hz
    mixedMoment B raw3630step0 raw3630step0Labels = mixedMoment B raw3630step1 raw3630step1Labels := by
      have hz : ∀ j, raw3630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3630step1 = (fun i j => raw3630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3630step1 raw3630step0; decide +kernel
      have hl : raw3630step1Labels = raw3630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step0 raw3630step0Labels permutation80 hz
    mixedMoment B raw3630step1 raw3630step1Labels = mixedMoment B raw3630step2 raw3630step2Labels := by
      have hz : ∀ j, raw3630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3630step2 = (fun i j => raw3630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3630step2 raw3630step1; decide +kernel
      have hl : raw3630step2Labels = raw3630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step1 raw3630step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3641 raw3641Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3641 raw3641Labels = mixedMoment B raw3641step0 raw3641step0Labels := by
      have hz : ∀ j, raw3641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3641step0 = (fun i j => raw3641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3641step0 raw3641; decide +kernel
      have hl : raw3641step0Labels = raw3641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3641 raw3641Labels permutation346 hz
    mixedMoment B raw3641step0 raw3641step0Labels = mixedMoment B raw3641step1 raw3641step1Labels := by
      have ha : raw3641step1 = (fun i j => raw3641step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3641step1 raw3641step0; decide +kernel
      have hl : raw3641step1Labels = raw3641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3641step0 raw3641step0Labels permutation34 permutation2
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical3642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3642 raw3642Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3642 raw3642Labels = mixedMoment B raw3642step0 raw3642step0Labels := by
      have hz : ∀ j, raw3642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3642step0 = (fun i j => raw3642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3642step0 raw3642; decide +kernel
      have hl : raw3642step0Labels = raw3642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3642 raw3642Labels permutation346 hz
    _ = mixedMoment B node2026 node2026Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3834 raw3834Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3834 raw3834Labels = mixedMoment B raw3834step0 raw3834step0Labels := by
      have hz : ∀ j, raw3834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3834step0 = (fun i j => raw3834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3834step0 raw3834; decide +kernel
      have hl : raw3834step0Labels = raw3834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834 raw3834Labels permutation590 hz
    mixedMoment B raw3834step0 raw3834step0Labels = mixedMoment B raw3834step1 raw3834step1Labels := by
      have hz : ∀ j, raw3834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3834step1 = (fun i j => raw3834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3834step1 raw3834step0; decide +kernel
      have hl : raw3834step1Labels = raw3834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834step0 raw3834step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3844 raw3844Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3844 raw3844Labels = mixedMoment B raw3844step0 raw3844step0Labels := by
      have ha : raw3844step0 = (fun i j => raw3844 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3844step0 raw3844; decide +kernel
      have hl : raw3844step0Labels = raw3844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3844 raw3844Labels permutation160 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3846 raw3846Labels = mixedMoment B node2010 node2010Labels := by
  calc
    _ = mixedMoment B node2010 node2010Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical5636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5636 raw5636Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw5636 raw5636Labels = mixedMoment B raw5636step0 raw5636step0Labels := by
      have hz : ∀ j, raw5636 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw5636step0 = (fun i j => raw5636 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw5636step0 raw5636; decide +kernel
      have hl : raw5636step0Labels = raw5636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5636 raw5636Labels permutation152 hz
    mixedMoment B raw5636step0 raw5636step0Labels = mixedMoment B raw5636step1 raw5636step1Labels := by
      have ha : raw5636step1 = (fun i j => raw5636step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5636step1 raw5636step0; decide +kernel
      have hl : raw5636step1Labels = raw5636step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5636step0 raw5636step0Labels permutation146 permutation0
    mixedMoment B raw5636step1 raw5636step1Labels = mixedMoment B raw5636step2 raw5636step2Labels := by
      have ha : raw5636step2 = -raw5636step1 := by apply Matrix.ext; change ∀ i j, raw5636step2 i j = -(raw5636step1 i j); unfold raw5636step2 raw5636step1; decide +kernel
      have hl : raw5636step2Labels = raw5636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical5649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5649 raw5649Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5649 raw5649Labels = mixedMoment B raw5649step0 raw5649step0Labels := by
      have ha : raw5649step0 = (fun i j => raw5649 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5649step0 raw5649; decide +kernel
      have hl : raw5649step0Labels = raw5649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5649 raw5649Labels permutation682 permutation2
    mixedMoment B raw5649step0 raw5649step0Labels = mixedMoment B raw5649step1 raw5649step1Labels := by
      have ha : raw5649step1 = -raw5649step0 := by apply Matrix.ext; change ∀ i j, raw5649step1 i j = -(raw5649step0 i j); unfold raw5649step1 raw5649step0; decide +kernel
      have hl : raw5649step1Labels = raw5649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical5656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5656 raw5656Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5656 raw5656Labels = mixedMoment B raw5656step0 raw5656step0Labels := by
      have ha : raw5656step0 = (fun i j => raw5656 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5656step0 raw5656; decide +kernel
      have hl : raw5656step0Labels = raw5656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5656 raw5656Labels permutation676 permutation2
    mixedMoment B raw5656step0 raw5656step0Labels = mixedMoment B raw5656step1 raw5656step1Labels := by
      have ha : raw5656step1 = -raw5656step0 := by apply Matrix.ext; change ∀ i j, raw5656step1 i j = -(raw5656step0 i j); unfold raw5656step1 raw5656step0; decide +kernel
      have hl : raw5656step1Labels = raw5656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

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

theorem canonical11534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11534 raw11534Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11534 raw11534Labels = mixedMoment B raw11534step0 raw11534step0Labels := by
      have hz : ∀ j, raw11534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11534step0 = (fun i j => raw11534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11534step0 raw11534; decide +kernel
      have hl : raw11534step0Labels = raw11534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534 raw11534Labels permutation434 hz
    mixedMoment B raw11534step0 raw11534step0Labels = mixedMoment B raw11534step1 raw11534step1Labels := by
      have hz : ∀ j, raw11534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11534step1 = (fun i j => raw11534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11534step1 raw11534step0; decide +kernel
      have hl : raw11534step1Labels = raw11534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534step0 raw11534step0Labels permutation56 hz
    mixedMoment B raw11534step1 raw11534step1Labels = mixedMoment B raw11534step2 raw11534step2Labels := by
      have hz : ∀ i, raw11534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11534step2 = (fun i j => raw11534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11534step2 raw11534step1; decide +kernel
      have hl : raw11534step2Labels = (fun j => raw11534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11534step1 raw11534step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11537 raw11537Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11537 raw11537Labels = mixedMoment B raw11537step0 raw11537step0Labels := by
      have hz : ∀ j, raw11537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11537step0 = (fun i j => raw11537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11537step0 raw11537; decide +kernel
      have hl : raw11537step0Labels = raw11537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537 raw11537Labels permutation346 hz
    mixedMoment B raw11537step0 raw11537step0Labels = mixedMoment B raw11537step1 raw11537step1Labels := by
      have hz : ∀ j, raw11537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11537step1 = (fun i j => raw11537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11537step1 raw11537step0; decide +kernel
      have hl : raw11537step1Labels = raw11537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537step0 raw11537step0Labels permutation56 hz
    mixedMoment B raw11537step1 raw11537step1Labels = mixedMoment B raw11537step2 raw11537step2Labels := by
      have hz : ∀ i, raw11537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11537step2 = (fun i j => raw11537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11537step2 raw11537step1; decide +kernel
      have hl : raw11537step2Labels = (fun j => raw11537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11537step1 raw11537step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem sound905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node905 node905Labels = Sparse.eval nodeValue905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 905) = mixedMoment B node905 node905Labels := rfl
  simpa [nodeValue905, Sparse.eval] using hc.symm

theorem sound909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node909 node909Labels = Sparse.eval nodeValue909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 909) = mixedMoment B node909 node909Labels := rfl
  simpa [nodeValue909, Sparse.eval] using hc.symm

theorem sound914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node914 node914Labels = Sparse.eval nodeValue914 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 914) = mixedMoment B node914 node914Labels := rfl
  simpa [nodeValue914, Sparse.eval] using hc.symm

theorem sound925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node925 node925Labels = Sparse.eval nodeValue925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 925) = mixedMoment B node925 node925Labels := rfl
  simpa [nodeValue925, Sparse.eval] using hc.symm

theorem sound931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node931 node931Labels = Sparse.eval nodeValue931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 931) = mixedMoment B node931 node931Labels := rfl
  simpa [nodeValue931, Sparse.eval] using hc.symm

theorem sound940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node940 node940Labels = Sparse.eval nodeValue940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 940) = mixedMoment B node940 node940Labels := rfl
  simpa [nodeValue940, Sparse.eval] using hc.symm

theorem sound949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node949 node949Labels = Sparse.eval nodeValue949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 949) = mixedMoment B node949 node949Labels := rfl
  simpa [nodeValue949, Sparse.eval] using hc.symm

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

theorem sound1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1116 node1116Labels = Sparse.eval nodeValue1116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1116) = mixedMoment B node1116 node1116Labels := rfl
  simpa [nodeValue1116, Sparse.eval] using hc.symm

theorem sound1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1137 node1137Labels = Sparse.eval nodeValue1137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1137) = mixedMoment B node1137 node1137Labels := rfl
  simpa [nodeValue1137, Sparse.eval] using hc.symm

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

theorem sound1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1790 node1790Labels = Sparse.eval nodeValue1790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1790) = mixedMoment B node1790 node1790Labels := rfl
  simpa [nodeValue1790, Sparse.eval] using hc.symm

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

theorem sound1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1793 node1793Labels = Sparse.eval nodeValue1793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1793) = mixedMoment B node1793 node1793Labels := rfl
  simpa [nodeValue1793, Sparse.eval] using hc.symm

theorem sound1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1797 node1797Labels = Sparse.eval nodeValue1797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1797) = mixedMoment B node1797 node1797Labels := rfl
  simpa [nodeValue1797, Sparse.eval] using hc.symm

theorem sound1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1808 node1808Labels = Sparse.eval nodeValue1808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1808) = mixedMoment B node1808 node1808Labels := rfl
  simpa [nodeValue1808, Sparse.eval] using hc.symm

theorem sound1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1813 node1813Labels = Sparse.eval nodeValue1813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1813) = mixedMoment B node1813 node1813Labels := rfl
  simpa [nodeValue1813, Sparse.eval] using hc.symm

theorem sound1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1820 node1820Labels = Sparse.eval nodeValue1820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1820) = mixedMoment B node1820 node1820Labels := rfl
  simpa [nodeValue1820, Sparse.eval] using hc.symm

theorem sound1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1828 node1828Labels = Sparse.eval nodeValue1828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1828) = mixedMoment B node1828 node1828Labels := rfl
  simpa [nodeValue1828, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1910 node1910Labels = Sparse.eval nodeValue1910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1910) = mixedMoment B node1910 node1910Labels := rfl
  simpa [nodeValue1910, Sparse.eval] using hc.symm

theorem sound1916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1916 node1916Labels = Sparse.eval nodeValue1916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1916) = mixedMoment B node1916 node1916Labels := rfl
  simpa [nodeValue1916, Sparse.eval] using hc.symm

theorem sound1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1917 node1917Labels = Sparse.eval nodeValue1917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1917) = mixedMoment B node1917 node1917Labels := rfl
  simpa [nodeValue1917, Sparse.eval] using hc.symm

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

theorem sound1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1940 node1940Labels = Sparse.eval nodeValue1940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1940) = mixedMoment B node1940 node1940Labels := rfl
  simpa [nodeValue1940, Sparse.eval] using hc.symm

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

theorem sound1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1957 node1957Labels = Sparse.eval nodeValue1957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1957) = mixedMoment B node1957 node1957Labels := rfl
  simpa [nodeValue1957, Sparse.eval] using hc.symm

theorem sound1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1961 node1961Labels = Sparse.eval nodeValue1961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1961) = mixedMoment B node1961 node1961Labels := rfl
  simpa [nodeValue1961, Sparse.eval] using hc.symm

theorem sound1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1965 node1965Labels = Sparse.eval nodeValue1965 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1965) = mixedMoment B node1965 node1965Labels := rfl
  simpa [nodeValue1965, Sparse.eval] using hc.symm

theorem sound1971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1971 node1971Labels = Sparse.eval nodeValue1971 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1971) = mixedMoment B node1971 node1971Labels := rfl
  simpa [nodeValue1971, Sparse.eval] using hc.symm

theorem sound1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1973 node1973Labels = Sparse.eval nodeValue1973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1973) = mixedMoment B node1973 node1973Labels := rfl
  simpa [nodeValue1973, Sparse.eval] using hc.symm

theorem sound1976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1976 node1976Labels = Sparse.eval nodeValue1976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1976) = mixedMoment B node1976 node1976Labels := rfl
  simpa [nodeValue1976, Sparse.eval] using hc.symm

theorem sound1980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1980 node1980Labels = Sparse.eval nodeValue1980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1980) = mixedMoment B node1980 node1980Labels := rfl
  simpa [nodeValue1980, Sparse.eval] using hc.symm

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

theorem sound2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2009 node2009Labels = Sparse.eval nodeValue2009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2009) = mixedMoment B node2009 node2009Labels := rfl
  simpa [nodeValue2009, Sparse.eval] using hc.symm

theorem sound2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2010 node2010Labels = Sparse.eval nodeValue2010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2010) = mixedMoment B node2010 node2010Labels := rfl
  simpa [nodeValue2010, Sparse.eval] using hc.symm

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

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2026 node2026Labels = Sparse.eval nodeValue2026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2026) = mixedMoment B node2026 node2026Labels := rfl
  simpa [nodeValue2026, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2035 node2035Labels = Sparse.eval nodeValue2035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2035) = mixedMoment B node2035 node2035Labels := rfl
  simpa [nodeValue2035, Sparse.eval] using hc.symm

theorem sound2037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2037 node2037Labels = Sparse.eval nodeValue2037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2037) = mixedMoment B node2037 node2037Labels := rfl
  simpa [nodeValue2037, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

theorem sound2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2063 node2063Labels = Sparse.eval nodeValue2063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2063) = mixedMoment B node2063 node2063Labels := rfl
  simpa [nodeValue2063, Sparse.eval] using hc.symm

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

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

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

theorem sound2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2219 node2219Labels = Sparse.eval nodeValue2219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2219) = mixedMoment B node2219 node2219Labels := rfl
  simpa [nodeValue2219, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2221 node2221Labels = Sparse.eval nodeValue2221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2221) = mixedMoment B node2221 node2221Labels := rfl
  simpa [nodeValue2221, Sparse.eval] using hc.symm

theorem sound2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2222 node2222Labels = Sparse.eval nodeValue2222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2222) = mixedMoment B node2222 node2222Labels := rfl
  simpa [nodeValue2222, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2282 node2282Labels = Sparse.eval nodeValue2282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2282) = mixedMoment B node2282 node2282Labels := rfl
  simpa [nodeValue2282, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

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

theorem sound2340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2340 node2340Labels = Sparse.eval nodeValue2340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2340) = mixedMoment B node2340 node2340Labels := rfl
  simpa [nodeValue2340, Sparse.eval] using hc.symm

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

theorem sound2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2430 node2430Labels = Sparse.eval nodeValue2430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2430) = mixedMoment B node2430 node2430Labels := rfl
  simpa [nodeValue2430, Sparse.eval] using hc.symm

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

theorem sound2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2440 node2440Labels = Sparse.eval nodeValue2440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2440) = mixedMoment B node2440 node2440Labels := rfl
  simpa [nodeValue2440, Sparse.eval] using hc.symm

theorem sound2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2471 node2471Labels = Sparse.eval nodeValue2471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2471) = mixedMoment B node2471 node2471Labels := rfl
  simpa [nodeValue2471, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

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

theorem sound2497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2497 node2497Labels = Sparse.eval nodeValue2497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2497) = mixedMoment B node2497 node2497Labels := rfl
  simpa [nodeValue2497, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound3350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3350 node3350Labels = Sparse.eval nodeValue3350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3350) = mixedMoment B node3350 node3350Labels := rfl
  simpa [nodeValue3350, Sparse.eval] using hc.symm

theorem sound3358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3358 node3358Labels = Sparse.eval nodeValue3358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3358) = mixedMoment B node3358 node3358Labels := rfl
  simpa [nodeValue3358, Sparse.eval] using hc.symm

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

theorem sound3437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3437 node3437Labels = Sparse.eval nodeValue3437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3437) = mixedMoment B node3437 node3437Labels := rfl
  simpa [nodeValue3437, Sparse.eval] using hc.symm

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

theorem sound3466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3466 node3466Labels = Sparse.eval nodeValue3466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3466) = mixedMoment B node3466 node3466Labels := rfl
  simpa [nodeValue3466, Sparse.eval] using hc.symm

theorem sound3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3472 node3472Labels = Sparse.eval nodeValue3472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3472) = mixedMoment B node3472 node3472Labels := rfl
  simpa [nodeValue3472, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

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

theorem sound4056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4056 node4056Labels = Sparse.eval nodeValue4056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4056) = mixedMoment B node4056 node4056Labels := rfl
  simpa [nodeValue4056, Sparse.eval] using hc.symm

theorem sound4057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4057 node4057Labels = Sparse.eval nodeValue4057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4057) = mixedMoment B node4057 node4057Labels := rfl
  simpa [nodeValue4057, Sparse.eval] using hc.symm

theorem sound4063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4063 node4063Labels = Sparse.eval nodeValue4063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4063) = mixedMoment B node4063 node4063Labels := rfl
  simpa [nodeValue4063, Sparse.eval] using hc.symm

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1890 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 1) (sourceB1890 + difference 1 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 1) (sourceB1890 + difference 1 0) sourceC1890) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 2) (sourceB1890 + difference 2 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 2) (sourceB1890 + difference 2 0) sourceC1890) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 3) (sourceB1890 + difference 3 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 3) (sourceB1890 + difference 3 0) sourceC1890) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 4) (sourceB1890 + difference 4 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 4) (sourceB1890 + difference 4 0) sourceC1890) = raw14366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14366; decide +kernel
    rw [ha]
    exact (canonical14366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 5) (sourceB1890 + difference 5 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 5) (sourceB1890 + difference 5 0) sourceC1890) = raw14367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14367; decide +kernel
    rw [ha]
    exact (canonical14367 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 0) (sourceB1890 + difference 0 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 0) (sourceB1890 + difference 0 1) sourceC1890) = raw27293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27293; decide +kernel
    rw [ha]
    exact (canonical27293 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 2) (sourceB1890 + difference 2 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 2) (sourceB1890 + difference 2 1) sourceC1890) = raw14360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14360; decide +kernel
    rw [ha]
    exact (canonical14360 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 3) (sourceB1890 + difference 3 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 3) (sourceB1890 + difference 3 1) sourceC1890) = raw27294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27294; decide +kernel
    rw [ha]
    exact (canonical27294 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 4) (sourceB1890 + difference 4 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 4) (sourceB1890 + difference 4 1) sourceC1890) = raw27295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27295; decide +kernel
    rw [ha]
    exact (canonical27295 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 5) (sourceB1890 + difference 5 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 5) (sourceB1890 + difference 5 1) sourceC1890) = raw27296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27296; decide +kernel
    rw [ha]
    exact (canonical27296 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 0) (sourceB1890 + difference 0 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 0) (sourceB1890 + difference 0 2) sourceC1890) = raw27297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27297; decide +kernel
    rw [ha]
    exact (canonical27297 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 1) (sourceB1890 + difference 1 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 1) (sourceB1890 + difference 1 2) sourceC1890) = raw27298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27298; decide +kernel
    rw [ha]
    exact (canonical27298 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 3) (sourceB1890 + difference 3 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 3) (sourceB1890 + difference 3 2) sourceC1890) = raw27299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27299; decide +kernel
    rw [ha]
    exact (canonical27299 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 4) (sourceB1890 + difference 4 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 4) (sourceB1890 + difference 4 2) sourceC1890) = raw27300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27300; decide +kernel
    rw [ha]
    exact (canonical27300 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 5) (sourceB1890 + difference 5 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 5) (sourceB1890 + difference 5 2) sourceC1890) = raw27301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27301; decide +kernel
    rw [ha]
    exact (canonical27301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 0) (sourceB1890 + difference 0 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 0) (sourceB1890 + difference 0 3) sourceC1890) = raw27302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27302; decide +kernel
    rw [ha]
    exact (canonical27302 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 1) (sourceB1890 + difference 1 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 1) (sourceB1890 + difference 1 3) sourceC1890) = raw27303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27303; decide +kernel
    rw [ha]
    exact (canonical27303 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 2) (sourceB1890 + difference 2 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 2) (sourceB1890 + difference 2 3) sourceC1890) = raw14368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14368; decide +kernel
    rw [ha]
    exact (canonical14368 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 4) (sourceB1890 + difference 4 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 4) (sourceB1890 + difference 4 3) sourceC1890) = raw27304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27304; decide +kernel
    rw [ha]
    exact (canonical27304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 5) (sourceB1890 + difference 5 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 5) (sourceB1890 + difference 5 3) sourceC1890) = raw27305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27305; decide +kernel
    rw [ha]
    exact (canonical27305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 0) (sourceB1890 + difference 0 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 0) (sourceB1890 + difference 0 4) sourceC1890) = raw27306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27306; decide +kernel
    rw [ha]
    exact (canonical27306 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 1) (sourceB1890 + difference 1 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 1) (sourceB1890 + difference 1 4) sourceC1890) = raw27307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27307; decide +kernel
    rw [ha]
    exact (canonical27307 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 2) (sourceB1890 + difference 2 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 2) (sourceB1890 + difference 2 4) sourceC1890) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 3) (sourceB1890 + difference 3 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 3) (sourceB1890 + difference 3 4) sourceC1890) = raw23784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw23784; decide +kernel
    rw [ha]
    exact (canonical23784 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 5) (sourceB1890 + difference 5 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 5) (sourceB1890 + difference 5 4) sourceC1890) = raw27308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27308; decide +kernel
    rw [ha]
    exact (canonical27308 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 0) (sourceB1890 + difference 0 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 0) (sourceB1890 + difference 0 5) sourceC1890) = raw26357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26357; decide +kernel
    rw [ha]
    exact (canonical26357 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 1) (sourceB1890 + difference 1 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 1) (sourceB1890 + difference 1 5) sourceC1890) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 2) (sourceB1890 + difference 2 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 2) (sourceB1890 + difference 2 5) sourceC1890) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 3) (sourceB1890 + difference 3 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 3) (sourceB1890 + difference 3 5) sourceC1890) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 4) (sourceB1890 + difference 4 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 4) (sourceB1890 + difference 4 5) sourceC1890) = raw26359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26359; decide +kernel
    rw [ha]
    exact (canonical26359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1890 sourceB1890 sourceC1890
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1890, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1891 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 0) (sourceB1891 + difference 0 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 0) (sourceB1891 + difference 0 4) sourceC1891) = raw20089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw20089; decide +kernel
    rw [ha]
    exact (canonical20089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 1) (sourceB1891 + difference 1 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1820) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 1) (sourceB1891 + difference 1 4) sourceC1891) = raw27309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27309; decide +kernel
    rw [ha]
    exact (canonical27309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 2) (sourceB1891 + difference 2 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1971) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 2) (sourceB1891 + difference 2 4) sourceC1891) = raw27310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27310; decide +kernel
    rw [ha]
    exact (canonical27310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 3) (sourceB1891 + difference 3 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1971) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 3) (sourceB1891 + difference 3 4) sourceC1891) = raw27311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27311; decide +kernel
    rw [ha]
    exact (canonical27311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 4) (sourceB1891 + difference 4 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 4) (sourceB1891 + difference 4 4) sourceC1891) = raw3529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw3529; decide +kernel
    rw [ha]
    exact (canonical3529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 5) (sourceB1891 + difference 5 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 5) (sourceB1891 + difference 5 4) sourceC1891) = raw27312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27312; decide +kernel
    rw [ha]
    exact (canonical27312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1891 + sourceB1891) sourceC1891) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1891 + sourceB1891) sourceC1891) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1891 sourceB1891 sourceC1891 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1891 sourceB1891 sourceC1891
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1891, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1892 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1892 + difference 0 4) (sourceB1892 + difference 4 0) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1892 + difference 0 4) (sourceB1892 + difference 4 0) sourceC1892) = raw27313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27313; decide +kernel
    rw [ha]
    exact (canonical27313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1892 + difference 1 4) (sourceB1892 + difference 4 1) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA1892 + difference 1 4) (sourceB1892 + difference 4 1) sourceC1892) = raw27314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27314; decide +kernel
    rw [ha]
    exact (canonical27314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1892 + difference 2 4) (sourceB1892 + difference 4 2) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1892 + difference 2 4) (sourceB1892 + difference 4 2) sourceC1892) = raw27315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27315; decide +kernel
    rw [ha]
    exact (canonical27315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1892 + difference 3 4) (sourceB1892 + difference 4 3) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1892 + difference 3 4) (sourceB1892 + difference 4 3) sourceC1892) = raw27316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27316; decide +kernel
    rw [ha]
    exact (canonical27316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1892 + difference 4 4) (sourceB1892 + difference 4 4) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1892 + difference 4 4) (sourceB1892 + difference 4 4) sourceC1892) = raw27317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27317; decide +kernel
    rw [ha]
    exact (canonical27317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1892 + difference 5 4) (sourceB1892 + difference 4 5) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1892 + difference 5 4) (sourceB1892 + difference 4 5) sourceC1892) = raw27318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27318; decide +kernel
    rw [ha]
    exact (canonical27318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1892 + sourceB1892) sourceC1892) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1892 + sourceB1892) sourceC1892) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1892 sourceB1892 sourceC1892 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1892 sourceB1892 sourceC1892
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1892, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1893 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 0) (sourceB1893 + difference 0 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 0) (sourceB1893 + difference 0 3) sourceC1893) = raw20109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw20109; decide +kernel
    rw [ha]
    exact (canonical20109 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 1) (sourceB1893 + difference 1 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 1) (sourceB1893 + difference 1 3) sourceC1893) = raw27320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27320; decide +kernel
    rw [ha]
    exact (canonical27320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 2) (sourceB1893 + difference 2 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1965) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 2) (sourceB1893 + difference 2 3) sourceC1893) = raw27321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27321; decide +kernel
    rw [ha]
    exact (canonical27321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 3) (sourceB1893 + difference 3 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 3) (sourceB1893 + difference 3 3) sourceC1893) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 4) (sourceB1893 + difference 4 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 4) (sourceB1893 + difference 4 3) sourceC1893) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 5) (sourceB1893 + difference 5 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 5) (sourceB1893 + difference 5 3) sourceC1893) = raw27322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27322; decide +kernel
    rw [ha]
    exact (canonical27322 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1893 + sourceB1893) sourceC1893) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1893 + sourceB1893) sourceC1893) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1893 sourceB1893 sourceC1893 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1893 sourceB1893 sourceC1893
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1893, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1894 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 0) (sourceB1894 + difference 0 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 0) (sourceB1894 + difference 0 4) sourceC1894) = raw20113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw20113; decide +kernel
    rw [ha]
    exact (canonical20113 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 1) (sourceB1894 + difference 1 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1797) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 1) (sourceB1894 + difference 1 4) sourceC1894) = raw27323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27323; decide +kernel
    rw [ha]
    exact (canonical27323 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 2) (sourceB1894 + difference 2 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1957) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 2) (sourceB1894 + difference 2 4) sourceC1894) = raw27324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27324; decide +kernel
    rw [ha]
    exact (canonical27324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 3) (sourceB1894 + difference 3 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 3) (sourceB1894 + difference 3 4) sourceC1894) = raw27325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27325; decide +kernel
    rw [ha]
    exact (canonical27325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 4) (sourceB1894 + difference 4 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 4) (sourceB1894 + difference 4 4) sourceC1894) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 5) (sourceB1894 + difference 5 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 5) (sourceB1894 + difference 5 4) sourceC1894) = raw27326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27326; decide +kernel
    rw [ha]
    exact (canonical27326 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1894 + sourceB1894) sourceC1894) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1894 + sourceB1894) sourceC1894) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1894 sourceB1894 sourceC1894 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1894 sourceB1894 sourceC1894
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1894, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1895 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1895 + difference 0 3) (sourceB1895 + difference 3 0) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1895 + difference 0 3) (sourceB1895 + difference 3 0) sourceC1895) = raw27327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27327; decide +kernel
    rw [ha]
    exact (canonical27327 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1895 + difference 1 3) (sourceB1895 + difference 3 1) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1895 + difference 1 3) (sourceB1895 + difference 3 1) sourceC1895) = raw27328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27328; decide +kernel
    rw [ha]
    exact (canonical27328 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1895 + difference 2 3) (sourceB1895 + difference 3 2) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1976) := by
    have ha : (tripleCharges (sourceA1895 + difference 2 3) (sourceB1895 + difference 3 2) sourceC1895) = raw27329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27329; decide +kernel
    rw [ha]
    exact (canonical27329 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1895 + difference 3 3) (sourceB1895 + difference 3 3) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1895 + difference 3 3) (sourceB1895 + difference 3 3) sourceC1895) = raw27330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27330; decide +kernel
    rw [ha]
    exact (canonical27330 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1895 + difference 4 3) (sourceB1895 + difference 3 4) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA1895 + difference 4 3) (sourceB1895 + difference 3 4) sourceC1895) = raw27331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27331; decide +kernel
    rw [ha]
    exact (canonical27331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1895 + difference 5 3) (sourceB1895 + difference 3 5) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1895 + difference 5 3) (sourceB1895 + difference 3 5) sourceC1895) = raw27332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27332; decide +kernel
    rw [ha]
    exact (canonical27332 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1895 + sourceB1895) sourceC1895) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1895 + sourceB1895) sourceC1895) = raw27333 := by
      apply Matrix.ext; unfold doubleCharges sourceA1895 sourceB1895 sourceC1895 raw27333; decide +kernel
    rw [ha]
    exact (canonical27333 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1895 sourceB1895 sourceC1895
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1895, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1897 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1897 + difference 0 4) (sourceB1897 + difference 4 0) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1897 + difference 0 4) (sourceB1897 + difference 4 0) sourceC1897) = raw27339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27339; decide +kernel
    rw [ha]
    exact (canonical27339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1897 + difference 1 4) (sourceB1897 + difference 4 1) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1897 + difference 1 4) (sourceB1897 + difference 4 1) sourceC1897) = raw27340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27340; decide +kernel
    rw [ha]
    exact (canonical27340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1897 + difference 2 4) (sourceB1897 + difference 4 2) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA1897 + difference 2 4) (sourceB1897 + difference 4 2) sourceC1897) = raw27341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27341; decide +kernel
    rw [ha]
    exact (canonical27341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1897 + difference 3 4) (sourceB1897 + difference 4 3) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA1897 + difference 3 4) (sourceB1897 + difference 4 3) sourceC1897) = raw27342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27342; decide +kernel
    rw [ha]
    exact (canonical27342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1897 + difference 4 4) (sourceB1897 + difference 4 4) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1897 + difference 4 4) (sourceB1897 + difference 4 4) sourceC1897) = raw27316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27316; decide +kernel
    rw [ha]
    exact (canonical27316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1897 + difference 5 4) (sourceB1897 + difference 4 5) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1897 + difference 5 4) (sourceB1897 + difference 4 5) sourceC1897) = raw27343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27343; decide +kernel
    rw [ha]
    exact (canonical27343 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1897 + sourceB1897) sourceC1897) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1897 + sourceB1897) sourceC1897) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1897 sourceB1897 sourceC1897 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1897 sourceB1897 sourceC1897
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1897, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1898 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 0) (sourceB1898 + difference 0 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 0) (sourceB1898 + difference 0 3) sourceC1898) = raw20137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw20137; decide +kernel
    rw [ha]
    exact (canonical20137 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 1) (sourceB1898 + difference 1 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1808) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 1) (sourceB1898 + difference 1 3) sourceC1898) = raw27344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27344; decide +kernel
    rw [ha]
    exact (canonical27344 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 2) (sourceB1898 + difference 2 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1961) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 2) (sourceB1898 + difference 2 3) sourceC1898) = raw27345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27345; decide +kernel
    rw [ha]
    exact (canonical27345 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 3) (sourceB1898 + difference 3 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 3) (sourceB1898 + difference 3 3) sourceC1898) = raw27346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27346; decide +kernel
    rw [ha]
    exact (canonical27346 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 4) (sourceB1898 + difference 4 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 4) (sourceB1898 + difference 4 3) sourceC1898) = raw27347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27347; decide +kernel
    rw [ha]
    exact (canonical27347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 5) (sourceB1898 + difference 5 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 5) (sourceB1898 + difference 5 3) sourceC1898) = raw27348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27348; decide +kernel
    rw [ha]
    exact (canonical27348 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1898 + sourceB1898) sourceC1898) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1898 + sourceB1898) sourceC1898) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1898 sourceB1898 sourceC1898 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1898 sourceB1898 sourceC1898
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1898, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1899 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1899 + difference 0 3) (sourceB1899 + difference 3 0) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1899 + difference 0 3) (sourceB1899 + difference 3 0) sourceC1899) = raw27349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27349; decide +kernel
    rw [ha]
    exact (canonical27349 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1899 + difference 1 3) (sourceB1899 + difference 3 1) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1899 + difference 1 3) (sourceB1899 + difference 3 1) sourceC1899) = raw27350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27350; decide +kernel
    rw [ha]
    exact (canonical27350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1899 + difference 2 3) (sourceB1899 + difference 3 2) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA1899 + difference 2 3) (sourceB1899 + difference 3 2) sourceC1899) = raw27351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27351; decide +kernel
    rw [ha]
    exact (canonical27351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1899 + difference 3 3) (sourceB1899 + difference 3 3) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA1899 + difference 3 3) (sourceB1899 + difference 3 3) sourceC1899) = raw27352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27352; decide +kernel
    rw [ha]
    exact (canonical27352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1899 + difference 4 3) (sourceB1899 + difference 3 4) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA1899 + difference 4 3) (sourceB1899 + difference 3 4) sourceC1899) = raw27353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27353; decide +kernel
    rw [ha]
    exact (canonical27353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1899 + difference 5 3) (sourceB1899 + difference 3 5) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1899 + difference 5 3) (sourceB1899 + difference 3 5) sourceC1899) = raw27354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27354; decide +kernel
    rw [ha]
    exact (canonical27354 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1899 + sourceB1899) sourceC1899) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1899 + sourceB1899) sourceC1899) = raw27355 := by
      apply Matrix.ext; unfold doubleCharges sourceA1899 sourceB1899 sourceC1899 raw27355; decide +kernel
    rw [ha]
    exact (canonical27355 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1899 sourceB1899 sourceC1899
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1899, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1900 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 0) (sourceB1900 + difference 0 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 0) (sourceB1900 + difference 0 0) sourceC1900) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 1) (sourceB1900 + difference 1 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 1) (sourceB1900 + difference 1 0) sourceC1900) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 2) (sourceB1900 + difference 2 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 2) (sourceB1900 + difference 2 0) sourceC1900) = raw27358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27358; decide +kernel
    rw [ha]
    exact (canonical27358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 3) (sourceB1900 + difference 3 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 3) (sourceB1900 + difference 3 0) sourceC1900) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 4) (sourceB1900 + difference 4 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 4) (sourceB1900 + difference 4 0) sourceC1900) = raw27360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27360; decide +kernel
    rw [ha]
    exact (canonical27360 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 5) (sourceB1900 + difference 5 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 5) (sourceB1900 + difference 5 0) sourceC1900) = raw27361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27361; decide +kernel
    rw [ha]
    exact (canonical27361 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1900 + sourceB1900) sourceC1900) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1900 + sourceB1900) sourceC1900) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1900 sourceB1900 sourceC1900 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1900 sourceB1900 sourceC1900
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1900, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1901 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1901 + difference 0 1) (sourceB1901 + difference 1 0) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1901 + difference 0 1) (sourceB1901 + difference 1 0) sourceC1901) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1901 + difference 1 1) (sourceB1901 + difference 1 1) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1901 + difference 1 1) (sourceB1901 + difference 1 1) sourceC1901) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1901 + difference 2 1) (sourceB1901 + difference 1 2) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA1901 + difference 2 1) (sourceB1901 + difference 1 2) sourceC1901) = raw27362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27362; decide +kernel
    rw [ha]
    exact (canonical27362 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1901 + difference 3 1) (sourceB1901 + difference 1 3) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA1901 + difference 3 1) (sourceB1901 + difference 1 3) sourceC1901) = raw27363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27363; decide +kernel
    rw [ha]
    exact (canonical27363 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1901 + difference 4 1) (sourceB1901 + difference 1 4) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1901 + difference 4 1) (sourceB1901 + difference 1 4) sourceC1901) = raw27364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27364; decide +kernel
    rw [ha]
    exact (canonical27364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1901 + difference 5 1) (sourceB1901 + difference 1 5) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1901 + difference 5 1) (sourceB1901 + difference 1 5) sourceC1901) = raw27365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27365; decide +kernel
    rw [ha]
    exact (canonical27365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1901 + sourceB1901) sourceC1901) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1901 + sourceB1901) sourceC1901) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1901 sourceB1901 sourceC1901 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1901 sourceB1901 sourceC1901
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1901, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1902 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1902 + difference 0 3) (sourceB1902 + difference 3 0) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1902 + difference 0 3) (sourceB1902 + difference 3 0) sourceC1902) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1902 + difference 1 3) (sourceB1902 + difference 3 1) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1902 + difference 1 3) (sourceB1902 + difference 3 1) sourceC1902) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1902 + difference 2 3) (sourceB1902 + difference 3 2) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1902 + difference 2 3) (sourceB1902 + difference 3 2) sourceC1902) = raw27367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27367; decide +kernel
    rw [ha]
    exact (canonical27367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1902 + difference 3 3) (sourceB1902 + difference 3 3) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1902 + difference 3 3) (sourceB1902 + difference 3 3) sourceC1902) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1902 + difference 4 3) (sourceB1902 + difference 3 4) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1902 + difference 4 3) (sourceB1902 + difference 3 4) sourceC1902) = raw27343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27343; decide +kernel
    rw [ha]
    exact (canonical27343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1902 + difference 5 3) (sourceB1902 + difference 3 5) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1902 + difference 5 3) (sourceB1902 + difference 3 5) sourceC1902) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1902 + sourceB1902) sourceC1902) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1902 + sourceB1902) sourceC1902) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1902 sourceB1902 sourceC1902 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1902 sourceB1902 sourceC1902
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1902, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1903 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 0) (sourceB1903 + difference 0 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 0) (sourceB1903 + difference 0 2) sourceC1903) = raw20191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw20191; decide +kernel
    rw [ha]
    exact (canonical20191 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 1) (sourceB1903 + difference 1 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1790) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 1) (sourceB1903 + difference 1 2) sourceC1903) = raw27369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27369; decide +kernel
    rw [ha]
    exact (canonical27369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 2) (sourceB1903 + difference 2 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 2) (sourceB1903 + difference 2 2) sourceC1903) = raw27370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27370; decide +kernel
    rw [ha]
    exact (canonical27370 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 3) (sourceB1903 + difference 3 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 3) (sourceB1903 + difference 3 2) sourceC1903) = raw27371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27371; decide +kernel
    rw [ha]
    exact (canonical27371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 4) (sourceB1903 + difference 4 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 4) (sourceB1903 + difference 4 2) sourceC1903) = raw27372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27372; decide +kernel
    rw [ha]
    exact (canonical27372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 5) (sourceB1903 + difference 5 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 5) (sourceB1903 + difference 5 2) sourceC1903) = raw27373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27373; decide +kernel
    rw [ha]
    exact (canonical27373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1903 + sourceB1903) sourceC1903) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1903 + sourceB1903) sourceC1903) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1903 sourceB1903 sourceC1903 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1903 sourceB1903 sourceC1903
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1903, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1904 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1904 + difference 0 2) (sourceB1904 + difference 2 0) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1904 + difference 0 2) (sourceB1904 + difference 2 0) sourceC1904) = raw27374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27374; decide +kernel
    rw [ha]
    exact (canonical27374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1904 + difference 1 2) (sourceB1904 + difference 2 1) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1904 + difference 1 2) (sourceB1904 + difference 2 1) sourceC1904) = raw5656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw5656; decide +kernel
    rw [ha]
    exact (canonical5656 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1904 + difference 2 2) (sourceB1904 + difference 2 2) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1904 + difference 2 2) (sourceB1904 + difference 2 2) sourceC1904) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1904 + difference 3 2) (sourceB1904 + difference 2 3) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2440) := by
    have ha : (tripleCharges (sourceA1904 + difference 3 2) (sourceB1904 + difference 2 3) sourceC1904) = raw27375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27375; decide +kernel
    rw [ha]
    exact (canonical27375 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1904 + difference 4 2) (sourceB1904 + difference 2 4) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA1904 + difference 4 2) (sourceB1904 + difference 2 4) sourceC1904) = raw27376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27376; decide +kernel
    rw [ha]
    exact (canonical27376 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1904 + difference 5 2) (sourceB1904 + difference 2 5) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1904 + difference 5 2) (sourceB1904 + difference 2 5) sourceC1904) = raw27377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27377; decide +kernel
    rw [ha]
    exact (canonical27377 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1904 + sourceB1904) sourceC1904) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1904 + sourceB1904) sourceC1904) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA1904 sourceB1904 sourceC1904 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1904 sourceB1904 sourceC1904
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1904, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1905 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 0) (sourceB1905 + difference 0 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 0) (sourceB1905 + difference 0 0) sourceC1905) = raw27367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27367; decide +kernel
    rw [ha]
    exact (canonical27367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 1) (sourceB1905 + difference 1 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 1) (sourceB1905 + difference 1 0) sourceC1905) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 2) (sourceB1905 + difference 2 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 2) (sourceB1905 + difference 2 0) sourceC1905) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 3) (sourceB1905 + difference 3 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 3) (sourceB1905 + difference 3 0) sourceC1905) = raw27379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27379; decide +kernel
    rw [ha]
    exact (canonical27379 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 4) (sourceB1905 + difference 4 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 4) (sourceB1905 + difference 4 0) sourceC1905) = raw27380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27380; decide +kernel
    rw [ha]
    exact (canonical27380 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 5) (sourceB1905 + difference 5 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 5) (sourceB1905 + difference 5 0) sourceC1905) = raw27381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27381; decide +kernel
    rw [ha]
    exact (canonical27381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1905 + sourceB1905) sourceC1905) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1905 + sourceB1905) sourceC1905) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1905 sourceB1905 sourceC1905 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1905 sourceB1905 sourceC1905
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1905, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1907 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 0) (sourceB1907 + difference 0 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 909) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 0) (sourceB1907 + difference 0 2) sourceC1907) = raw20218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw20218; decide +kernel
    rw [ha]
    exact (canonical20218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 1) (sourceB1907 + difference 1 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1793) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 1) (sourceB1907 + difference 1 2) sourceC1907) = raw27385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27385; decide +kernel
    rw [ha]
    exact (canonical27385 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 2) (sourceB1907 + difference 2 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 2) (sourceB1907 + difference 2 2) sourceC1907) = raw3846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw3846; decide +kernel
    rw [ha]
    exact (canonical3846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 3) (sourceB1907 + difference 3 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1976) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 3) (sourceB1907 + difference 3 2) sourceC1907) = raw27386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27386; decide +kernel
    rw [ha]
    exact (canonical27386 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 4) (sourceB1907 + difference 4 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 4) (sourceB1907 + difference 4 2) sourceC1907) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 5) (sourceB1907 + difference 5 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 5) (sourceB1907 + difference 5 2) sourceC1907) = raw27387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27387; decide +kernel
    rw [ha]
    exact (canonical27387 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1907 + sourceB1907) sourceC1907) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1907 + sourceB1907) sourceC1907) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA1907 sourceB1907 sourceC1907 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1907 sourceB1907 sourceC1907
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1907, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1600 : Integer.Sparse.reindex keyMap MixedData.row1600 = numericRow1600 := by decide +kernel

theorem numericCheck1600 (x : Master → ℝ) : Integer.Sparse.eval numericRow1600 x =
    (1 : ℝ) * reducedSource1600 x := by
  norm_num [numericRow1600, reducedSource1600, Integer.Sparse.eval, Sparse.eval, nodeValue4056, nodeValue4057, nodeValue4063, nodeValue4068, nodeValue4069, nodeValue4079, nodeValue4083]

theorem reindexCheck1601 : Integer.Sparse.reindex keyMap MixedData.row1601 = numericRow1601 := by decide +kernel

theorem numericCheck1601 (x : Master → ℝ) : Integer.Sparse.eval numericRow1601 x =
    (1 : ℝ) * reducedSource1601 x := by
  norm_num [numericRow1601, reducedSource1601, Integer.Sparse.eval, Sparse.eval, nodeValue940, nodeValue1820, nodeValue1971, nodeValue2063, nodeValue2065, nodeValue4085]

theorem reindexCheck1602 : Integer.Sparse.reindex keyMap MixedData.row1602 = numericRow1602 := by decide +kernel

theorem numericCheck1602 (x : Master → ℝ) : Integer.Sparse.eval numericRow1602 x =
    (1 : ℝ) * reducedSource1602 x := by
  norm_num [numericRow1602, reducedSource1602, Integer.Sparse.eval, Sparse.eval, nodeValue2220, nodeValue2222, nodeValue2230, nodeValue2282, nodeValue2287, nodeValue4081]

theorem reindexCheck1603 : Integer.Sparse.reindex keyMap MixedData.row1603 = numericRow1603 := by decide +kernel

theorem numericCheck1603 (x : Master → ℝ) : Integer.Sparse.eval numericRow1603 x =
    (1 : ℝ) * reducedSource1603 x := by
  norm_num [numericRow1603, reducedSource1603, Integer.Sparse.eval, Sparse.eval, nodeValue931, nodeValue1813, nodeValue1965, nodeValue2026, nodeValue2037, nodeValue2058, nodeValue4084]

theorem reindexCheck1604 : Integer.Sparse.reindex keyMap MixedData.row1604 = numericRow1604 := by decide +kernel

theorem numericCheck1604 (x : Master → ℝ) : Integer.Sparse.eval numericRow1604 x =
    (1 : ℝ) * reducedSource1604 x := by
  norm_num [numericRow1604, reducedSource1604, Integer.Sparse.eval, Sparse.eval, nodeValue914, nodeValue1797, nodeValue1957, nodeValue1980, nodeValue2026, nodeValue2028, nodeValue4084]

theorem reindexCheck1605 : Integer.Sparse.reindex keyMap MixedData.row1605 = numericRow1605 := by decide +kernel

theorem numericCheck1605 (x : Master → ℝ) : Integer.Sparse.eval numericRow1605 x =
    (1 : ℝ) * reducedSource1605 x := by
  norm_num [numericRow1605, reducedSource1605, Integer.Sparse.eval, Sparse.eval, nodeValue949, nodeValue1828, nodeValue1976, nodeValue2092, nodeValue2110, nodeValue4083]

theorem reindexCheck1606 : Integer.Sparse.reindex keyMap MixedData.row1606 = numericRow1606 := by decide +kernel

theorem numericCheck1606 (x : Master → ℝ) : Integer.Sparse.eval numericRow1606 x =
    (1 : ℝ) * reducedSource1606 x := by
  norm_num [numericRow1606, reducedSource1606, Integer.Sparse.eval, Sparse.eval, nodeValue2219, nodeValue2220, nodeValue2221, nodeValue2224, nodeValue4081]

theorem reindexCheck1607 : Integer.Sparse.reindex keyMap MixedData.row1607 = numericRow1607 := by decide +kernel

theorem numericCheck1607 (x : Master → ℝ) : Integer.Sparse.eval numericRow1607 x =
    (1 : ℝ) * reducedSource1607 x := by
  norm_num [numericRow1607, reducedSource1607, Integer.Sparse.eval, Sparse.eval, nodeValue925, nodeValue1808, nodeValue1961, nodeValue2035, nodeValue2054, nodeValue2062, nodeValue4084]

theorem reindexCheck1608 : Integer.Sparse.reindex keyMap MixedData.row1608 = numericRow1608 := by decide +kernel

theorem numericCheck1608 (x : Master → ℝ) : Integer.Sparse.eval numericRow1608 x =
    (1 : ℝ) * reducedSource1608 x := by
  norm_num [numericRow1608, reducedSource1608, Integer.Sparse.eval, Sparse.eval, nodeValue1137, nodeValue2340, nodeValue2430, nodeValue2486, nodeValue2497, nodeValue2515, nodeValue4092]

theorem reindexCheck1609 : Integer.Sparse.reindex keyMap MixedData.row1609 = numericRow1609 := by decide +kernel

theorem numericCheck1609 (x : Master → ℝ) : Integer.Sparse.eval numericRow1609 x =
    (1 : ℝ) * reducedSource1609 x := by
  norm_num [numericRow1609, reducedSource1609, Integer.Sparse.eval, Sparse.eval, nodeValue1948, nodeValue2207, nodeValue3358, nodeValue3437, nodeValue3472, nodeValue3481, nodeValue4081]

theorem reindexCheck1610 : Integer.Sparse.reindex keyMap MixedData.row1610 = numericRow1610 := by decide +kernel

theorem numericCheck1610 (x : Master → ℝ) : Integer.Sparse.eval numericRow1610 x =
    (1 : ℝ) * reducedSource1610 x := by
  norm_num [numericRow1610, reducedSource1610, Integer.Sparse.eval, Sparse.eval, nodeValue1910, nodeValue1916, nodeValue1917, nodeValue1948, nodeValue2207, nodeValue3472, nodeValue4081]

theorem reindexCheck1611 : Integer.Sparse.reindex keyMap MixedData.row1611 = numericRow1611 := by decide +kernel

theorem numericCheck1611 (x : Master → ℝ) : Integer.Sparse.eval numericRow1611 x =
    (1 : ℝ) * reducedSource1611 x := by
  norm_num [numericRow1611, reducedSource1611, Integer.Sparse.eval, Sparse.eval, nodeValue2201, nodeValue2203, nodeValue2207, nodeValue2224, nodeValue2259, nodeValue3481, nodeValue4081]

theorem reindexCheck1612 : Integer.Sparse.reindex keyMap MixedData.row1612 = numericRow1612 := by decide +kernel

theorem numericCheck1612 (x : Master → ℝ) : Integer.Sparse.eval numericRow1612 x =
    (1 : ℝ) * reducedSource1612 x := by
  norm_num [numericRow1612, reducedSource1612, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue1790, nodeValue1973, nodeValue2009, nodeValue2020, nodeValue2025, nodeValue4083]

theorem reindexCheck1613 : Integer.Sparse.reindex keyMap MixedData.row1613 = numericRow1613 := by decide +kernel

theorem numericCheck1613 (x : Master → ℝ) : Integer.Sparse.eval numericRow1613 x =
    (1 : ℝ) * reducedSource1613 x := by
  norm_num [numericRow1613, reducedSource1613, Integer.Sparse.eval, Sparse.eval, nodeValue1116, nodeValue2323, nodeValue2440, nodeValue2471, nodeValue2483, nodeValue4091]

theorem reindexCheck1614 : Integer.Sparse.reindex keyMap MixedData.row1614 = numericRow1614 := by decide +kernel

theorem numericCheck1614 (x : Master → ℝ) : Integer.Sparse.eval numericRow1614 x =
    (1 : ℝ) * reducedSource1614 x := by
  norm_num [numericRow1614, reducedSource1614, Integer.Sparse.eval, Sparse.eval, nodeValue1940, nodeValue2201, nodeValue3350, nodeValue3466, nodeValue3481, nodeValue4081]

theorem reindexCheck1615 : Integer.Sparse.reindex keyMap MixedData.row1615 = numericRow1615 := by decide +kernel

theorem numericCheck1615 (x : Master → ℝ) : Integer.Sparse.eval numericRow1615 x =
    (1 : ℝ) * reducedSource1615 x := by
  norm_num [numericRow1615, reducedSource1615, Integer.Sparse.eval, Sparse.eval, nodeValue909, nodeValue1793, nodeValue1976, nodeValue2010, nodeValue2023, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1600 (mixedVector B) = 0 := by
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1890, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4056, h4057, h4063, h4068, h4069, h4079, h4083, reducedSource1600] using sourceEq1890 B hB

theorem rowSound1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1600 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1600, numericCheck1600, reducedZero1600 B hB hF, mul_zero]

theorem reducedZero1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1601 (mixedVector B) = 0 := by
  have h940 : mixedVector B (Sum.inr 940) = Sparse.eval nodeValue940 (mixedVector B) := by
    change mixedMoment B node940 node940Labels = _
    exact sound940 B hB hF
  have h1820 : mixedVector B (Sum.inr 1820) = Sparse.eval nodeValue1820 (mixedVector B) := by
    change mixedMoment B node1820 node1820Labels = _
    exact sound1820 B hB hF
  have h1971 : mixedVector B (Sum.inr 1971) = Sparse.eval nodeValue1971 (mixedVector B) := by
    change mixedMoment B node1971 node1971Labels = _
    exact sound1971 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1891, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h940, h1820, h1971, h2063, h2065, h4085, reducedSource1601] using sourceEq1891 B hB

theorem rowSound1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1601 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1601, numericCheck1601, reducedZero1601 B hB hF, mul_zero]

theorem reducedZero1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1602 (mixedVector B) = 0 := by
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1892, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2220, h2222, h2230, h2282, h2287, h4081, reducedSource1602] using sourceEq1892 B hB

theorem rowSound1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1602 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1602, numericCheck1602, reducedZero1602 B hB hF, mul_zero]

theorem reducedZero1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1603 (mixedVector B) = 0 := by
  have h931 : mixedVector B (Sum.inr 931) = Sparse.eval nodeValue931 (mixedVector B) := by
    change mixedMoment B node931 node931Labels = _
    exact sound931 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h1965 : mixedVector B (Sum.inr 1965) = Sparse.eval nodeValue1965 (mixedVector B) := by
    change mixedMoment B node1965 node1965Labels = _
    exact sound1965 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1893, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h931, h1813, h1965, h2026, h2037, h2058, h4084, reducedSource1603] using sourceEq1893 B hB

theorem rowSound1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1603 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1603, numericCheck1603, reducedZero1603 B hB hF, mul_zero]

theorem reducedZero1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1604 (mixedVector B) = 0 := by
  have h914 : mixedVector B (Sum.inr 914) = Sparse.eval nodeValue914 (mixedVector B) := by
    change mixedMoment B node914 node914Labels = _
    exact sound914 B hB hF
  have h1797 : mixedVector B (Sum.inr 1797) = Sparse.eval nodeValue1797 (mixedVector B) := by
    change mixedMoment B node1797 node1797Labels = _
    exact sound1797 B hB hF
  have h1957 : mixedVector B (Sum.inr 1957) = Sparse.eval nodeValue1957 (mixedVector B) := by
    change mixedMoment B node1957 node1957Labels = _
    exact sound1957 B hB hF
  have h1980 : mixedVector B (Sum.inr 1980) = Sparse.eval nodeValue1980 (mixedVector B) := by
    change mixedMoment B node1980 node1980Labels = _
    exact sound1980 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1894, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h914, h1797, h1957, h1980, h2026, h2028, h4084, reducedSource1604] using sourceEq1894 B hB

theorem rowSound1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1604 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1604, numericCheck1604, reducedZero1604 B hB hF, mul_zero]

theorem reducedZero1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1605 (mixedVector B) = 0 := by
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h1828 : mixedVector B (Sum.inr 1828) = Sparse.eval nodeValue1828 (mixedVector B) := by
    change mixedMoment B node1828 node1828Labels = _
    exact sound1828 B hB hF
  have h1976 : mixedVector B (Sum.inr 1976) = Sparse.eval nodeValue1976 (mixedVector B) := by
    change mixedMoment B node1976 node1976Labels = _
    exact sound1976 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1895, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h949, h1828, h1976, h2092, h2110, h4083, reducedSource1605] using sourceEq1895 B hB

theorem rowSound1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1605 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1605, numericCheck1605, reducedZero1605 B hB hF, mul_zero]

theorem reducedZero1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1606 (mixedVector B) = 0 := by
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1897, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2219, h2220, h2221, h2224, h4081, reducedSource1606] using sourceEq1897 B hB

theorem rowSound1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1606 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1606, numericCheck1606, reducedZero1606 B hB hF, mul_zero]

theorem reducedZero1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1607 (mixedVector B) = 0 := by
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h1808 : mixedVector B (Sum.inr 1808) = Sparse.eval nodeValue1808 (mixedVector B) := by
    change mixedMoment B node1808 node1808Labels = _
    exact sound1808 B hB hF
  have h1961 : mixedVector B (Sum.inr 1961) = Sparse.eval nodeValue1961 (mixedVector B) := by
    change mixedMoment B node1961 node1961Labels = _
    exact sound1961 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1898, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h925, h1808, h1961, h2035, h2054, h2062, h4084, reducedSource1607] using sourceEq1898 B hB

theorem rowSound1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1607 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1607, numericCheck1607, reducedZero1607 B hB hF, mul_zero]

theorem reducedZero1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1608 (mixedVector B) = 0 := by
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1899, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1137, h2340, h2430, h2486, h2497, h2515, h4092, reducedSource1608] using sourceEq1899 B hB

theorem rowSound1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1608 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1608, numericCheck1608, reducedZero1608 B hB hF, mul_zero]

theorem reducedZero1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1609 (mixedVector B) = 0 := by
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1900, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1948, h2207, h3358, h3437, h3472, h3481, h4081, reducedSource1609] using sourceEq1900 B hB

theorem rowSound1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1609 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1609, numericCheck1609, reducedZero1609 B hB hF, mul_zero]

theorem reducedZero1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1610 (mixedVector B) = 0 := by
  have h1910 : mixedVector B (Sum.inr 1910) = Sparse.eval nodeValue1910 (mixedVector B) := by
    change mixedMoment B node1910 node1910Labels = _
    exact sound1910 B hB hF
  have h1916 : mixedVector B (Sum.inr 1916) = Sparse.eval nodeValue1916 (mixedVector B) := by
    change mixedMoment B node1916 node1916Labels = _
    exact sound1916 B hB hF
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1901, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1910, h1916, h1917, h1948, h2207, h3472, h4081, reducedSource1610] using sourceEq1901 B hB

theorem rowSound1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1610 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1610, numericCheck1610, reducedZero1610 B hB hF, mul_zero]

theorem reducedZero1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1611 (mixedVector B) = 0 := by
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1902, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2201, h2203, h2207, h2224, h2259, h3481, h4081, reducedSource1611] using sourceEq1902 B hB

theorem rowSound1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1611 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1611, numericCheck1611, reducedZero1611 B hB hF, mul_zero]

theorem reducedZero1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1612 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h1790 : mixedVector B (Sum.inr 1790) = Sparse.eval nodeValue1790 (mixedVector B) := by
    change mixedMoment B node1790 node1790Labels = _
    exact sound1790 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1903, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h1790, h1973, h2009, h2020, h2025, h4083, reducedSource1612] using sourceEq1903 B hB

theorem rowSound1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1612 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1612, numericCheck1612, reducedZero1612 B hB hF, mul_zero]

theorem reducedZero1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1613 (mixedVector B) = 0 := by
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2440 : mixedVector B (Sum.inr 2440) = Sparse.eval nodeValue2440 (mixedVector B) := by
    change mixedMoment B node2440 node2440Labels = _
    exact sound2440 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1904, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1116, h2323, h2440, h2471, h2483, h4091, reducedSource1613] using sourceEq1904 B hB

theorem rowSound1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1613 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1613, numericCheck1613, reducedZero1613 B hB hF, mul_zero]

theorem reducedZero1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1614 (mixedVector B) = 0 := by
  have h1940 : mixedVector B (Sum.inr 1940) = Sparse.eval nodeValue1940 (mixedVector B) := by
    change mixedMoment B node1940 node1940Labels = _
    exact sound1940 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1905, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1940, h2201, h3350, h3466, h3481, h4081, reducedSource1614] using sourceEq1905 B hB

theorem rowSound1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1614 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1614, numericCheck1614, reducedZero1614 B hB hF, mul_zero]

theorem reducedZero1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1615 (mixedVector B) = 0 := by
  have h909 : mixedVector B (Sum.inr 909) = Sparse.eval nodeValue909 (mixedVector B) := by
    change mixedMoment B node909 node909Labels = _
    exact sound909 B hB hF
  have h1793 : mixedVector B (Sum.inr 1793) = Sparse.eval nodeValue1793 (mixedVector B) := by
    change mixedMoment B node1793 node1793Labels = _
    exact sound1793 B hB hF
  have h1976 : mixedVector B (Sum.inr 1976) = Sparse.eval nodeValue1976 (mixedVector B) := by
    change mixedMoment B node1976 node1976Labels = _
    exact sound1976 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1907, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h909, h1793, h1976, h2010, h2023, h4083, reducedSource1615] using sourceEq1907 B hB

theorem rowSound1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1615 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1615, numericCheck1615, reducedZero1615 B hB hF, mul_zero]

theorem sourceRowsAt1600 : MixedData.sourceRows (1600 : Fin 2425) =
    MixedData.row1600 := by decide +kernel

theorem sourceRowsAt1601 : MixedData.sourceRows (1601 : Fin 2425) =
    MixedData.row1601 := by decide +kernel

theorem sourceRowsAt1602 : MixedData.sourceRows (1602 : Fin 2425) =
    MixedData.row1602 := by decide +kernel

theorem sourceRowsAt1603 : MixedData.sourceRows (1603 : Fin 2425) =
    MixedData.row1603 := by decide +kernel

theorem sourceRowsAt1604 : MixedData.sourceRows (1604 : Fin 2425) =
    MixedData.row1604 := by decide +kernel

theorem sourceRowsAt1605 : MixedData.sourceRows (1605 : Fin 2425) =
    MixedData.row1605 := by decide +kernel

theorem sourceRowsAt1606 : MixedData.sourceRows (1606 : Fin 2425) =
    MixedData.row1606 := by decide +kernel

theorem sourceRowsAt1607 : MixedData.sourceRows (1607 : Fin 2425) =
    MixedData.row1607 := by decide +kernel

theorem sourceRowsAt1608 : MixedData.sourceRows (1608 : Fin 2425) =
    MixedData.row1608 := by decide +kernel

theorem sourceRowsAt1609 : MixedData.sourceRows (1609 : Fin 2425) =
    MixedData.row1609 := by decide +kernel

theorem sourceRowsAt1610 : MixedData.sourceRows (1610 : Fin 2425) =
    MixedData.row1610 := by decide +kernel

theorem sourceRowsAt1611 : MixedData.sourceRows (1611 : Fin 2425) =
    MixedData.row1611 := by decide +kernel

theorem sourceRowsAt1612 : MixedData.sourceRows (1612 : Fin 2425) =
    MixedData.row1612 := by decide +kernel

theorem sourceRowsAt1613 : MixedData.sourceRows (1613 : Fin 2425) =
    MixedData.row1613 := by decide +kernel

theorem sourceRowsAt1614 : MixedData.sourceRows (1614 : Fin 2425) =
    MixedData.row1614 := by decide +kernel

theorem sourceRowsAt1615 : MixedData.sourceRows (1615 : Fin 2425) =
    MixedData.row1615 := by decide +kernel

theorem chunkSound100_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 100) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1600 ∨ k.val = 1601 ∨ k.val = 1602 ∨ k.val = 1603 ∨ k.val = 1604 ∨ k.val = 1605 ∨ k.val = 1606 ∨ k.val = 1607 ∨ k.val = 1608 ∨ k.val = 1609 ∨ k.val = 1610 ∨ k.val = 1611 ∨ k.val = 1612 ∨ k.val = 1613 ∨ k.val = 1614 ∨ k.val = 1615 := by omega
  rcases heq with h1600 | h1601 | h1602 | h1603 | h1604 | h1605 | h1606 | h1607 | h1608 | h1609 | h1610 | h1611 | h1612 | h1613 | h1614 | h1615
  · have he : k = (1600 : Fin 2425) := Fin.ext h1600
    subst k
    rw [sourceRowsAt1600]
    exact rowSound1600 B hB hF
  · have he : k = (1601 : Fin 2425) := Fin.ext h1601
    subst k
    rw [sourceRowsAt1601]
    exact rowSound1601 B hB hF
  · have he : k = (1602 : Fin 2425) := Fin.ext h1602
    subst k
    rw [sourceRowsAt1602]
    exact rowSound1602 B hB hF
  · have he : k = (1603 : Fin 2425) := Fin.ext h1603
    subst k
    rw [sourceRowsAt1603]
    exact rowSound1603 B hB hF
  · have he : k = (1604 : Fin 2425) := Fin.ext h1604
    subst k
    rw [sourceRowsAt1604]
    exact rowSound1604 B hB hF
  · have he : k = (1605 : Fin 2425) := Fin.ext h1605
    subst k
    rw [sourceRowsAt1605]
    exact rowSound1605 B hB hF
  · have he : k = (1606 : Fin 2425) := Fin.ext h1606
    subst k
    rw [sourceRowsAt1606]
    exact rowSound1606 B hB hF
  · have he : k = (1607 : Fin 2425) := Fin.ext h1607
    subst k
    rw [sourceRowsAt1607]
    exact rowSound1607 B hB hF
  · have he : k = (1608 : Fin 2425) := Fin.ext h1608
    subst k
    rw [sourceRowsAt1608]
    exact rowSound1608 B hB hF
  · have he : k = (1609 : Fin 2425) := Fin.ext h1609
    subst k
    rw [sourceRowsAt1609]
    exact rowSound1609 B hB hF
  · have he : k = (1610 : Fin 2425) := Fin.ext h1610
    subst k
    rw [sourceRowsAt1610]
    exact rowSound1610 B hB hF
  · have he : k = (1611 : Fin 2425) := Fin.ext h1611
    subst k
    rw [sourceRowsAt1611]
    exact rowSound1611 B hB hF
  · have he : k = (1612 : Fin 2425) := Fin.ext h1612
    subst k
    rw [sourceRowsAt1612]
    exact rowSound1612 B hB hF
  · have he : k = (1613 : Fin 2425) := Fin.ext h1613
    subst k
    rw [sourceRowsAt1613]
    exact rowSound1613 B hB hF
  · have he : k = (1614 : Fin 2425) := Fin.ext h1614
    subst k
    rw [sourceRowsAt1614]
    exact rowSound1614 B hB hF
  · have he : k = (1615 : Fin 2425) := Fin.ext h1615
    subst k
    rw [sourceRowsAt1615]
    exact rowSound1615 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e_oai
