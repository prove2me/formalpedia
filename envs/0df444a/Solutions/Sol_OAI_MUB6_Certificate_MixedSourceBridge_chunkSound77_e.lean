-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:44.70977+00:00
-- url     : https://prove2.me/submissions/08a1bad2-2796-4391-b6a4-de0dc0784c67

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1232_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1233_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20079 raw20079Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20079 raw20079Labels = mixedMoment B raw20079step0 raw20079step0Labels := by
      have hz : ∀ j, raw20079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20079step0 = (fun i j => raw20079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20079step0 raw20079; decide +kernel
      have hl : raw20079step0Labels = raw20079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079 raw20079Labels permutation434 hz
    mixedMoment B raw20079step0 raw20079step0Labels = mixedMoment B raw20079step1 raw20079step1Labels := by
      have hz : ∀ j, raw20079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20079step1 = (fun i j => raw20079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20079step1 raw20079step0; decide +kernel
      have hl : raw20079step1Labels = raw20079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step0 raw20079step0Labels permutation80 hz
    mixedMoment B raw20079step1 raw20079step1Labels = mixedMoment B raw20079step2 raw20079step2Labels := by
      have hz : ∀ j, raw20079step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20079step2 = (fun i j => raw20079step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20079step2 raw20079step1; decide +kernel
      have hl : raw20079step2Labels = raw20079step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step1 raw20079step1Labels permutation14 hz
    mixedMoment B raw20079step2 raw20079step2Labels = mixedMoment B raw20079step3 raw20079step3Labels := by
      have hz : ∀ i, raw20079step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20079step3 = (fun i j => raw20079step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20079step3 raw20079step2; decide +kernel
      have hl : raw20079step3Labels = (fun j => raw20079step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20079step2 raw20079step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

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

theorem canonical20081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20081 raw20081Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20081 raw20081Labels = mixedMoment B raw20081step0 raw20081step0Labels := by
      have hz : ∀ j, raw20081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20081step0 = (fun i j => raw20081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20081step0 raw20081; decide +kernel
      have hl : raw20081step0Labels = raw20081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081 raw20081Labels permutation434 hz
    mixedMoment B raw20081step0 raw20081step0Labels = mixedMoment B raw20081step1 raw20081step1Labels := by
      have hz : ∀ j, raw20081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20081step1 = (fun i j => raw20081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20081step1 raw20081step0; decide +kernel
      have hl : raw20081step1Labels = raw20081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081step0 raw20081step0Labels permutation56 hz
    mixedMoment B raw20081step1 raw20081step1Labels = mixedMoment B raw20081step2 raw20081step2Labels := by
      have hz : ∀ i, raw20081step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20081step2 = (fun i j => raw20081step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20081step2 raw20081step1; decide +kernel
      have hl : raw20081step2Labels = (fun j => raw20081step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20081step1 raw20081step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

theorem canonical20082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20082 raw20082Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20082 raw20082Labels = mixedMoment B raw20082step0 raw20082step0Labels := by
      have hz : ∀ j, raw20082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20082step0 = (fun i j => raw20082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20082step0 raw20082; decide +kernel
      have hl : raw20082step0Labels = raw20082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082 raw20082Labels permutation346 hz
    mixedMoment B raw20082step0 raw20082step0Labels = mixedMoment B raw20082step1 raw20082step1Labels := by
      have hz : ∀ j, raw20082step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20082step1 = (fun i j => raw20082step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20082step1 raw20082step0; decide +kernel
      have hl : raw20082step1Labels = raw20082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082step0 raw20082step0Labels permutation56 hz
    mixedMoment B raw20082step1 raw20082step1Labels = mixedMoment B raw20082step2 raw20082step2Labels := by
      have hz : ∀ i, raw20082step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20082step2 = (fun i j => raw20082step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20082step2 raw20082step1; decide +kernel
      have hl : raw20082step2Labels = (fun j => raw20082step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20082step1 raw20082step1Labels permutation6 hz
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

theorem canonical20141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20141 raw20141Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw20141 raw20141Labels = mixedMoment B raw20141step0 raw20141step0Labels := by
      have hz : ∀ j, raw20141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20141step0 = (fun i j => raw20141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20141step0 raw20141; decide +kernel
      have hl : raw20141step0Labels = raw20141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141 raw20141Labels permutation346 hz
    mixedMoment B raw20141step0 raw20141step0Labels = mixedMoment B raw20141step1 raw20141step1Labels := by
      have hz : ∀ j, raw20141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20141step1 = (fun i j => raw20141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20141step1 raw20141step0; decide +kernel
      have hl : raw20141step1Labels = raw20141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141step0 raw20141step0Labels permutation56 hz
    mixedMoment B raw20141step1 raw20141step1Labels = mixedMoment B raw20141step2 raw20141step2Labels := by
      have ha : raw20141step2 = (fun i j => raw20141step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20141step2 raw20141step1; decide +kernel
      have hl : raw20141step2Labels = raw20141step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20141step1 raw20141step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

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

theorem canonical20195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20195 raw20195Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw20195 raw20195Labels = mixedMoment B raw20195step0 raw20195step0Labels := by
      have hz : ∀ j, raw20195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20195step0 = (fun i j => raw20195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20195step0 raw20195; decide +kernel
      have hl : raw20195step0Labels = raw20195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20195 raw20195Labels permutation265 hz
    mixedMoment B raw20195step0 raw20195step0Labels = mixedMoment B raw20195step1 raw20195step1Labels := by
      have ha : raw20195step1 = (fun i j => raw20195step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20195step1 raw20195step0; decide +kernel
      have hl : raw20195step1Labels = raw20195step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20195step0 raw20195step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

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

theorem canonical22301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22301 raw22301Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22301 raw22301Labels = mixedMoment B raw22301step0 raw22301step0Labels := by
      have hz : ∀ j, raw22301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22301step0 = (fun i j => raw22301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22301step0 raw22301; decide +kernel
      have hl : raw22301step0Labels = raw22301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22301 raw22301Labels permutation434 hz
    mixedMoment B raw22301step0 raw22301step0Labels = mixedMoment B raw22301step1 raw22301step1Labels := by
      have hz : ∀ j, raw22301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22301step1 = (fun i j => raw22301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22301step1 raw22301step0; decide +kernel
      have hl : raw22301step1Labels = raw22301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22301step0 raw22301step0Labels permutation80 hz
    mixedMoment B raw22301step1 raw22301step1Labels = mixedMoment B raw22301step2 raw22301step2Labels := by
      have hz : ∀ i, raw22301step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22301step2 = (fun i j => raw22301step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22301step2 raw22301step1; decide +kernel
      have hl : raw22301step2Labels = (fun j => raw22301step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22301step1 raw22301step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

theorem canonical22302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22302 raw22302Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22302 raw22302Labels = mixedMoment B raw22302step0 raw22302step0Labels := by
      have hz : ∀ j, raw22302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22302step0 = (fun i j => raw22302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22302step0 raw22302; decide +kernel
      have hl : raw22302step0Labels = raw22302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22302 raw22302Labels permutation434 hz
    mixedMoment B raw22302step0 raw22302step0Labels = mixedMoment B raw22302step1 raw22302step1Labels := by
      have hz : ∀ i, raw22302step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22302step1 = (fun i j => raw22302step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22302step1 raw22302step0; decide +kernel
      have hl : raw22302step1Labels = (fun j => raw22302step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22302step0 raw22302step0Labels permutation6 hz
    mixedMoment B raw22302step1 raw22302step1Labels = mixedMoment B raw22302step2 raw22302step2Labels := by
      have ha : raw22302step2 = (fun i j => raw22302step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22302step2 raw22302step1; decide +kernel
      have hl : raw22302step2Labels = raw22302step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22302step1 raw22302step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical22303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22303 raw22303Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22303 raw22303Labels = mixedMoment B raw22303step0 raw22303step0Labels := by
      have hz : ∀ j, raw22303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22303step0 = (fun i j => raw22303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22303step0 raw22303; decide +kernel
      have hl : raw22303step0Labels = raw22303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22303 raw22303Labels permutation346 hz
    mixedMoment B raw22303step0 raw22303step0Labels = mixedMoment B raw22303step1 raw22303step1Labels := by
      have hz : ∀ i, raw22303step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22303step1 = (fun i j => raw22303step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22303step1 raw22303step0; decide +kernel
      have hl : raw22303step1Labels = (fun j => raw22303step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22303step0 raw22303step0Labels permutation6 hz
    mixedMoment B raw22303step1 raw22303step1Labels = mixedMoment B raw22303step2 raw22303step2Labels := by
      have ha : raw22303step2 = (fun i j => raw22303step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22303step2 raw22303step1; decide +kernel
      have hl : raw22303step2Labels = raw22303step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22303step1 raw22303step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical22304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22304 raw22304Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22304 raw22304Labels = mixedMoment B raw22304step0 raw22304step0Labels := by
      have hz : ∀ j, raw22304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22304step0 = (fun i j => raw22304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22304step0 raw22304; decide +kernel
      have hl : raw22304step0Labels = raw22304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22304 raw22304Labels permutation434 hz
    mixedMoment B raw22304step0 raw22304step0Labels = mixedMoment B raw22304step1 raw22304step1Labels := by
      have hz : ∀ j, raw22304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22304step1 = (fun i j => raw22304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22304step1 raw22304step0; decide +kernel
      have hl : raw22304step1Labels = raw22304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22304step0 raw22304step0Labels permutation56 hz
    mixedMoment B raw22304step1 raw22304step1Labels = mixedMoment B raw22304step2 raw22304step2Labels := by
      have hz : ∀ i, raw22304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22304step2 = (fun i j => raw22304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22304step2 raw22304step1; decide +kernel
      have hl : raw22304step2Labels = (fun j => raw22304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22304step1 raw22304step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

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

theorem canonical22306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22306 raw22306Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22306 raw22306Labels = mixedMoment B raw22306step0 raw22306step0Labels := by
      have hz : ∀ j, raw22306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22306step0 = (fun i j => raw22306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22306step0 raw22306; decide +kernel
      have hl : raw22306step0Labels = raw22306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22306 raw22306Labels permutation265 hz
    mixedMoment B raw22306step0 raw22306step0Labels = mixedMoment B raw22306step1 raw22306step1Labels := by
      have hz : ∀ i, raw22306step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22306step1 = (fun i j => raw22306step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22306step1 raw22306step0; decide +kernel
      have hl : raw22306step1Labels = (fun j => raw22306step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22306step0 raw22306step0Labels permutation6 hz
    mixedMoment B raw22306step1 raw22306step1Labels = mixedMoment B raw22306step2 raw22306step2Labels := by
      have ha : raw22306step2 = (fun i j => raw22306step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22306step2 raw22306step1; decide +kernel
      have hl : raw22306step2Labels = raw22306step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22306step1 raw22306step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical22307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22307 raw22307Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22307 raw22307Labels = mixedMoment B raw22307step0 raw22307step0Labels := by
      have hz : ∀ j, raw22307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22307step0 = (fun i j => raw22307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22307step0 raw22307; decide +kernel
      have hl : raw22307step0Labels = raw22307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307 raw22307Labels permutation346 hz
    mixedMoment B raw22307step0 raw22307step0Labels = mixedMoment B raw22307step1 raw22307step1Labels := by
      have hz : ∀ j, raw22307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22307step1 = (fun i j => raw22307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22307step1 raw22307step0; decide +kernel
      have hl : raw22307step1Labels = raw22307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307step0 raw22307step0Labels permutation56 hz
    mixedMoment B raw22307step1 raw22307step1Labels = mixedMoment B raw22307step2 raw22307step2Labels := by
      have hz : ∀ i, raw22307step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22307step2 = (fun i j => raw22307step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22307step2 raw22307step1; decide +kernel
      have hl : raw22307step2Labels = (fun j => raw22307step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22307step1 raw22307step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

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

theorem canonical22309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22309 raw22309Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22309 raw22309Labels = mixedMoment B raw22309step0 raw22309step0Labels := by
      have hz : ∀ j, raw22309 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22309step0 = (fun i j => raw22309 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22309step0 raw22309; decide +kernel
      have hl : raw22309step0Labels = raw22309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22309 raw22309Labels permutation265 hz
    mixedMoment B raw22309step0 raw22309step0Labels = mixedMoment B raw22309step1 raw22309step1Labels := by
      have hz : ∀ i, raw22309step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22309step1 = (fun i j => raw22309step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22309step1 raw22309step0; decide +kernel
      have hl : raw22309step1Labels = (fun j => raw22309step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22309step0 raw22309step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

theorem canonical22310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22310 raw22310Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw22310 raw22310Labels = mixedMoment B raw22310step0 raw22310step0Labels := by
      have hz : ∀ j, raw22310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22310step0 = (fun i j => raw22310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22310step0 raw22310; decide +kernel
      have hl : raw22310step0Labels = raw22310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310 raw22310Labels permutation434 hz
    mixedMoment B raw22310step0 raw22310step0Labels = mixedMoment B raw22310step1 raw22310step1Labels := by
      have hz : ∀ j, raw22310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22310step1 = (fun i j => raw22310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22310step1 raw22310step0; decide +kernel
      have hl : raw22310step1Labels = raw22310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step0 raw22310step0Labels permutation80 hz
    mixedMoment B raw22310step1 raw22310step1Labels = mixedMoment B raw22310step2 raw22310step2Labels := by
      have hz : ∀ j, raw22310step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22310step2 = (fun i j => raw22310step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22310step2 raw22310step1; decide +kernel
      have hl : raw22310step2Labels = raw22310step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step1 raw22310step1Labels permutation14 hz
    mixedMoment B raw22310step2 raw22310step2Labels = mixedMoment B raw22310step3 raw22310step3Labels := by
      have hz : ∀ i, raw22310step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22310step3 = (fun i j => raw22310step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22310step3 raw22310step2; decide +kernel
      have hl : raw22310step3Labels = (fun j => raw22310step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22310step2 raw22310step2Labels permutation6 hz
    _ = mixedMoment B node4061 node4061Labels := by rfl

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

theorem canonical22312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22312 raw22312Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22312 raw22312Labels = mixedMoment B raw22312step0 raw22312step0Labels := by
      have hz : ∀ j, raw22312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22312step0 = (fun i j => raw22312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22312step0 raw22312; decide +kernel
      have hl : raw22312step0Labels = raw22312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312 raw22312Labels permutation434 hz
    mixedMoment B raw22312step0 raw22312step0Labels = mixedMoment B raw22312step1 raw22312step1Labels := by
      have hz : ∀ j, raw22312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22312step1 = (fun i j => raw22312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22312step1 raw22312step0; decide +kernel
      have hl : raw22312step1Labels = raw22312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312step0 raw22312step0Labels permutation56 hz
    mixedMoment B raw22312step1 raw22312step1Labels = mixedMoment B raw22312step2 raw22312step2Labels := by
      have hz : ∀ i, raw22312step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22312step2 = (fun i j => raw22312step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22312step2 raw22312step1; decide +kernel
      have hl : raw22312step2Labels = (fun j => raw22312step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22312step1 raw22312step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical22313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22313 raw22313Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22313 raw22313Labels = mixedMoment B raw22313step0 raw22313step0Labels := by
      have hz : ∀ j, raw22313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22313step0 = (fun i j => raw22313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22313step0 raw22313; decide +kernel
      have hl : raw22313step0Labels = raw22313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313 raw22313Labels permutation346 hz
    mixedMoment B raw22313step0 raw22313step0Labels = mixedMoment B raw22313step1 raw22313step1Labels := by
      have hz : ∀ j, raw22313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22313step1 = (fun i j => raw22313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22313step1 raw22313step0; decide +kernel
      have hl : raw22313step1Labels = raw22313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313step0 raw22313step0Labels permutation56 hz
    mixedMoment B raw22313step1 raw22313step1Labels = mixedMoment B raw22313step2 raw22313step2Labels := by
      have hz : ∀ i, raw22313step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22313step2 = (fun i j => raw22313step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22313step2 raw22313step1; decide +kernel
      have hl : raw22313step2Labels = (fun j => raw22313step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22313step1 raw22313step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

theorem canonical22314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22314 raw22314Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw22314 raw22314Labels = mixedMoment B raw22314step0 raw22314step0Labels := by
      have hz : ∀ j, raw22314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22314step0 = (fun i j => raw22314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22314step0 raw22314; decide +kernel
      have hl : raw22314step0Labels = raw22314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22314 raw22314Labels permutation346 hz
    mixedMoment B raw22314step0 raw22314step0Labels = mixedMoment B raw22314step1 raw22314step1Labels := by
      have hz : ∀ j, raw22314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22314step1 = (fun i j => raw22314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22314step1 raw22314step0; decide +kernel
      have hl : raw22314step1Labels = raw22314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22314step0 raw22314step0Labels permutation56 hz
    _ = mixedMoment B node616 node616Labels := by rfl

theorem canonical22315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22315 raw22315Labels = mixedMoment B node935 node935Labels := by
  calc
    mixedMoment B raw22315 raw22315Labels = mixedMoment B raw22315step0 raw22315step0Labels := by
      have hz : ∀ j, raw22315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22315step0 = (fun i j => raw22315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22315step0 raw22315; decide +kernel
      have hl : raw22315step0Labels = raw22315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22315 raw22315Labels permutation346 hz
    _ = mixedMoment B node935 node935Labels := by rfl

theorem canonical22316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22316 raw22316Labels = mixedMoment B node935 node935Labels := by
  calc
    mixedMoment B raw22316 raw22316Labels = mixedMoment B raw22316step0 raw22316step0Labels := by
      have hz : ∀ j, raw22316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22316step0 = (fun i j => raw22316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22316step0 raw22316; decide +kernel
      have hl : raw22316step0Labels = raw22316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22316 raw22316Labels permutation265 hz
    _ = mixedMoment B node935 node935Labels := by rfl

theorem canonical22317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22317 raw22317Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw22317 raw22317Labels = mixedMoment B raw22317step0 raw22317step0Labels := by
      have hz : ∀ j, raw22317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22317step0 = (fun i j => raw22317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22317step0 raw22317; decide +kernel
      have hl : raw22317step0Labels = raw22317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22317 raw22317Labels permutation346 hz
    mixedMoment B raw22317step0 raw22317step0Labels = mixedMoment B raw22317step1 raw22317step1Labels := by
      have hz : ∀ j, raw22317step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22317step1 = (fun i j => raw22317step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22317step1 raw22317step0; decide +kernel
      have hl : raw22317step1Labels = raw22317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22317step0 raw22317step0Labels permutation56 hz
    _ = mixedMoment B node1063 node1063Labels := by rfl

theorem canonical22318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22318 raw22318Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw22318 raw22318Labels = mixedMoment B raw22318step0 raw22318step0Labels := by
      have hz : ∀ j, raw22318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22318step0 = (fun i j => raw22318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22318step0 raw22318; decide +kernel
      have hl : raw22318step0Labels = raw22318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22318 raw22318Labels permutation346 hz
    mixedMoment B raw22318step0 raw22318step0Labels = mixedMoment B raw22318step1 raw22318step1Labels := by
      have hz : ∀ j, raw22318step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22318step1 = (fun i j => raw22318step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22318step1 raw22318step0; decide +kernel
      have hl : raw22318step1Labels = raw22318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22318step0 raw22318step0Labels permutation56 hz
    mixedMoment B raw22318step1 raw22318step1Labels = mixedMoment B raw22318step2 raw22318step2Labels := by
      have ha : raw22318step2 = (fun i j => raw22318step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22318step2 raw22318step1; decide +kernel
      have hl : raw22318step2Labels = raw22318step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22318step1 raw22318step1Labels permutation12 permutation2
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical22319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22319 raw22319Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw22319 raw22319Labels = mixedMoment B raw22319step0 raw22319step0Labels := by
      have hz : ∀ j, raw22319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22319step0 = (fun i j => raw22319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22319step0 raw22319; decide +kernel
      have hl : raw22319step0Labels = raw22319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22319 raw22319Labels permutation346 hz
    mixedMoment B raw22319step0 raw22319step0Labels = mixedMoment B raw22319step1 raw22319step1Labels := by
      have ha : raw22319step1 = (fun i j => raw22319step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22319step1 raw22319step0; decide +kernel
      have hl : raw22319step1Labels = raw22319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22319step0 raw22319step0Labels permutation39 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

theorem canonical22320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22320 raw22320Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw22320 raw22320Labels = mixedMoment B raw22320step0 raw22320step0Labels := by
      have hz : ∀ j, raw22320 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22320step0 = (fun i j => raw22320 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22320step0 raw22320; decide +kernel
      have hl : raw22320step0Labels = raw22320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22320 raw22320Labels permutation265 hz
    mixedMoment B raw22320step0 raw22320step0Labels = mixedMoment B raw22320step1 raw22320step1Labels := by
      have ha : raw22320step1 = (fun i j => raw22320step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22320step1 raw22320step0; decide +kernel
      have hl : raw22320step1Labels = raw22320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22320step0 raw22320step0Labels permutation39 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

theorem canonical22321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22321 raw22321Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw22321 raw22321Labels = mixedMoment B raw22321step0 raw22321step0Labels := by
      have hz : ∀ j, raw22321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22321step0 = (fun i j => raw22321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22321step0 raw22321; decide +kernel
      have hl : raw22321step0Labels = raw22321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22321 raw22321Labels permutation346 hz
    mixedMoment B raw22321step0 raw22321step0Labels = mixedMoment B raw22321step1 raw22321step1Labels := by
      have hz : ∀ j, raw22321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22321step1 = (fun i j => raw22321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22321step1 raw22321step0; decide +kernel
      have hl : raw22321step1Labels = raw22321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22321step0 raw22321step0Labels permutation56 hz
    mixedMoment B raw22321step1 raw22321step1Labels = mixedMoment B raw22321step2 raw22321step2Labels := by
      have ha : raw22321step2 = (fun i j => raw22321step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22321step2 raw22321step1; decide +kernel
      have hl : raw22321step2Labels = raw22321step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22321step1 raw22321step1Labels permutation9 permutation2
    _ = mixedMoment B node1324 node1324Labels := by rfl

theorem canonical22322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22322 raw22322Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw22322 raw22322Labels = mixedMoment B raw22322step0 raw22322step0Labels := by
      have hz : ∀ j, raw22322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22322step0 = (fun i j => raw22322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22322step0 raw22322; decide +kernel
      have hl : raw22322step0Labels = raw22322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22322 raw22322Labels permutation346 hz
    mixedMoment B raw22322step0 raw22322step0Labels = mixedMoment B raw22322step1 raw22322step1Labels := by
      have hz : ∀ j, raw22322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22322step1 = (fun i j => raw22322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22322step1 raw22322step0; decide +kernel
      have hl : raw22322step1Labels = raw22322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22322step0 raw22322step0Labels permutation56 hz
    _ = mixedMoment B node1325 node1325Labels := by rfl

theorem canonical22323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22323 raw22323Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22323 raw22323Labels = mixedMoment B raw22323step0 raw22323step0Labels := by
      have hz : ∀ j, raw22323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22323step0 = (fun i j => raw22323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22323step0 raw22323; decide +kernel
      have hl : raw22323step0Labels = raw22323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22323 raw22323Labels permutation346 hz
    mixedMoment B raw22323step0 raw22323step0Labels = mixedMoment B raw22323step1 raw22323step1Labels := by
      have hz : ∀ j, raw22323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22323step1 = (fun i j => raw22323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22323step1 raw22323step0; decide +kernel
      have hl : raw22323step1Labels = raw22323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22323step0 raw22323step0Labels permutation56 hz
    mixedMoment B raw22323step1 raw22323step1Labels = mixedMoment B raw22323step2 raw22323step2Labels := by
      have ha : raw22323step2 = (fun i j => raw22323step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22323step2 raw22323step1; decide +kernel
      have hl : raw22323step2Labels = raw22323step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22323step1 raw22323step1Labels permutation11 permutation4
    mixedMoment B raw22323step2 raw22323step2Labels = mixedMoment B raw22323step3 raw22323step3Labels := by
      have ha : raw22323step3 = -raw22323step2 := by apply Matrix.ext; change ∀ i j, raw22323step3 i j = -(raw22323step2 i j); unfold raw22323step3 raw22323step2; decide +kernel
      have hl : raw22323step3Labels = raw22323step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical22326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22326 raw22326Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22326 raw22326Labels = mixedMoment B raw22326step0 raw22326step0Labels := by
      have hz : ∀ j, raw22326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22326step0 = (fun i j => raw22326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22326step0 raw22326; decide +kernel
      have hl : raw22326step0Labels = raw22326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326 raw22326Labels permutation346 hz
    mixedMoment B raw22326step0 raw22326step0Labels = mixedMoment B raw22326step1 raw22326step1Labels := by
      have hz : ∀ j, raw22326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22326step1 = (fun i j => raw22326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22326step1 raw22326step0; decide +kernel
      have hl : raw22326step1Labels = raw22326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326step0 raw22326step0Labels permutation56 hz
    mixedMoment B raw22326step1 raw22326step1Labels = mixedMoment B raw22326step2 raw22326step2Labels := by
      have ha : raw22326step2 = (fun i j => raw22326step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22326step2 raw22326step1; decide +kernel
      have hl : raw22326step2Labels = raw22326step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22326step1 raw22326step1Labels permutation9 permutation2
    mixedMoment B raw22326step2 raw22326step2Labels = mixedMoment B raw22326step3 raw22326step3Labels := by
      have ha : raw22326step3 = -raw22326step2 := by apply Matrix.ext; change ∀ i j, raw22326step3 i j = -(raw22326step2 i j); unfold raw22326step3 raw22326step2; decide +kernel
      have hl : raw22326step3Labels = raw22326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical22330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22330 raw22330Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22330 raw22330Labels = mixedMoment B raw22330step0 raw22330step0Labels := by
      have hz : ∀ j, raw22330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22330step0 = (fun i j => raw22330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22330step0 raw22330; decide +kernel
      have hl : raw22330step0Labels = raw22330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22330 raw22330Labels permutation346 hz
    mixedMoment B raw22330step0 raw22330step0Labels = mixedMoment B raw22330step1 raw22330step1Labels := by
      have ha : raw22330step1 = (fun i j => raw22330step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22330step1 raw22330step0; decide +kernel
      have hl : raw22330step1Labels = raw22330step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22330step0 raw22330step0Labels permutation44 permutation4
    mixedMoment B raw22330step1 raw22330step1Labels = mixedMoment B raw22330step2 raw22330step2Labels := by
      have ha : raw22330step2 = -raw22330step1 := by apply Matrix.ext; change ∀ i j, raw22330step2 i j = -(raw22330step1 i j); unfold raw22330step2 raw22330step1; decide +kernel
      have hl : raw22330step2Labels = raw22330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical22331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22331 raw22331Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22331 raw22331Labels = mixedMoment B raw22331step0 raw22331step0Labels := by
      have hz : ∀ j, raw22331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22331step0 = (fun i j => raw22331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22331step0 raw22331; decide +kernel
      have hl : raw22331step0Labels = raw22331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22331 raw22331Labels permutation265 hz
    mixedMoment B raw22331step0 raw22331step0Labels = mixedMoment B raw22331step1 raw22331step1Labels := by
      have ha : raw22331step1 = (fun i j => raw22331step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22331step1 raw22331step0; decide +kernel
      have hl : raw22331step1Labels = raw22331step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22331step0 raw22331step0Labels permutation44 permutation4
    mixedMoment B raw22331step1 raw22331step1Labels = mixedMoment B raw22331step2 raw22331step2Labels := by
      have ha : raw22331step2 = -raw22331step1 := by apply Matrix.ext; change ∀ i j, raw22331step2 i j = -(raw22331step1 i j); unfold raw22331step2 raw22331step1; decide +kernel
      have hl : raw22331step2Labels = raw22331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical22332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22332 raw22332Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22332 raw22332Labels = mixedMoment B raw22332step0 raw22332step0Labels := by
      have hz : ∀ j, raw22332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22332step0 = (fun i j => raw22332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22332step0 raw22332; decide +kernel
      have hl : raw22332step0Labels = raw22332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332 raw22332Labels permutation346 hz
    mixedMoment B raw22332step0 raw22332step0Labels = mixedMoment B raw22332step1 raw22332step1Labels := by
      have hz : ∀ j, raw22332step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22332step1 = (fun i j => raw22332step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22332step1 raw22332step0; decide +kernel
      have hl : raw22332step1Labels = raw22332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332step0 raw22332step0Labels permutation56 hz
    mixedMoment B raw22332step1 raw22332step1Labels = mixedMoment B raw22332step2 raw22332step2Labels := by
      have ha : raw22332step2 = (fun i j => raw22332step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22332step2 raw22332step1; decide +kernel
      have hl : raw22332step2Labels = raw22332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22332step1 raw22332step1Labels permutation8 permutation4
    mixedMoment B raw22332step2 raw22332step2Labels = mixedMoment B raw22332step3 raw22332step3Labels := by
      have ha : raw22332step3 = -raw22332step2 := by apply Matrix.ext; change ∀ i j, raw22332step3 i j = -(raw22332step2 i j); unfold raw22332step3 raw22332step2; decide +kernel
      have hl : raw22332step3Labels = raw22332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22333 raw22333Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22333 raw22333Labels = mixedMoment B raw22333step0 raw22333step0Labels := by
      have hz : ∀ j, raw22333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22333step0 = (fun i j => raw22333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22333step0 raw22333; decide +kernel
      have hl : raw22333step0Labels = raw22333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22333 raw22333Labels permutation346 hz
    mixedMoment B raw22333step0 raw22333step0Labels = mixedMoment B raw22333step1 raw22333step1Labels := by
      have hz : ∀ j, raw22333step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22333step1 = (fun i j => raw22333step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22333step1 raw22333step0; decide +kernel
      have hl : raw22333step1Labels = raw22333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22333step0 raw22333step0Labels permutation56 hz
    mixedMoment B raw22333step1 raw22333step1Labels = mixedMoment B raw22333step2 raw22333step2Labels := by
      have ha : raw22333step2 = (fun i j => raw22333step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22333step2 raw22333step1; decide +kernel
      have hl : raw22333step2Labels = raw22333step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22333step1 raw22333step1Labels permutation10 permutation4
    mixedMoment B raw22333step2 raw22333step2Labels = mixedMoment B raw22333step3 raw22333step3Labels := by
      have ha : raw22333step3 = -raw22333step2 := by apply Matrix.ext; change ∀ i j, raw22333step3 i j = -(raw22333step2 i j); unfold raw22333step3 raw22333step2; decide +kernel
      have hl : raw22333step3Labels = raw22333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical22334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22334 raw22334Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw22334 raw22334Labels = mixedMoment B raw22334step0 raw22334step0Labels := by
      have hz : ∀ j, raw22334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22334step0 = (fun i j => raw22334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22334step0 raw22334; decide +kernel
      have hl : raw22334step0Labels = raw22334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22334 raw22334Labels permutation346 hz
    mixedMoment B raw22334step0 raw22334step0Labels = mixedMoment B raw22334step1 raw22334step1Labels := by
      have hz : ∀ j, raw22334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22334step1 = (fun i j => raw22334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22334step1 raw22334step0; decide +kernel
      have hl : raw22334step1Labels = raw22334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22334step0 raw22334step0Labels permutation56 hz
    mixedMoment B raw22334step1 raw22334step1Labels = mixedMoment B raw22334step2 raw22334step2Labels := by
      have ha : raw22334step2 = (fun i j => raw22334step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22334step2 raw22334step1; decide +kernel
      have hl : raw22334step2Labels = raw22334step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22334step1 raw22334step1Labels permutation11 permutation4
    mixedMoment B raw22334step2 raw22334step2Labels = mixedMoment B raw22334step3 raw22334step3Labels := by
      have ha : raw22334step3 = -raw22334step2 := by apply Matrix.ext; change ∀ i j, raw22334step3 i j = -(raw22334step2 i j); unfold raw22334step3 raw22334step2; decide +kernel
      have hl : raw22334step3Labels = raw22334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node858 node858Labels := by rfl

theorem canonical22335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22335 raw22335Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22335 raw22335Labels = mixedMoment B raw22335step0 raw22335step0Labels := by
      have hz : ∀ j, raw22335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22335step0 = (fun i j => raw22335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22335step0 raw22335; decide +kernel
      have hl : raw22335step0Labels = raw22335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22335 raw22335Labels permutation346 hz
    mixedMoment B raw22335step0 raw22335step0Labels = mixedMoment B raw22335step1 raw22335step1Labels := by
      have ha : raw22335step1 = (fun i j => raw22335step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22335step1 raw22335step0; decide +kernel
      have hl : raw22335step1Labels = raw22335step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22335step0 raw22335step0Labels permutation35 permutation4
    mixedMoment B raw22335step1 raw22335step1Labels = mixedMoment B raw22335step2 raw22335step2Labels := by
      have ha : raw22335step2 = -raw22335step1 := by apply Matrix.ext; change ∀ i j, raw22335step2 i j = -(raw22335step1 i j); unfold raw22335step2 raw22335step1; decide +kernel
      have hl : raw22335step2Labels = raw22335step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

theorem canonical22336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22336 raw22336Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22336 raw22336Labels = mixedMoment B raw22336step0 raw22336step0Labels := by
      have hz : ∀ j, raw22336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22336step0 = (fun i j => raw22336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22336step0 raw22336; decide +kernel
      have hl : raw22336step0Labels = raw22336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22336 raw22336Labels permutation265 hz
    mixedMoment B raw22336step0 raw22336step0Labels = mixedMoment B raw22336step1 raw22336step1Labels := by
      have ha : raw22336step1 = (fun i j => raw22336step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22336step1 raw22336step0; decide +kernel
      have hl : raw22336step1Labels = raw22336step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22336step0 raw22336step0Labels permutation35 permutation4
    mixedMoment B raw22336step1 raw22336step1Labels = mixedMoment B raw22336step2 raw22336step2Labels := by
      have ha : raw22336step2 = -raw22336step1 := by apply Matrix.ext; change ∀ i j, raw22336step2 i j = -(raw22336step1 i j); unfold raw22336step2 raw22336step1; decide +kernel
      have hl : raw22336step2Labels = raw22336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

theorem canonical22337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22337 raw22337Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22337 raw22337Labels = mixedMoment B raw22337step0 raw22337step0Labels := by
      have hz : ∀ j, raw22337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22337step0 = (fun i j => raw22337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22337step0 raw22337; decide +kernel
      have hl : raw22337step0Labels = raw22337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22337 raw22337Labels permutation346 hz
    mixedMoment B raw22337step0 raw22337step0Labels = mixedMoment B raw22337step1 raw22337step1Labels := by
      have hz : ∀ j, raw22337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22337step1 = (fun i j => raw22337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22337step1 raw22337step0; decide +kernel
      have hl : raw22337step1Labels = raw22337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22337step0 raw22337step0Labels permutation56 hz
    mixedMoment B raw22337step1 raw22337step1Labels = mixedMoment B raw22337step2 raw22337step2Labels := by
      have ha : raw22337step2 = (fun i j => raw22337step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22337step2 raw22337step1; decide +kernel
      have hl : raw22337step2Labels = raw22337step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22337step1 raw22337step1Labels permutation13 permutation4
    mixedMoment B raw22337step2 raw22337step2Labels = mixedMoment B raw22337step3 raw22337step3Labels := by
      have ha : raw22337step3 = -raw22337step2 := by apply Matrix.ext; change ∀ i j, raw22337step3 i j = -(raw22337step2 i j); unfold raw22337step3 raw22337step2; decide +kernel
      have hl : raw22337step3Labels = raw22337step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical22338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22338 raw22338Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22338 raw22338Labels = mixedMoment B raw22338step0 raw22338step0Labels := by
      have hz : ∀ j, raw22338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22338step0 = (fun i j => raw22338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22338step0 raw22338; decide +kernel
      have hl : raw22338step0Labels = raw22338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22338 raw22338Labels permutation346 hz
    mixedMoment B raw22338step0 raw22338step0Labels = mixedMoment B raw22338step1 raw22338step1Labels := by
      have hz : ∀ j, raw22338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22338step1 = (fun i j => raw22338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22338step1 raw22338step0; decide +kernel
      have hl : raw22338step1Labels = raw22338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22338step0 raw22338step0Labels permutation56 hz
    mixedMoment B raw22338step1 raw22338step1Labels = mixedMoment B raw22338step2 raw22338step2Labels := by
      have ha : raw22338step2 = (fun i j => raw22338step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22338step2 raw22338step1; decide +kernel
      have hl : raw22338step2Labels = raw22338step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22338step1 raw22338step1Labels permutation10 permutation4
    mixedMoment B raw22338step2 raw22338step2Labels = mixedMoment B raw22338step3 raw22338step3Labels := by
      have ha : raw22338step3 = -raw22338step2 := by apply Matrix.ext; change ∀ i j, raw22338step3 i j = -(raw22338step2 i j); unfold raw22338step3 raw22338step2; decide +kernel
      have hl : raw22338step3Labels = raw22338step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical22339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22339 raw22339Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22339 raw22339Labels = mixedMoment B raw22339step0 raw22339step0Labels := by
      have hz : ∀ j, raw22339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22339step0 = (fun i j => raw22339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22339step0 raw22339; decide +kernel
      have hl : raw22339step0Labels = raw22339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22339 raw22339Labels permutation346 hz
    mixedMoment B raw22339step0 raw22339step0Labels = mixedMoment B raw22339step1 raw22339step1Labels := by
      have ha : raw22339step1 = (fun i j => raw22339step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22339step1 raw22339step0; decide +kernel
      have hl : raw22339step1Labels = raw22339step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22339step0 raw22339step0Labels permutation34 permutation4
    mixedMoment B raw22339step1 raw22339step1Labels = mixedMoment B raw22339step2 raw22339step2Labels := by
      have ha : raw22339step2 = -raw22339step1 := by apply Matrix.ext; change ∀ i j, raw22339step2 i j = -(raw22339step1 i j); unfold raw22339step2 raw22339step1; decide +kernel
      have hl : raw22339step2Labels = raw22339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

theorem canonical22340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22340 raw22340Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22340 raw22340Labels = mixedMoment B raw22340step0 raw22340step0Labels := by
      have hz : ∀ j, raw22340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22340step0 = (fun i j => raw22340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22340step0 raw22340; decide +kernel
      have hl : raw22340step0Labels = raw22340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22340 raw22340Labels permutation265 hz
    mixedMoment B raw22340step0 raw22340step0Labels = mixedMoment B raw22340step1 raw22340step1Labels := by
      have ha : raw22340step1 = (fun i j => raw22340step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22340step1 raw22340step0; decide +kernel
      have hl : raw22340step1Labels = raw22340step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22340step0 raw22340step0Labels permutation34 permutation4
    mixedMoment B raw22340step1 raw22340step1Labels = mixedMoment B raw22340step2 raw22340step2Labels := by
      have ha : raw22340step2 = -raw22340step1 := by apply Matrix.ext; change ∀ i j, raw22340step2 i j = -(raw22340step1 i j); unfold raw22340step2 raw22340step1; decide +kernel
      have hl : raw22340step2Labels = raw22340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

theorem canonical22341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22341 raw22341Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw22341 raw22341Labels = mixedMoment B raw22341step0 raw22341step0Labels := by
      have hz : ∀ j, raw22341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22341step0 = (fun i j => raw22341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22341step0 raw22341; decide +kernel
      have hl : raw22341step0Labels = raw22341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22341 raw22341Labels permutation346 hz
    mixedMoment B raw22341step0 raw22341step0Labels = mixedMoment B raw22341step1 raw22341step1Labels := by
      have hz : ∀ j, raw22341step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22341step1 = (fun i j => raw22341step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22341step1 raw22341step0; decide +kernel
      have hl : raw22341step1Labels = raw22341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22341step0 raw22341step0Labels permutation56 hz
    mixedMoment B raw22341step1 raw22341step1Labels = mixedMoment B raw22341step2 raw22341step2Labels := by
      have ha : raw22341step2 = (fun i j => raw22341step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22341step2 raw22341step1; decide +kernel
      have hl : raw22341step2Labels = raw22341step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22341step1 raw22341step1Labels permutation10 permutation4
    mixedMoment B raw22341step2 raw22341step2Labels = mixedMoment B raw22341step3 raw22341step3Labels := by
      have ha : raw22341step3 = -raw22341step2 := by apply Matrix.ext; change ∀ i j, raw22341step3 i j = -(raw22341step2 i j); unfold raw22341step3 raw22341step2; decide +kernel
      have hl : raw22341step3Labels = raw22341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1660 node1660Labels := by rfl

theorem canonical22352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22352 raw22352Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw22352 raw22352Labels = mixedMoment B raw22352step0 raw22352step0Labels := by
      have hz : ∀ j, raw22352 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22352step0 = (fun i j => raw22352 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22352step0 raw22352; decide +kernel
      have hl : raw22352step0Labels = raw22352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22352 raw22352Labels permutation265 hz
    mixedMoment B raw22352step0 raw22352step0Labels = mixedMoment B raw22352step1 raw22352step1Labels := by
      have ha : raw22352step1 = (fun i j => raw22352step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22352step1 raw22352step0; decide +kernel
      have hl : raw22352step1Labels = raw22352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22352step0 raw22352step0Labels permutation38 permutation2
    _ = mixedMoment B node586 node586Labels := by rfl

theorem canonical22353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22353 raw22353Labels = mixedMoment B node910 node910Labels := by
  calc
    mixedMoment B raw22353 raw22353Labels = mixedMoment B raw22353step0 raw22353step0Labels := by
      have ha : raw22353step0 = (fun i j => raw22353 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22353step0 raw22353; decide +kernel
      have hl : raw22353step0Labels = raw22353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22353 raw22353Labels permutation158 permutation2
    _ = mixedMoment B node910 node910Labels := by rfl

theorem canonical22354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22354 raw22354Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw22354 raw22354Labels = mixedMoment B raw22354step0 raw22354step0Labels := by
      have hz : ∀ j, raw22354 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22354step0 = (fun i j => raw22354 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22354step0 raw22354; decide +kernel
      have hl : raw22354step0Labels = raw22354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22354 raw22354Labels permutation265 hz
    _ = mixedMoment B node1026 node1026Labels := by rfl

theorem canonical22355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22355 raw22355Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw22355 raw22355Labels = mixedMoment B raw22355step0 raw22355step0Labels := by
      have hz : ∀ j, raw22355 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22355step0 = (fun i j => raw22355 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22355step0 raw22355; decide +kernel
      have hl : raw22355step0Labels = raw22355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22355 raw22355Labels permutation265 hz
    mixedMoment B raw22355step0 raw22355step0Labels = mixedMoment B raw22355step1 raw22355step1Labels := by
      have ha : raw22355step1 = (fun i j => raw22355step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22355step1 raw22355step0; decide +kernel
      have hl : raw22355step1Labels = raw22355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22355step0 raw22355step0Labels permutation38 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

theorem canonical22356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22356 raw22356Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw22356 raw22356Labels = mixedMoment B raw22356step0 raw22356step0Labels := by
      have hz : ∀ j, raw22356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22356step0 = (fun i j => raw22356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22356step0 raw22356; decide +kernel
      have hl : raw22356step0Labels = raw22356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22356 raw22356Labels permutation265 hz
    mixedMoment B raw22356step0 raw22356step0Labels = mixedMoment B raw22356step1 raw22356step1Labels := by
      have ha : raw22356step1 = (fun i j => raw22356step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22356step1 raw22356step0; decide +kernel
      have hl : raw22356step1Labels = raw22356step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22356step0 raw22356step0Labels permutation39 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical22357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22357 raw22357Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw22357 raw22357Labels = mixedMoment B raw22357step0 raw22357step0Labels := by
      have ha : raw22357step0 = (fun i j => raw22357 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22357step0 raw22357; decide +kernel
      have hl : raw22357step0Labels = raw22357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22357 raw22357Labels permutation183 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

theorem canonical22358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22358 raw22358Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw22358 raw22358Labels = mixedMoment B raw22358step0 raw22358step0Labels := by
      have hz : ∀ j, raw22358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22358step0 = (fun i j => raw22358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22358step0 raw22358; decide +kernel
      have hl : raw22358step0Labels = raw22358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22358 raw22358Labels permutation265 hz
    mixedMoment B raw22358step0 raw22358step0Labels = mixedMoment B raw22358step1 raw22358step1Labels := by
      have ha : raw22358step1 = (fun i j => raw22358step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22358step1 raw22358step0; decide +kernel
      have hl : raw22358step1Labels = raw22358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22358step0 raw22358step0Labels permutation33 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

theorem canonical22359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22359 raw22359Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw22359 raw22359Labels = mixedMoment B raw22359step0 raw22359step0Labels := by
      have hz : ∀ j, raw22359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22359step0 = (fun i j => raw22359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22359step0 raw22359; decide +kernel
      have hl : raw22359step0Labels = raw22359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22359 raw22359Labels permutation265 hz
    mixedMoment B raw22359step0 raw22359step0Labels = mixedMoment B raw22359step1 raw22359step1Labels := by
      have ha : raw22359step1 = (fun i j => raw22359step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22359step1 raw22359step0; decide +kernel
      have hl : raw22359step1Labels = raw22359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22359step0 raw22359step0Labels permutation33 permutation2
    _ = mixedMoment B node1333 node1333Labels := by rfl

theorem canonical22360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22360 raw22360Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw22360 raw22360Labels = mixedMoment B raw22360step0 raw22360step0Labels := by
      have hz : ∀ j, raw22360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22360step0 = (fun i j => raw22360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22360step0 raw22360; decide +kernel
      have hl : raw22360step0Labels = raw22360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22360 raw22360Labels permutation265 hz
    _ = mixedMoment B node1334 node1334Labels := by rfl

theorem canonical22361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22361 raw22361Labels = mixedMoment B node3280 node3280Labels := by
  calc
    mixedMoment B raw22361 raw22361Labels = mixedMoment B raw22361step0 raw22361step0Labels := by
      have ha : raw22361step0 = (fun i j => raw22361 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22361step0 raw22361; decide +kernel
      have hl : raw22361step0Labels = raw22361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22361 raw22361Labels permutation183 permutation2
    mixedMoment B raw22361step0 raw22361step0Labels = mixedMoment B raw22361step1 raw22361step1Labels := by
      have ha : raw22361step1 = -raw22361step0 := by apply Matrix.ext; change ∀ i j, raw22361step1 i j = -(raw22361step0 i j); unfold raw22361step1 raw22361step0; decide +kernel
      have hl : raw22361step1Labels = raw22361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3280 node3280Labels := by rfl

theorem canonical22362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22362 raw22362Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22362 raw22362Labels = mixedMoment B raw22362step0 raw22362step0Labels := by
      have hz : ∀ j, raw22362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22362step0 = (fun i j => raw22362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22362step0 raw22362; decide +kernel
      have hl : raw22362step0Labels = raw22362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22362 raw22362Labels permutation434 hz
    mixedMoment B raw22362step0 raw22362step0Labels = mixedMoment B raw22362step1 raw22362step1Labels := by
      have hz : ∀ j, raw22362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22362step1 = (fun i j => raw22362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22362step1 raw22362step0; decide +kernel
      have hl : raw22362step1Labels = raw22362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22362step0 raw22362step0Labels permutation56 hz
    mixedMoment B raw22362step1 raw22362step1Labels = mixedMoment B raw22362step2 raw22362step2Labels := by
      have ha : raw22362step2 = (fun i j => raw22362step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22362step2 raw22362step1; decide +kernel
      have hl : raw22362step2Labels = raw22362step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22362step1 raw22362step1Labels permutation9 permutation2
    mixedMoment B raw22362step2 raw22362step2Labels = mixedMoment B raw22362step3 raw22362step3Labels := by
      have ha : raw22362step3 = -raw22362step2 := by apply Matrix.ext; change ∀ i j, raw22362step3 i j = -(raw22362step2 i j); unfold raw22362step3 raw22362step2; decide +kernel
      have hl : raw22362step3Labels = raw22362step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22363 raw22363Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22363 raw22363Labels = mixedMoment B raw22363step0 raw22363step0Labels := by
      have hz : ∀ j, raw22363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22363step0 = (fun i j => raw22363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22363step0 raw22363; decide +kernel
      have hl : raw22363step0Labels = raw22363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22363 raw22363Labels permutation265 hz
    mixedMoment B raw22363step0 raw22363step0Labels = mixedMoment B raw22363step1 raw22363step1Labels := by
      have ha : raw22363step1 = (fun i j => raw22363step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22363step1 raw22363step0; decide +kernel
      have hl : raw22363step1Labels = raw22363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22363step0 raw22363step0Labels permutation125 permutation2
    _ = mixedMoment B node2397 node2397Labels := by rfl

theorem canonical22364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22364 raw22364Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw22364 raw22364Labels = mixedMoment B raw22364step0 raw22364step0Labels := by
      have hz : ∀ j, raw22364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22364step0 = (fun i j => raw22364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22364step0 raw22364; decide +kernel
      have hl : raw22364step0Labels = raw22364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22364 raw22364Labels permutation265 hz
    mixedMoment B raw22364step0 raw22364step0Labels = mixedMoment B raw22364step1 raw22364step1Labels := by
      have ha : raw22364step1 = -raw22364step0 := by apply Matrix.ext; change ∀ i j, raw22364step1 i j = -(raw22364step0 i j); unfold raw22364step1 raw22364step0; decide +kernel
      have hl : raw22364step1Labels = raw22364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3284 node3284Labels := by rfl

theorem canonical22368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22368 raw22368Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw22368 raw22368Labels = mixedMoment B raw22368step0 raw22368step0Labels := by
      have hz : ∀ j, raw22368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22368step0 = (fun i j => raw22368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22368step0 raw22368; decide +kernel
      have hl : raw22368step0Labels = raw22368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22368 raw22368Labels permutation265 hz
    mixedMoment B raw22368step0 raw22368step0Labels = mixedMoment B raw22368step1 raw22368step1Labels := by
      have ha : raw22368step1 = (fun i j => raw22368step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22368step1 raw22368step0; decide +kernel
      have hl : raw22368step1Labels = raw22368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22368step0 raw22368step0Labels permutation32 permutation4
    mixedMoment B raw22368step1 raw22368step1Labels = mixedMoment B raw22368step2 raw22368step2Labels := by
      have ha : raw22368step2 = -raw22368step1 := by apply Matrix.ext; change ∀ i j, raw22368step2 i j = -(raw22368step1 i j); unfold raw22368step2 raw22368step1; decide +kernel
      have hl : raw22368step2Labels = raw22368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical22369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22369 raw22369Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22369 raw22369Labels = mixedMoment B raw22369step0 raw22369step0Labels := by
      have hz : ∀ j, raw22369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22369step0 = (fun i j => raw22369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22369step0 raw22369; decide +kernel
      have hl : raw22369step0Labels = raw22369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22369 raw22369Labels permutation265 hz
    mixedMoment B raw22369step0 raw22369step0Labels = mixedMoment B raw22369step1 raw22369step1Labels := by
      have ha : raw22369step1 = (fun i j => raw22369step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22369step1 raw22369step0; decide +kernel
      have hl : raw22369step1Labels = raw22369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22369step0 raw22369step0Labels permutation44 permutation4
    mixedMoment B raw22369step1 raw22369step1Labels = mixedMoment B raw22369step2 raw22369step2Labels := by
      have ha : raw22369step2 = -raw22369step1 := by apply Matrix.ext; change ∀ i j, raw22369step2 i j = -(raw22369step1 i j); unfold raw22369step2 raw22369step1; decide +kernel
      have hl : raw22369step2Labels = raw22369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical22370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22370 raw22370Labels = mixedMoment B node1614 node1614Labels := by
  calc
    mixedMoment B raw22370 raw22370Labels = mixedMoment B raw22370step0 raw22370step0Labels := by
      have ha : raw22370step0 = (fun i j => raw22370 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22370step0 raw22370; decide +kernel
      have hl : raw22370step0Labels = raw22370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22370 raw22370Labels permutation152 permutation4
    mixedMoment B raw22370step0 raw22370step0Labels = mixedMoment B raw22370step1 raw22370step1Labels := by
      have ha : raw22370step1 = -raw22370step0 := by apply Matrix.ext; change ∀ i j, raw22370step1 i j = -(raw22370step0 i j); unfold raw22370step1 raw22370step0; decide +kernel
      have hl : raw22370step1Labels = raw22370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1614 node1614Labels := by rfl

theorem canonical22371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22371 raw22371Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22371 raw22371Labels = mixedMoment B raw22371step0 raw22371step0Labels := by
      have hz : ∀ j, raw22371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22371step0 = (fun i j => raw22371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22371step0 raw22371; decide +kernel
      have hl : raw22371step0Labels = raw22371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22371 raw22371Labels permutation434 hz
    mixedMoment B raw22371step0 raw22371step0Labels = mixedMoment B raw22371step1 raw22371step1Labels := by
      have hz : ∀ j, raw22371step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22371step1 = (fun i j => raw22371step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22371step1 raw22371step0; decide +kernel
      have hl : raw22371step1Labels = raw22371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22371step0 raw22371step0Labels permutation56 hz
    mixedMoment B raw22371step1 raw22371step1Labels = mixedMoment B raw22371step2 raw22371step2Labels := by
      have ha : raw22371step2 = (fun i j => raw22371step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22371step2 raw22371step1; decide +kernel
      have hl : raw22371step2Labels = raw22371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22371step1 raw22371step1Labels permutation8 permutation4
    mixedMoment B raw22371step2 raw22371step2Labels = mixedMoment B raw22371step3 raw22371step3Labels := by
      have ha : raw22371step3 = -raw22371step2 := by apply Matrix.ext; change ∀ i j, raw22371step3 i j = -(raw22371step2 i j); unfold raw22371step3 raw22371step2; decide +kernel
      have hl : raw22371step3Labels = raw22371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22372 raw22372Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22372 raw22372Labels = mixedMoment B raw22372step0 raw22372step0Labels := by
      have hz : ∀ j, raw22372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22372step0 = (fun i j => raw22372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22372step0 raw22372; decide +kernel
      have hl : raw22372step0Labels = raw22372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22372 raw22372Labels permutation265 hz
    mixedMoment B raw22372step0 raw22372step0Labels = mixedMoment B raw22372step1 raw22372step1Labels := by
      have ha : raw22372step1 = (fun i j => raw22372step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22372step1 raw22372step0; decide +kernel
      have hl : raw22372step1Labels = raw22372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22372step0 raw22372step0Labels permutation50 permutation4
    mixedMoment B raw22372step1 raw22372step1Labels = mixedMoment B raw22372step2 raw22372step2Labels := by
      have ha : raw22372step2 = -raw22372step1 := by apply Matrix.ext; change ∀ i j, raw22372step2 i j = -(raw22372step1 i j); unfold raw22372step2 raw22372step1; decide +kernel
      have hl : raw22372step2Labels = raw22372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical22373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22373 raw22373Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw22373 raw22373Labels = mixedMoment B raw22373step0 raw22373step0Labels := by
      have ha : raw22373step0 = (fun i j => raw22373 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22373step0 raw22373; decide +kernel
      have hl : raw22373step0Labels = raw22373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22373 raw22373Labels permutation164 permutation4
    mixedMoment B raw22373step0 raw22373step0Labels = mixedMoment B raw22373step1 raw22373step1Labels := by
      have ha : raw22373step1 = -raw22373step0 := by apply Matrix.ext; change ∀ i j, raw22373step1 i j = -(raw22373step0 i j); unfold raw22373step1 raw22373step0; decide +kernel
      have hl : raw22373step1Labels = raw22373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1606 node1606Labels := by rfl

theorem canonical22374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22374 raw22374Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22374 raw22374Labels = mixedMoment B raw22374step0 raw22374step0Labels := by
      have hz : ∀ j, raw22374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22374step0 = (fun i j => raw22374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22374step0 raw22374; decide +kernel
      have hl : raw22374step0Labels = raw22374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22374 raw22374Labels permutation434 hz
    mixedMoment B raw22374step0 raw22374step0Labels = mixedMoment B raw22374step1 raw22374step1Labels := by
      have hz : ∀ j, raw22374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22374step1 = (fun i j => raw22374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22374step1 raw22374step0; decide +kernel
      have hl : raw22374step1Labels = raw22374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22374step0 raw22374step0Labels permutation56 hz
    mixedMoment B raw22374step1 raw22374step1Labels = mixedMoment B raw22374step2 raw22374step2Labels := by
      have ha : raw22374step2 = (fun i j => raw22374step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22374step2 raw22374step1; decide +kernel
      have hl : raw22374step2Labels = raw22374step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22374step1 raw22374step1Labels permutation10 permutation4
    mixedMoment B raw22374step2 raw22374step2Labels = mixedMoment B raw22374step3 raw22374step3Labels := by
      have ha : raw22374step3 = -raw22374step2 := by apply Matrix.ext; change ∀ i j, raw22374step3 i j = -(raw22374step2 i j); unfold raw22374step3 raw22374step2; decide +kernel
      have hl : raw22374step3Labels = raw22374step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical22375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22375 raw22375Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22375 raw22375Labels = mixedMoment B raw22375step0 raw22375step0Labels := by
      have hz : ∀ j, raw22375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22375step0 = (fun i j => raw22375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22375step0 raw22375; decide +kernel
      have hl : raw22375step0Labels = raw22375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22375 raw22375Labels permutation265 hz
    mixedMoment B raw22375step0 raw22375step0Labels = mixedMoment B raw22375step1 raw22375step1Labels := by
      have ha : raw22375step1 = (fun i j => raw22375step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22375step1 raw22375step0; decide +kernel
      have hl : raw22375step1Labels = raw22375step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22375step0 raw22375step0Labels permutation44 permutation4
    mixedMoment B raw22375step1 raw22375step1Labels = mixedMoment B raw22375step2 raw22375step2Labels := by
      have ha : raw22375step2 = -raw22375step1 := by apply Matrix.ext; change ∀ i j, raw22375step2 i j = -(raw22375step1 i j); unfold raw22375step2 raw22375step1; decide +kernel
      have hl : raw22375step2Labels = raw22375step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

theorem canonical22378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22378 raw22378Labels = mixedMoment B node1356 node1356Labels := by
  calc
    mixedMoment B raw22378 raw22378Labels = mixedMoment B raw22378step0 raw22378step0Labels := by
      have hz : ∀ j, raw22378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22378step0 = (fun i j => raw22378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22378step0 raw22378; decide +kernel
      have hl : raw22378step0Labels = raw22378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22378 raw22378Labels permutation265 hz
    mixedMoment B raw22378step0 raw22378step0Labels = mixedMoment B raw22378step1 raw22378step1Labels := by
      have ha : raw22378step1 = (fun i j => raw22378step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22378step1 raw22378step0; decide +kernel
      have hl : raw22378step1Labels = raw22378step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22378step0 raw22378step0Labels permutation38 permutation2
    _ = mixedMoment B node1356 node1356Labels := by rfl

theorem canonical22379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22379 raw22379Labels = mixedMoment B node2970 node2970Labels := by
  calc
    mixedMoment B raw22379 raw22379Labels = mixedMoment B raw22379step0 raw22379step0Labels := by
      have ha : raw22379step0 = (fun i j => raw22379 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22379step0 raw22379; decide +kernel
      have hl : raw22379step0Labels = raw22379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22379 raw22379Labels permutation158 permutation2
    _ = mixedMoment B node2970 node2970Labels := by rfl

theorem canonical22380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22380 raw22380Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw22380 raw22380Labels = mixedMoment B raw22380step0 raw22380step0Labels := by
      have hz : ∀ j, raw22380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22380step0 = (fun i j => raw22380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22380step0 raw22380; decide +kernel
      have hl : raw22380step0Labels = raw22380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22380 raw22380Labels permutation265 hz
    _ = mixedMoment B node2911 node2911Labels := by rfl

theorem canonical22381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22381 raw22381Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw22381 raw22381Labels = mixedMoment B raw22381step0 raw22381step0Labels := by
      have hz : ∀ j, raw22381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22381step0 = (fun i j => raw22381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22381step0 raw22381; decide +kernel
      have hl : raw22381step0Labels = raw22381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22381 raw22381Labels permutation265 hz
    mixedMoment B raw22381step0 raw22381step0Labels = mixedMoment B raw22381step1 raw22381step1Labels := by
      have ha : raw22381step1 = (fun i j => raw22381step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22381step1 raw22381step0; decide +kernel
      have hl : raw22381step1Labels = raw22381step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22381step0 raw22381step0Labels permutation38 permutation2
    _ = mixedMoment B node2856 node2856Labels := by rfl

theorem canonical22382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22382 raw22382Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw22382 raw22382Labels = mixedMoment B raw22382step0 raw22382step0Labels := by
      have hz : ∀ j, raw22382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22382step0 = (fun i j => raw22382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22382step0 raw22382; decide +kernel
      have hl : raw22382step0Labels = raw22382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22382 raw22382Labels permutation265 hz
    mixedMoment B raw22382step0 raw22382step0Labels = mixedMoment B raw22382step1 raw22382step1Labels := by
      have ha : raw22382step1 = (fun i j => raw22382step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22382step1 raw22382step0; decide +kernel
      have hl : raw22382step1Labels = raw22382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22382step0 raw22382step0Labels permutation38 permutation2
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical22383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22383 raw22383Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw22383 raw22383Labels = mixedMoment B raw22383step0 raw22383step0Labels := by
      have hz : ∀ j, raw22383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22383step0 = (fun i j => raw22383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22383step0 raw22383; decide +kernel
      have hl : raw22383step0Labels = raw22383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22383 raw22383Labels permutation265 hz
    mixedMoment B raw22383step0 raw22383step0Labels = mixedMoment B raw22383step1 raw22383step1Labels := by
      have ha : raw22383step1 = (fun i j => raw22383step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22383step1 raw22383step0; decide +kernel
      have hl : raw22383step1Labels = raw22383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22383step0 raw22383step0Labels permutation39 permutation2
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical22384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22384 raw22384Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw22384 raw22384Labels = mixedMoment B raw22384step0 raw22384step0Labels := by
      have hz : ∀ j, raw22384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22384step0 = (fun i j => raw22384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22384step0 raw22384; decide +kernel
      have hl : raw22384step0Labels = raw22384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22384 raw22384Labels permutation265 hz
    mixedMoment B raw22384step0 raw22384step0Labels = mixedMoment B raw22384step1 raw22384step1Labels := by
      have ha : raw22384step1 = (fun i j => raw22384step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22384step1 raw22384step0; decide +kernel
      have hl : raw22384step1Labels = raw22384step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22384step0 raw22384step0Labels permutation122 permutation0
    mixedMoment B raw22384step1 raw22384step1Labels = mixedMoment B raw22384step2 raw22384step2Labels := by
      have ha : raw22384step2 = -raw22384step1 := by apply Matrix.ext; change ∀ i j, raw22384step2 i j = -(raw22384step1 i j); unfold raw22384step2 raw22384step1; decide +kernel
      have hl : raw22384step2Labels = raw22384step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical22392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22392 raw22392Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw22392 raw22392Labels = mixedMoment B raw22392step0 raw22392step0Labels := by
      have hz : ∀ j, raw22392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22392step0 = (fun i j => raw22392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22392step0 raw22392; decide +kernel
      have hl : raw22392step0Labels = raw22392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22392 raw22392Labels permutation434 hz
    mixedMoment B raw22392step0 raw22392step0Labels = mixedMoment B raw22392step1 raw22392step1Labels := by
      have hz : ∀ j, raw22392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22392step1 = (fun i j => raw22392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22392step1 raw22392step0; decide +kernel
      have hl : raw22392step1Labels = raw22392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22392step0 raw22392step0Labels permutation80 hz
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical22393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22393 raw22393Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22393 raw22393Labels = mixedMoment B raw22393step0 raw22393step0Labels := by
      have hz : ∀ j, raw22393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22393step0 = (fun i j => raw22393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22393step0 raw22393; decide +kernel
      have hl : raw22393step0Labels = raw22393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22393 raw22393Labels permutation434 hz
    mixedMoment B raw22393step0 raw22393step0Labels = mixedMoment B raw22393step1 raw22393step1Labels := by
      have hz : ∀ j, raw22393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22393step1 = (fun i j => raw22393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22393step1 raw22393step0; decide +kernel
      have hl : raw22393step1Labels = raw22393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22393step0 raw22393step0Labels permutation80 hz
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical22394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22394 raw22394Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw22394 raw22394Labels = mixedMoment B raw22394step0 raw22394step0Labels := by
      have hz : ∀ j, raw22394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22394step0 = (fun i j => raw22394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22394step0 raw22394; decide +kernel
      have hl : raw22394step0Labels = raw22394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22394 raw22394Labels permutation434 hz
    _ = mixedMoment B node1133 node1133Labels := by rfl

theorem canonical22395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22395 raw22395Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw22395 raw22395Labels = mixedMoment B raw22395step0 raw22395step0Labels := by
      have hz : ∀ j, raw22395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22395step0 = (fun i j => raw22395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22395step0 raw22395; decide +kernel
      have hl : raw22395step0Labels = raw22395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22395 raw22395Labels permutation346 hz
    _ = mixedMoment B node1133 node1133Labels := by rfl

theorem canonical22396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22396 raw22396Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw22396 raw22396Labels = mixedMoment B raw22396step0 raw22396step0Labels := by
      have hz : ∀ j, raw22396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22396step0 = (fun i j => raw22396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22396step0 raw22396; decide +kernel
      have hl : raw22396step0Labels = raw22396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22396 raw22396Labels permutation434 hz
    mixedMoment B raw22396step0 raw22396step0Labels = mixedMoment B raw22396step1 raw22396step1Labels := by
      have hz : ∀ j, raw22396step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22396step1 = (fun i j => raw22396step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22396step1 raw22396step0; decide +kernel
      have hl : raw22396step1Labels = raw22396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22396step0 raw22396step0Labels permutation80 hz
    mixedMoment B raw22396step1 raw22396step1Labels = mixedMoment B raw22396step2 raw22396step2Labels := by
      have ha : raw22396step2 = (fun i j => raw22396step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22396step2 raw22396step1; decide +kernel
      have hl : raw22396step2Labels = raw22396step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22396step1 raw22396step1Labels permutation9 permutation2
    _ = mixedMoment B node1146 node1146Labels := by rfl

theorem canonical22397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22397 raw22397Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw22397 raw22397Labels = mixedMoment B raw22397step0 raw22397step0Labels := by
      have hz : ∀ j, raw22397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22397step0 = (fun i j => raw22397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22397step0 raw22397; decide +kernel
      have hl : raw22397step0Labels = raw22397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22397 raw22397Labels permutation434 hz
    mixedMoment B raw22397step0 raw22397step0Labels = mixedMoment B raw22397step1 raw22397step1Labels := by
      have hz : ∀ j, raw22397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22397step1 = (fun i j => raw22397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22397step1 raw22397step0; decide +kernel
      have hl : raw22397step1Labels = raw22397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22397step0 raw22397step0Labels permutation80 hz
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical22398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22398 raw22398Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw22398 raw22398Labels = mixedMoment B raw22398step0 raw22398step0Labels := by
      have hz : ∀ j, raw22398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22398step0 = (fun i j => raw22398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22398step0 raw22398; decide +kernel
      have hl : raw22398step0Labels = raw22398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398 raw22398Labels permutation520 hz
    mixedMoment B raw22398step0 raw22398step0Labels = mixedMoment B raw22398step1 raw22398step1Labels := by
      have hz : ∀ j, raw22398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22398step1 = (fun i j => raw22398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22398step1 raw22398step0; decide +kernel
      have hl : raw22398step1Labels = raw22398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step0 raw22398step0Labels permutation104 hz
    mixedMoment B raw22398step1 raw22398step1Labels = mixedMoment B raw22398step2 raw22398step2Labels := by
      have hz : ∀ j, raw22398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22398step2 = (fun i j => raw22398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22398step2 raw22398step1; decide +kernel
      have hl : raw22398step2Labels = raw22398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step1 raw22398step1Labels permutation20 hz
    mixedMoment B raw22398step2 raw22398step2Labels = mixedMoment B raw22398step3 raw22398step3Labels := by
      have ha : raw22398step3 = (fun i j => raw22398step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22398step3 raw22398step2; decide +kernel
      have hl : raw22398step3Labels = raw22398step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22398step2 raw22398step2Labels permutation7 permutation0
    mixedMoment B raw22398step3 raw22398step3Labels = mixedMoment B raw22398step4 raw22398step4Labels := by
      have ha : raw22398step4 = -raw22398step3 := by apply Matrix.ext; change ∀ i j, raw22398step4 i j = -(raw22398step3 i j); unfold raw22398step4 raw22398step3; decide +kernel
      have hl : raw22398step4Labels = raw22398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical22399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22399 raw22399Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw22399 raw22399Labels = mixedMoment B raw22399step0 raw22399step0Labels := by
      have hz : ∀ j, raw22399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22399step0 = (fun i j => raw22399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22399step0 raw22399; decide +kernel
      have hl : raw22399step0Labels = raw22399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22399 raw22399Labels permutation434 hz
    mixedMoment B raw22399step0 raw22399step0Labels = mixedMoment B raw22399step1 raw22399step1Labels := by
      have hz : ∀ j, raw22399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22399step1 = (fun i j => raw22399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22399step1 raw22399step0; decide +kernel
      have hl : raw22399step1Labels = raw22399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22399step0 raw22399step0Labels permutation80 hz
    mixedMoment B raw22399step1 raw22399step1Labels = mixedMoment B raw22399step2 raw22399step2Labels := by
      have ha : raw22399step2 = (fun i j => raw22399step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22399step2 raw22399step1; decide +kernel
      have hl : raw22399step2Labels = raw22399step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22399step1 raw22399step1Labels permutation9 permutation2
    _ = mixedMoment B node653 node653Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22400 raw22400Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22400 raw22400Labels = mixedMoment B raw22400step0 raw22400step0Labels := by
      have hz : ∀ j, raw22400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22400step0 = (fun i j => raw22400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22400step0 raw22400; decide +kernel
      have hl : raw22400step0Labels = raw22400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22400 raw22400Labels permutation434 hz
    mixedMoment B raw22400step0 raw22400step0Labels = mixedMoment B raw22400step1 raw22400step1Labels := by
      have hz : ∀ j, raw22400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22400step1 = (fun i j => raw22400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22400step1 raw22400step0; decide +kernel
      have hl : raw22400step1Labels = raw22400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22400step0 raw22400step0Labels permutation80 hz
    mixedMoment B raw22400step1 raw22400step1Labels = mixedMoment B raw22400step2 raw22400step2Labels := by
      have ha : raw22400step2 = (fun i j => raw22400step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22400step2 raw22400step1; decide +kernel
      have hl : raw22400step2Labels = raw22400step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22400step1 raw22400step1Labels permutation9 permutation2
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical22401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22401 raw22401Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw22401 raw22401Labels = mixedMoment B raw22401step0 raw22401step0Labels := by
      have hz : ∀ j, raw22401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22401step0 = (fun i j => raw22401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22401step0 raw22401; decide +kernel
      have hl : raw22401step0Labels = raw22401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22401 raw22401Labels permutation434 hz
    mixedMoment B raw22401step0 raw22401step0Labels = mixedMoment B raw22401step1 raw22401step1Labels := by
      have ha : raw22401step1 = (fun i j => raw22401step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22401step1 raw22401step0; decide +kernel
      have hl : raw22401step1Labels = raw22401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22401step0 raw22401step0Labels permutation39 permutation2
    _ = mixedMoment B node1171 node1171Labels := by rfl

theorem canonical22402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22402 raw22402Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw22402 raw22402Labels = mixedMoment B raw22402step0 raw22402step0Labels := by
      have hz : ∀ j, raw22402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22402step0 = (fun i j => raw22402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22402step0 raw22402; decide +kernel
      have hl : raw22402step0Labels = raw22402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22402 raw22402Labels permutation346 hz
    mixedMoment B raw22402step0 raw22402step0Labels = mixedMoment B raw22402step1 raw22402step1Labels := by
      have ha : raw22402step1 = (fun i j => raw22402step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22402step1 raw22402step0; decide +kernel
      have hl : raw22402step1Labels = raw22402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22402step0 raw22402step0Labels permutation39 permutation2
    _ = mixedMoment B node1171 node1171Labels := by rfl

theorem canonical22403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22403 raw22403Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw22403 raw22403Labels = mixedMoment B raw22403step0 raw22403step0Labels := by
      have hz : ∀ j, raw22403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22403step0 = (fun i j => raw22403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22403step0 raw22403; decide +kernel
      have hl : raw22403step0Labels = raw22403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22403 raw22403Labels permutation434 hz
    mixedMoment B raw22403step0 raw22403step0Labels = mixedMoment B raw22403step1 raw22403step1Labels := by
      have hz : ∀ j, raw22403step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22403step1 = (fun i j => raw22403step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22403step1 raw22403step0; decide +kernel
      have hl : raw22403step1Labels = raw22403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22403step0 raw22403step0Labels permutation80 hz
    _ = mixedMoment B node1306 node1306Labels := by rfl

theorem canonical22404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22404 raw22404Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22404 raw22404Labels = mixedMoment B raw22404step0 raw22404step0Labels := by
      have hz : ∀ j, raw22404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22404step0 = (fun i j => raw22404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22404step0 raw22404; decide +kernel
      have hl : raw22404step0Labels = raw22404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22404 raw22404Labels permutation434 hz
    mixedMoment B raw22404step0 raw22404step0Labels = mixedMoment B raw22404step1 raw22404step1Labels := by
      have hz : ∀ j, raw22404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22404step1 = (fun i j => raw22404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22404step1 raw22404step0; decide +kernel
      have hl : raw22404step1Labels = raw22404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22404step0 raw22404step0Labels permutation80 hz
    mixedMoment B raw22404step1 raw22404step1Labels = mixedMoment B raw22404step2 raw22404step2Labels := by
      have ha : raw22404step2 = (fun i j => raw22404step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22404step2 raw22404step1; decide +kernel
      have hl : raw22404step2Labels = raw22404step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22404step1 raw22404step1Labels permutation12 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical22405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22405 raw22405Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw22405 raw22405Labels = mixedMoment B raw22405step0 raw22405step0Labels := by
      have hz : ∀ j, raw22405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22405step0 = (fun i j => raw22405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22405step0 raw22405; decide +kernel
      have hl : raw22405step0Labels = raw22405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22405 raw22405Labels permutation434 hz
    mixedMoment B raw22405step0 raw22405step0Labels = mixedMoment B raw22405step1 raw22405step1Labels := by
      have hz : ∀ j, raw22405step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22405step1 = (fun i j => raw22405step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22405step1 raw22405step0; decide +kernel
      have hl : raw22405step1Labels = raw22405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22405step0 raw22405step0Labels permutation80 hz
    mixedMoment B raw22405step1 raw22405step1Labels = mixedMoment B raw22405step2 raw22405step2Labels := by
      have ha : raw22405step2 = (fun i j => raw22405step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22405step2 raw22405step1; decide +kernel
      have hl : raw22405step2Labels = raw22405step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22405step1 raw22405step1Labels permutation12 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

theorem canonical5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5197 raw5197Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5197 raw5197Labels = mixedMoment B raw5197step0 raw5197step0Labels := by
      have hz : ∀ j, raw5197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5197step0 = (fun i j => raw5197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5197step0 raw5197; decide +kernel
      have hl : raw5197step0Labels = raw5197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197 raw5197Labels permutation520 hz
    mixedMoment B raw5197step0 raw5197step0Labels = mixedMoment B raw5197step1 raw5197step1Labels := by
      have hz : ∀ j, raw5197step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5197step1 = (fun i j => raw5197step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5197step1 raw5197step0; decide +kernel
      have hl : raw5197step1Labels = raw5197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step0 raw5197step0Labels permutation104 hz
    mixedMoment B raw5197step1 raw5197step1Labels = mixedMoment B raw5197step2 raw5197step2Labels := by
      have hz : ∀ j, raw5197step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5197step2 = (fun i j => raw5197step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5197step2 raw5197step1; decide +kernel
      have hl : raw5197step2Labels = raw5197step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step1 raw5197step1Labels permutation20 hz
    mixedMoment B raw5197step2 raw5197step2Labels = mixedMoment B raw5197step3 raw5197step3Labels := by
      have hz : ∀ i, raw5197step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5197step3 = (fun i j => raw5197step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5197step3 raw5197step2; decide +kernel
      have hl : raw5197step3Labels = (fun j => raw5197step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5197step2 raw5197step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5201 raw5201Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5201 raw5201Labels = mixedMoment B raw5201step0 raw5201step0Labels := by
      have hz : ∀ j, raw5201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5201step0 = (fun i j => raw5201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5201step0 raw5201; decide +kernel
      have hl : raw5201step0Labels = raw5201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201 raw5201Labels permutation520 hz
    mixedMoment B raw5201step0 raw5201step0Labels = mixedMoment B raw5201step1 raw5201step1Labels := by
      have hz : ∀ j, raw5201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5201step1 = (fun i j => raw5201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5201step1 raw5201step0; decide +kernel
      have hl : raw5201step1Labels = raw5201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step0 raw5201step0Labels permutation104 hz
    mixedMoment B raw5201step1 raw5201step1Labels = mixedMoment B raw5201step2 raw5201step2Labels := by
      have hz : ∀ j, raw5201step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5201step2 = (fun i j => raw5201step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5201step2 raw5201step1; decide +kernel
      have hl : raw5201step2Labels = raw5201step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step1 raw5201step1Labels permutation14 hz
    mixedMoment B raw5201step2 raw5201step2Labels = mixedMoment B raw5201step3 raw5201step3Labels := by
      have hz : ∀ i, raw5201step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5201step3 = (fun i j => raw5201step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5201step3 raw5201step2; decide +kernel
      have hl : raw5201step3Labels = (fun j => raw5201step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5201step2 raw5201step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5205 raw5205Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5205 raw5205Labels = mixedMoment B raw5205step0 raw5205step0Labels := by
      have hz : ∀ j, raw5205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5205step0 = (fun i j => raw5205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5205step0 raw5205; decide +kernel
      have hl : raw5205step0Labels = raw5205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205 raw5205Labels permutation520 hz
    mixedMoment B raw5205step0 raw5205step0Labels = mixedMoment B raw5205step1 raw5205step1Labels := by
      have hz : ∀ j, raw5205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5205step1 = (fun i j => raw5205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5205step1 raw5205step0; decide +kernel
      have hl : raw5205step1Labels = raw5205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step0 raw5205step0Labels permutation80 hz
    mixedMoment B raw5205step1 raw5205step1Labels = mixedMoment B raw5205step2 raw5205step2Labels := by
      have hz : ∀ j, raw5205step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5205step2 = (fun i j => raw5205step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5205step2 raw5205step1; decide +kernel
      have hl : raw5205step2Labels = raw5205step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step1 raw5205step1Labels permutation14 hz
    mixedMoment B raw5205step2 raw5205step2Labels = mixedMoment B raw5205step3 raw5205step3Labels := by
      have hz : ∀ i, raw5205step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5205step3 = (fun i j => raw5205step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5205step3 raw5205step2; decide +kernel
      have hl : raw5205step3Labels = (fun j => raw5205step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5205step2 raw5205step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5210 raw5210Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5210 raw5210Labels = mixedMoment B raw5210step0 raw5210step0Labels := by
      have hz : ∀ j, raw5210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5210step0 = (fun i j => raw5210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5210step0 raw5210; decide +kernel
      have hl : raw5210step0Labels = raw5210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210 raw5210Labels permutation434 hz
    mixedMoment B raw5210step0 raw5210step0Labels = mixedMoment B raw5210step1 raw5210step1Labels := by
      have hz : ∀ j, raw5210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5210step1 = (fun i j => raw5210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5210step1 raw5210step0; decide +kernel
      have hl : raw5210step1Labels = raw5210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210step0 raw5210step0Labels permutation80 hz
    mixedMoment B raw5210step1 raw5210step1Labels = mixedMoment B raw5210step2 raw5210step2Labels := by
      have hz : ∀ i, raw5210step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5210step2 = (fun i j => raw5210step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5210step2 raw5210step1; decide +kernel
      have hl : raw5210step2Labels = (fun j => raw5210step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5210step1 raw5210step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical5213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5213 raw5213Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw5213 raw5213Labels = mixedMoment B raw5213step0 raw5213step0Labels := by
      have hz : ∀ j, raw5213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5213step0 = (fun i j => raw5213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5213step0 raw5213; decide +kernel
      have hl : raw5213step0Labels = raw5213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213 raw5213Labels permutation520 hz
    mixedMoment B raw5213step0 raw5213step0Labels = mixedMoment B raw5213step1 raw5213step1Labels := by
      have hz : ∀ j, raw5213step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5213step1 = (fun i j => raw5213step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5213step1 raw5213step0; decide +kernel
      have hl : raw5213step1Labels = raw5213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step0 raw5213step0Labels permutation104 hz
    mixedMoment B raw5213step1 raw5213step1Labels = mixedMoment B raw5213step2 raw5213step2Labels := by
      have hz : ∀ j, raw5213step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5213step2 = (fun i j => raw5213step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5213step2 raw5213step1; decide +kernel
      have hl : raw5213step2Labels = raw5213step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step1 raw5213step1Labels permutation20 hz
    mixedMoment B raw5213step2 raw5213step2Labels = mixedMoment B raw5213step3 raw5213step3Labels := by
      have hz : ∀ j, raw5213step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5213step3 = (fun i j => raw5213step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5213step3 raw5213step2; decide +kernel
      have hl : raw5213step3Labels = raw5213step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step2 raw5213step2Labels permutation4 hz
    mixedMoment B raw5213step3 raw5213step3Labels = mixedMoment B raw5213step4 raw5213step4Labels := by
      have hz : ∀ i, raw5213step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5213step4 = (fun i j => raw5213step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5213step4 raw5213step3; decide +kernel
      have hl : raw5213step4Labels = (fun j => raw5213step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5213step3 raw5213step3Labels permutation6 hz
    _ = mixedMoment B node4072 node4072Labels := by rfl

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

theorem canonical8535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8535 raw8535Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8535 raw8535Labels = mixedMoment B raw8535step0 raw8535step0Labels := by
      have hz : ∀ j, raw8535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8535step0 = (fun i j => raw8535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8535step0 raw8535; decide +kernel
      have hl : raw8535step0Labels = raw8535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535 raw8535Labels permutation346 hz
    mixedMoment B raw8535step0 raw8535step0Labels = mixedMoment B raw8535step1 raw8535step1Labels := by
      have hz : ∀ j, raw8535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8535step1 = (fun i j => raw8535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8535step1 raw8535step0; decide +kernel
      have hl : raw8535step1Labels = raw8535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535step0 raw8535step0Labels permutation56 hz
    mixedMoment B raw8535step1 raw8535step1Labels = mixedMoment B raw8535step2 raw8535step2Labels := by
      have ha : raw8535step2 = (fun i j => raw8535step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8535step2 raw8535step1; decide +kernel
      have hl : raw8535step2Labels = raw8535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8535step1 raw8535step1Labels permutation9 permutation2
    _ = mixedMoment B node1375 node1375Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9013 raw9013Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9013 raw9013Labels = mixedMoment B raw9013step0 raw9013step0Labels := by
      have hz : ∀ j, raw9013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9013step0 = (fun i j => raw9013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9013step0 raw9013; decide +kernel
      have hl : raw9013step0Labels = raw9013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9013 raw9013Labels permutation265 hz
    mixedMoment B raw9013step0 raw9013step0Labels = mixedMoment B raw9013step1 raw9013step1Labels := by
      have ha : raw9013step1 = (fun i j => raw9013step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9013step1 raw9013step0; decide +kernel
      have hl : raw9013step1Labels = raw9013step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9013step0 raw9013step0Labels permutation122 permutation0
    mixedMoment B raw9013step1 raw9013step1Labels = mixedMoment B raw9013step2 raw9013step2Labels := by
      have ha : raw9013step2 = -raw9013step1 := by apply Matrix.ext; change ∀ i j, raw9013step2 i j = -(raw9013step1 i j); unfold raw9013step2 raw9013step1; decide +kernel
      have hl : raw9013step2Labels = raw9013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9017 raw9017Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9017 raw9017Labels = mixedMoment B raw9017step0 raw9017step0Labels := by
      have hz : ∀ j, raw9017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9017step0 = (fun i j => raw9017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9017step0 raw9017; decide +kernel
      have hl : raw9017step0Labels = raw9017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9017 raw9017Labels permutation265 hz
    mixedMoment B raw9017step0 raw9017step0Labels = mixedMoment B raw9017step1 raw9017step1Labels := by
      have ha : raw9017step1 = (fun i j => raw9017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9017step1 raw9017step0; decide +kernel
      have hl : raw9017step1Labels = raw9017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9017step0 raw9017step0Labels permutation33 permutation2
    _ = mixedMoment B node1391 node1391Labels := by rfl

theorem canonical9031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9031 raw9031Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw9031 raw9031Labels = mixedMoment B raw9031step0 raw9031step0Labels := by
      have hz : ∀ j, raw9031 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9031step0 = (fun i j => raw9031 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9031step0 raw9031; decide +kernel
      have hl : raw9031step0Labels = raw9031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9031 raw9031Labels permutation265 hz
    mixedMoment B raw9031step0 raw9031step0Labels = mixedMoment B raw9031step1 raw9031step1Labels := by
      have ha : raw9031step1 = (fun i j => raw9031step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9031step1 raw9031step0; decide +kernel
      have hl : raw9031step1Labels = raw9031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9031step0 raw9031step0Labels permutation33 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

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

theorem canonical11531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11531 raw11531Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11531 raw11531Labels = mixedMoment B raw11531step0 raw11531step0Labels := by
      have hz : ∀ j, raw11531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11531step0 = (fun i j => raw11531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11531step0 raw11531; decide +kernel
      have hl : raw11531step0Labels = raw11531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531 raw11531Labels permutation434 hz
    mixedMoment B raw11531step0 raw11531step0Labels = mixedMoment B raw11531step1 raw11531step1Labels := by
      have hz : ∀ j, raw11531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11531step1 = (fun i j => raw11531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11531step1 raw11531step0; decide +kernel
      have hl : raw11531step1Labels = raw11531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531step0 raw11531step0Labels permutation80 hz
    mixedMoment B raw11531step1 raw11531step1Labels = mixedMoment B raw11531step2 raw11531step2Labels := by
      have hz : ∀ i, raw11531step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11531step2 = (fun i j => raw11531step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11531step2 raw11531step1; decide +kernel
      have hl : raw11531step2Labels = (fun j => raw11531step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11531step1 raw11531step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem canonical11540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11540 raw11540Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw11540 raw11540Labels = mixedMoment B raw11540step0 raw11540step0Labels := by
      have hz : ∀ j, raw11540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11540step0 = (fun i j => raw11540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11540step0 raw11540; decide +kernel
      have hl : raw11540step0Labels = raw11540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540 raw11540Labels permutation434 hz
    mixedMoment B raw11540step0 raw11540step0Labels = mixedMoment B raw11540step1 raw11540step1Labels := by
      have hz : ∀ j, raw11540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11540step1 = (fun i j => raw11540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11540step1 raw11540step0; decide +kernel
      have hl : raw11540step1Labels = raw11540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step0 raw11540step0Labels permutation80 hz
    mixedMoment B raw11540step1 raw11540step1Labels = mixedMoment B raw11540step2 raw11540step2Labels := by
      have hz : ∀ j, raw11540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11540step2 = (fun i j => raw11540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11540step2 raw11540step1; decide +kernel
      have hl : raw11540step2Labels = raw11540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step1 raw11540step1Labels permutation14 hz
    mixedMoment B raw11540step2 raw11540step2Labels = mixedMoment B raw11540step3 raw11540step3Labels := by
      have hz : ∀ i, raw11540step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11540step3 = (fun i j => raw11540step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11540step3 raw11540step2; decide +kernel
      have hl : raw11540step3Labels = (fun j => raw11540step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11540step2 raw11540step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node653 node653Labels = Sparse.eval nodeValue653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 653) = mixedMoment B node653 node653Labels := rfl
  simpa [nodeValue653, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

theorem sound830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node830 node830Labels = Sparse.eval nodeValue830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 830) = mixedMoment B node830 node830Labels := rfl
  simpa [nodeValue830, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

theorem sound858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node858 node858Labels = Sparse.eval nodeValue858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 858) = mixedMoment B node858 node858Labels := rfl
  simpa [nodeValue858, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node935 node935Labels = Sparse.eval nodeValue935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 935) = mixedMoment B node935 node935Labels := rfl
  simpa [nodeValue935, Sparse.eval] using hc.symm

theorem sound950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node950 node950Labels = Sparse.eval nodeValue950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 950) = mixedMoment B node950 node950Labels := rfl
  simpa [nodeValue950, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1026 node1026Labels = Sparse.eval nodeValue1026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1026) = mixedMoment B node1026 node1026Labels := rfl
  simpa [nodeValue1026, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1063 node1063Labels = Sparse.eval nodeValue1063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1063) = mixedMoment B node1063 node1063Labels := rfl
  simpa [nodeValue1063, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1133 node1133Labels = Sparse.eval nodeValue1133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1133) = mixedMoment B node1133 node1133Labels := rfl
  simpa [nodeValue1133, Sparse.eval] using hc.symm

theorem sound1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1143 node1143Labels = Sparse.eval nodeValue1143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1143) = mixedMoment B node1143 node1143Labels := rfl
  simpa [nodeValue1143, Sparse.eval] using hc.symm

theorem sound1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1146 node1146Labels = Sparse.eval nodeValue1146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1146) = mixedMoment B node1146 node1146Labels := rfl
  simpa [nodeValue1146, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound1171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1171 node1171Labels = Sparse.eval nodeValue1171 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1171) = mixedMoment B node1171 node1171Labels := rfl
  simpa [nodeValue1171, Sparse.eval] using hc.symm

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

theorem sound1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1245 node1245Labels = Sparse.eval nodeValue1245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1245) = mixedMoment B node1245 node1245Labels := rfl
  simpa [nodeValue1245, Sparse.eval] using hc.symm

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

theorem sound1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1318 node1318Labels = Sparse.eval nodeValue1318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1318) = mixedMoment B node1318 node1318Labels := rfl
  simpa [nodeValue1318, Sparse.eval] using hc.symm

theorem sound1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1324 node1324Labels = Sparse.eval nodeValue1324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1324) = mixedMoment B node1324 node1324Labels := rfl
  simpa [nodeValue1324, Sparse.eval] using hc.symm

theorem sound1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1325 node1325Labels = Sparse.eval nodeValue1325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1325) = mixedMoment B node1325 node1325Labels := rfl
  simpa [nodeValue1325, Sparse.eval] using hc.symm

theorem sound1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1328 node1328Labels = Sparse.eval nodeValue1328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1328) = mixedMoment B node1328 node1328Labels := rfl
  simpa [nodeValue1328, Sparse.eval] using hc.symm

theorem sound1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1333 node1333Labels = Sparse.eval nodeValue1333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1333) = mixedMoment B node1333 node1333Labels := rfl
  simpa [nodeValue1333, Sparse.eval] using hc.symm

theorem sound1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1334 node1334Labels = Sparse.eval nodeValue1334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1334) = mixedMoment B node1334 node1334Labels := rfl
  simpa [nodeValue1334, Sparse.eval] using hc.symm

theorem sound1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1338 node1338Labels = Sparse.eval nodeValue1338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1338) = mixedMoment B node1338 node1338Labels := rfl
  simpa [nodeValue1338, Sparse.eval] using hc.symm

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

theorem sound1356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1356 node1356Labels = Sparse.eval nodeValue1356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1356) = mixedMoment B node1356 node1356Labels := rfl
  simpa [nodeValue1356, Sparse.eval] using hc.symm

theorem sound1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1375 node1375Labels = Sparse.eval nodeValue1375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1375) = mixedMoment B node1375 node1375Labels := rfl
  simpa [nodeValue1375, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1614 node1614Labels = 0 := by
  exact mixedMoment_alpha B hF node1614 node1614Labels 1 permutation446
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

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

theorem sound1606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1606 node1606Labels = Sparse.eval nodeValue1606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1606) = mixedMoment B node1606 node1606Labels := rfl
  simpa [nodeValue1606, Sparse.eval] using hc.symm

theorem sound1611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1611 node1611Labels = Sparse.eval nodeValue1611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1611) = mixedMoment B node1611 node1611Labels := rfl
  simpa [nodeValue1611, Sparse.eval] using hc.symm

theorem sound1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1614 node1614Labels = Sparse.eval nodeValue1614 (mixedVector B) := by
  simpa only [nodeValue1614, Sparse.eval_nil] using zero1614 B _hB _hF

theorem sound1626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1626 node1626Labels = Sparse.eval nodeValue1626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1626) = mixedMoment B node1626 node1626Labels := rfl
  simpa [nodeValue1626, Sparse.eval] using hc.symm

theorem sound1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1655 node1655Labels = Sparse.eval nodeValue1655 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1655) = mixedMoment B node1655 node1655Labels := rfl
  simpa [nodeValue1655, Sparse.eval] using hc.symm

theorem sound1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1660 node1660Labels = Sparse.eval nodeValue1660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1660) = mixedMoment B node1660 node1660Labels := rfl
  simpa [nodeValue1660, Sparse.eval] using hc.symm

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

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1740 node1740Labels = Sparse.eval nodeValue1740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1740) = mixedMoment B node1740 node1740Labels := rfl
  simpa [nodeValue1740, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2397 node2397Labels = Sparse.eval nodeValue2397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2397) = mixedMoment B node2397 node2397Labels := rfl
  simpa [nodeValue2397, Sparse.eval] using hc.symm

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

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

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

theorem sound2856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2856 node2856Labels = Sparse.eval nodeValue2856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2856) = mixedMoment B node2856 node2856Labels := rfl
  simpa [nodeValue2856, Sparse.eval] using hc.symm

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

theorem sound2911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2911 node2911Labels = Sparse.eval nodeValue2911 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2911) = mixedMoment B node2911 node2911Labels := rfl
  simpa [nodeValue2911, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound2970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2970 node2970Labels = Sparse.eval nodeValue2970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2970) = mixedMoment B node2970 node2970Labels := rfl
  simpa [nodeValue2970, Sparse.eval] using hc.symm

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

theorem sound3025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3025 node3025Labels = Sparse.eval nodeValue3025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3025) = mixedMoment B node3025 node3025Labels := rfl
  simpa [nodeValue3025, Sparse.eval] using hc.symm

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

theorem sound3280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3280 node3280Labels = Sparse.eval nodeValue3280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3280) = mixedMoment B node3280 node3280Labels := rfl
  simpa [nodeValue3280, Sparse.eval] using hc.symm

theorem sound3284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3284 node3284Labels = Sparse.eval nodeValue3284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3284) = mixedMoment B node3284 node3284Labels := rfl
  simpa [nodeValue3284, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

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

theorem sound4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4058 node4058Labels = Sparse.eval nodeValue4058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4058) = mixedMoment B node4058 node4058Labels := rfl
  simpa [nodeValue4058, Sparse.eval] using hc.symm

theorem sound4060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4060 node4060Labels = Sparse.eval nodeValue4060 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4060) = mixedMoment B node4060 node4060Labels := rfl
  simpa [nodeValue4060, Sparse.eval] using hc.symm

theorem sound4061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4061 node4061Labels = Sparse.eval nodeValue4061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4061) = mixedMoment B node4061 node4061Labels := rfl
  simpa [nodeValue4061, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4072 node4072Labels = Sparse.eval nodeValue4072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4072) = mixedMoment B node4072 node4072Labels := rfl
  simpa [nodeValue4072, Sparse.eval] using hc.symm

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

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node586 node586Labels = Sparse.eval nodeValue586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 586) = mixedMoment B node586 node586Labels := rfl
  simpa [nodeValue586, Sparse.eval] using hc.symm

theorem sound616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node616 node616Labels = Sparse.eval nodeValue616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 616) = mixedMoment B node616 node616Labels := rfl
  simpa [nodeValue616, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1439 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 1) (sourceB1439 + difference 1 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 1) (sourceB1439 + difference 1 0) sourceC1439) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 2) (sourceB1439 + difference 2 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 2) (sourceB1439 + difference 2 0) sourceC1439) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 3) (sourceB1439 + difference 3 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 3) (sourceB1439 + difference 3 0) sourceC1439) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 4) (sourceB1439 + difference 4 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 4) (sourceB1439 + difference 4 0) sourceC1439) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 5) (sourceB1439 + difference 5 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 5) (sourceB1439 + difference 5 0) sourceC1439) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 0) (sourceB1439 + difference 0 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 0) (sourceB1439 + difference 0 1) sourceC1439) = raw22301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22301; decide +kernel
    rw [ha]
    exact (canonical22301 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 2) (sourceB1439 + difference 2 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 2) (sourceB1439 + difference 2 1) sourceC1439) = raw22302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22302; decide +kernel
    rw [ha]
    exact (canonical22302 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 3) (sourceB1439 + difference 3 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 3) (sourceB1439 + difference 3 1) sourceC1439) = raw22303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22303; decide +kernel
    rw [ha]
    exact (canonical22303 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 4) (sourceB1439 + difference 4 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 4) (sourceB1439 + difference 4 1) sourceC1439) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 5) (sourceB1439 + difference 5 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 5) (sourceB1439 + difference 5 1) sourceC1439) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 0) (sourceB1439 + difference 0 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 0) (sourceB1439 + difference 0 2) sourceC1439) = raw22304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22304; decide +kernel
    rw [ha]
    exact (canonical22304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 1) (sourceB1439 + difference 1 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 1) (sourceB1439 + difference 1 2) sourceC1439) = raw22305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22305; decide +kernel
    rw [ha]
    exact (canonical22305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 3) (sourceB1439 + difference 3 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 3) (sourceB1439 + difference 3 2) sourceC1439) = raw22306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22306; decide +kernel
    rw [ha]
    exact (canonical22306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 4) (sourceB1439 + difference 4 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 4) (sourceB1439 + difference 4 2) sourceC1439) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 5) (sourceB1439 + difference 5 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 5) (sourceB1439 + difference 5 2) sourceC1439) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 0) (sourceB1439 + difference 0 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 0) (sourceB1439 + difference 0 3) sourceC1439) = raw22307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22307; decide +kernel
    rw [ha]
    exact (canonical22307 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 1) (sourceB1439 + difference 1 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 1) (sourceB1439 + difference 1 3) sourceC1439) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 2) (sourceB1439 + difference 2 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 2) (sourceB1439 + difference 2 3) sourceC1439) = raw22309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22309; decide +kernel
    rw [ha]
    exact (canonical22309 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 4) (sourceB1439 + difference 4 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 4) (sourceB1439 + difference 4 3) sourceC1439) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 5) (sourceB1439 + difference 5 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 5) (sourceB1439 + difference 5 3) sourceC1439) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 0) (sourceB1439 + difference 0 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 0) (sourceB1439 + difference 0 4) sourceC1439) = raw22310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22310; decide +kernel
    rw [ha]
    exact (canonical22310 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 1) (sourceB1439 + difference 1 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 1) (sourceB1439 + difference 1 4) sourceC1439) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 2) (sourceB1439 + difference 2 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 2) (sourceB1439 + difference 2 4) sourceC1439) = raw22312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22312; decide +kernel
    rw [ha]
    exact (canonical22312 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 3) (sourceB1439 + difference 3 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 3) (sourceB1439 + difference 3 4) sourceC1439) = raw22313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22313; decide +kernel
    rw [ha]
    exact (canonical22313 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 5) (sourceB1439 + difference 5 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 5) (sourceB1439 + difference 5 4) sourceC1439) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 0) (sourceB1439 + difference 0 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 0) (sourceB1439 + difference 0 5) sourceC1439) = raw20079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20079; decide +kernel
    rw [ha]
    exact (canonical20079 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 1) (sourceB1439 + difference 1 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 1) (sourceB1439 + difference 1 5) sourceC1439) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 2) (sourceB1439 + difference 2 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 2) (sourceB1439 + difference 2 5) sourceC1439) = raw20081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20081; decide +kernel
    rw [ha]
    exact (canonical20081 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 3) (sourceB1439 + difference 3 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 3) (sourceB1439 + difference 3 5) sourceC1439) = raw20082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20082; decide +kernel
    rw [ha]
    exact (canonical20082 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 4) (sourceB1439 + difference 4 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 4) (sourceB1439 + difference 4 5) sourceC1439) = raw5213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5213; decide +kernel
    rw [ha]
    exact (canonical5213 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1439 sourceB1439 sourceC1439
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1439, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources45
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1440 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 0) (sourceB1440 + difference 0 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 616) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 0) (sourceB1440 + difference 0 3) sourceC1440) = raw22314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22314; decide +kernel
    rw [ha]
    exact (canonical22314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 1) (sourceB1440 + difference 1 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 1) (sourceB1440 + difference 1 3) sourceC1440) = raw22315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22315; decide +kernel
    rw [ha]
    exact (canonical22315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 2) (sourceB1440 + difference 2 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 2) (sourceB1440 + difference 2 3) sourceC1440) = raw22316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22316; decide +kernel
    rw [ha]
    exact (canonical22316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 3) (sourceB1440 + difference 3 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 3) (sourceB1440 + difference 3 3) sourceC1440) = raw22317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22317; decide +kernel
    rw [ha]
    exact (canonical22317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 4) (sourceB1440 + difference 4 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 4) (sourceB1440 + difference 4 3) sourceC1440) = raw20141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw20141; decide +kernel
    rw [ha]
    exact (canonical20141 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 5) (sourceB1440 + difference 5 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 5) (sourceB1440 + difference 5 3) sourceC1440) = raw22318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22318; decide +kernel
    rw [ha]
    exact (canonical22318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1440 + sourceB1440) sourceC1440) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1440 + sourceB1440) sourceC1440) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1440 sourceB1440 sourceC1440 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1440 sourceB1440 sourceC1440
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1440, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1441 + difference 0 3) (sourceB1441 + difference 3 0) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1441 + difference 0 3) (sourceB1441 + difference 3 0) sourceC1441) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1441 + difference 1 3) (sourceB1441 + difference 3 1) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1441 + difference 1 3) (sourceB1441 + difference 3 1) sourceC1441) = raw22319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22319; decide +kernel
    rw [ha]
    exact (canonical22319 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1441 + difference 2 3) (sourceB1441 + difference 3 2) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1441 + difference 2 3) (sourceB1441 + difference 3 2) sourceC1441) = raw22320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22320; decide +kernel
    rw [ha]
    exact (canonical22320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1441 + difference 3 3) (sourceB1441 + difference 3 3) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1441 + difference 3 3) (sourceB1441 + difference 3 3) sourceC1441) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1441 + difference 4 3) (sourceB1441 + difference 3 4) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1441 + difference 4 3) (sourceB1441 + difference 3 4) sourceC1441) = raw22321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22321; decide +kernel
    rw [ha]
    exact (canonical22321 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1441 + difference 5 3) (sourceB1441 + difference 3 5) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1441 + difference 5 3) (sourceB1441 + difference 3 5) sourceC1441) = raw22322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22322; decide +kernel
    rw [ha]
    exact (canonical22322 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1441 + sourceB1441) sourceC1441) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1441 + sourceB1441) sourceC1441) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA1441 sourceB1441 sourceC1441 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1441 sourceB1441 sourceC1441
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1441, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1443 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1443 + difference 0 3) (sourceB1443 + difference 3 0) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1443 + difference 0 3) (sourceB1443 + difference 3 0) sourceC1443) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1443 + difference 1 3) (sourceB1443 + difference 3 1) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1443 + difference 1 3) (sourceB1443 + difference 3 1) sourceC1443) = raw22330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22330; decide +kernel
    rw [ha]
    exact (canonical22330 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1443 + difference 2 3) (sourceB1443 + difference 3 2) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1443 + difference 2 3) (sourceB1443 + difference 3 2) sourceC1443) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1443 + difference 3 3) (sourceB1443 + difference 3 3) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1443 + difference 3 3) (sourceB1443 + difference 3 3) sourceC1443) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1443 + difference 4 3) (sourceB1443 + difference 3 4) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1443 + difference 4 3) (sourceB1443 + difference 3 4) sourceC1443) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1443 + difference 5 3) (sourceB1443 + difference 3 5) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1443 + difference 5 3) (sourceB1443 + difference 3 5) sourceC1443) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1443 + sourceB1443) sourceC1443) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1443 + sourceB1443) sourceC1443) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1443 sourceB1443 sourceC1443 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1443 sourceB1443 sourceC1443
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1443, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1444 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 0) (sourceB1444 + difference 0 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 0) (sourceB1444 + difference 0 4) sourceC1444) = raw22334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22334; decide +kernel
    rw [ha]
    exact (canonical22334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 1) (sourceB1444 + difference 1 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 1) (sourceB1444 + difference 1 4) sourceC1444) = raw22335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22335; decide +kernel
    rw [ha]
    exact (canonical22335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 2) (sourceB1444 + difference 2 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 2) (sourceB1444 + difference 2 4) sourceC1444) = raw22336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22336; decide +kernel
    rw [ha]
    exact (canonical22336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 3) (sourceB1444 + difference 3 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 3) (sourceB1444 + difference 3 4) sourceC1444) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 4) (sourceB1444 + difference 4 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 4) (sourceB1444 + difference 4 4) sourceC1444) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 5) (sourceB1444 + difference 5 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 5) (sourceB1444 + difference 5 4) sourceC1444) = raw22337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22337; decide +kernel
    rw [ha]
    exact (canonical22337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1444 + sourceB1444) sourceC1444) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1444 + sourceB1444) sourceC1444) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1444 sourceB1444 sourceC1444 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1444 sourceB1444 sourceC1444
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1444, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1445 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 0) (sourceB1445 + difference 0 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 0) (sourceB1445 + difference 0 5) sourceC1445) = raw22338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22338; decide +kernel
    rw [ha]
    exact (canonical22338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 1) (sourceB1445 + difference 1 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 1) (sourceB1445 + difference 1 5) sourceC1445) = raw22339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22339; decide +kernel
    rw [ha]
    exact (canonical22339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 2) (sourceB1445 + difference 2 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 2) (sourceB1445 + difference 2 5) sourceC1445) = raw22340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22340; decide +kernel
    rw [ha]
    exact (canonical22340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 3) (sourceB1445 + difference 3 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 3) (sourceB1445 + difference 3 5) sourceC1445) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 4) (sourceB1445 + difference 4 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 4) (sourceB1445 + difference 4 5) sourceC1445) = raw22341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22341; decide +kernel
    rw [ha]
    exact (canonical22341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 5) (sourceB1445 + difference 5 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 5) (sourceB1445 + difference 5 5) sourceC1445) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1445 + sourceB1445) sourceC1445) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1445 + sourceB1445) sourceC1445) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1445 sourceB1445 sourceC1445 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1445 sourceB1445 sourceC1445
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1445, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 0) (sourceB1448 + difference 0 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 0) (sourceB1448 + difference 0 2) sourceC1448) = raw22352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22352; decide +kernel
    rw [ha]
    exact (canonical22352 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 1) (sourceB1448 + difference 1 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 1) (sourceB1448 + difference 1 2) sourceC1448) = raw22353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22353; decide +kernel
    rw [ha]
    exact (canonical22353 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 2) (sourceB1448 + difference 2 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 2) (sourceB1448 + difference 2 2) sourceC1448) = raw22354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22354; decide +kernel
    rw [ha]
    exact (canonical22354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 3) (sourceB1448 + difference 3 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 3) (sourceB1448 + difference 3 2) sourceC1448) = raw22355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22355; decide +kernel
    rw [ha]
    exact (canonical22355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 4) (sourceB1448 + difference 4 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 4) (sourceB1448 + difference 4 2) sourceC1448) = raw20195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw20195; decide +kernel
    rw [ha]
    exact (canonical20195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 5) (sourceB1448 + difference 5 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 5) (sourceB1448 + difference 5 2) sourceC1448) = raw22356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22356; decide +kernel
    rw [ha]
    exact (canonical22356 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1448 + sourceB1448) sourceC1448) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1448 + sourceB1448) sourceC1448) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1448 sourceB1448 sourceC1448 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1448 sourceB1448 sourceC1448
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1448, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1449 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1449 + difference 0 2) (sourceB1449 + difference 2 0) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1449 + difference 0 2) (sourceB1449 + difference 2 0) sourceC1449) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1449 + difference 1 2) (sourceB1449 + difference 2 1) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA1449 + difference 1 2) (sourceB1449 + difference 2 1) sourceC1449) = raw22357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22357; decide +kernel
    rw [ha]
    exact (canonical22357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1449 + difference 2 2) (sourceB1449 + difference 2 2) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1449 + difference 2 2) (sourceB1449 + difference 2 2) sourceC1449) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1449 + difference 3 2) (sourceB1449 + difference 2 3) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA1449 + difference 3 2) (sourceB1449 + difference 2 3) sourceC1449) = raw22358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22358; decide +kernel
    rw [ha]
    exact (canonical22358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1449 + difference 4 2) (sourceB1449 + difference 2 4) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1449 + difference 4 2) (sourceB1449 + difference 2 4) sourceC1449) = raw22359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22359; decide +kernel
    rw [ha]
    exact (canonical22359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1449 + difference 5 2) (sourceB1449 + difference 2 5) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1449 + difference 5 2) (sourceB1449 + difference 2 5) sourceC1449) = raw22360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22360; decide +kernel
    rw [ha]
    exact (canonical22360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1449 + sourceB1449) sourceC1449) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1449 + sourceB1449) sourceC1449) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA1449 sourceB1449 sourceC1449 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1449 sourceB1449 sourceC1449
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1449, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1450 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 0) (sourceB1450 + difference 0 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 0) (sourceB1450 + difference 0 0) sourceC1450) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 1) (sourceB1450 + difference 1 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3280) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 1) (sourceB1450 + difference 1 0) sourceC1450) = raw22361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22361; decide +kernel
    rw [ha]
    exact (canonical22361 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 2) (sourceB1450 + difference 2 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 2) (sourceB1450 + difference 2 0) sourceC1450) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 3) (sourceB1450 + difference 3 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 3) (sourceB1450 + difference 3 0) sourceC1450) = raw22362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22362; decide +kernel
    rw [ha]
    exact (canonical22362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 4) (sourceB1450 + difference 4 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 4) (sourceB1450 + difference 4 0) sourceC1450) = raw22363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22363; decide +kernel
    rw [ha]
    exact (canonical22363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 5) (sourceB1450 + difference 5 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3284) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 5) (sourceB1450 + difference 5 0) sourceC1450) = raw22364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22364; decide +kernel
    rw [ha]
    exact (canonical22364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1450 + sourceB1450) sourceC1450) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1450 + sourceB1450) sourceC1450) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1450 sourceB1450 sourceC1450 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1450 sourceB1450 sourceC1450
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1450, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1452 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 0) (sourceB1452 + difference 0 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 0) (sourceB1452 + difference 0 4) sourceC1452) = raw22368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22368; decide +kernel
    rw [ha]
    exact (canonical22368 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 1) (sourceB1452 + difference 1 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1614) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 1) (sourceB1452 + difference 1 4) sourceC1452) = raw22370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22370; decide +kernel
    rw [ha]
    exact (canonical22370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 2) (sourceB1452 + difference 2 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 2) (sourceB1452 + difference 2 4) sourceC1452) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 3) (sourceB1452 + difference 3 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 3) (sourceB1452 + difference 3 4) sourceC1452) = raw22371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22371; decide +kernel
    rw [ha]
    exact (canonical22371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 4) (sourceB1452 + difference 4 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 4) (sourceB1452 + difference 4 4) sourceC1452) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 5) (sourceB1452 + difference 5 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 5) (sourceB1452 + difference 5 4) sourceC1452) = raw22372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22372; decide +kernel
    rw [ha]
    exact (canonical22372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1452 + sourceB1452) sourceC1452) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1452 + sourceB1452) sourceC1452) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1452 sourceB1452 sourceC1452 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1452 sourceB1452 sourceC1452
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1452, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 0) (sourceB1453 + difference 0 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 0) (sourceB1453 + difference 0 5) sourceC1453) = raw22369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22369; decide +kernel
    rw [ha]
    exact (canonical22369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 1) (sourceB1453 + difference 1 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 1) (sourceB1453 + difference 1 5) sourceC1453) = raw22373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22373; decide +kernel
    rw [ha]
    exact (canonical22373 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 2) (sourceB1453 + difference 2 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 2) (sourceB1453 + difference 2 5) sourceC1453) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 3) (sourceB1453 + difference 3 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 3) (sourceB1453 + difference 3 5) sourceC1453) = raw22374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22374; decide +kernel
    rw [ha]
    exact (canonical22374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 4) (sourceB1453 + difference 4 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 4) (sourceB1453 + difference 4 5) sourceC1453) = raw22375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22375; decide +kernel
    rw [ha]
    exact (canonical22375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 5) (sourceB1453 + difference 5 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 5) (sourceB1453 + difference 5 5) sourceC1453) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1453 + sourceB1453) sourceC1453) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1453 + sourceB1453) sourceC1453) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1453 sourceB1453 sourceC1453 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1453 sourceB1453 sourceC1453
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1453, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 0) (sourceB1455 + difference 0 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1356) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 0) (sourceB1455 + difference 0 0) sourceC1455) = raw22378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22378; decide +kernel
    rw [ha]
    exact (canonical22378 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 1) (sourceB1455 + difference 1 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2970) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 1) (sourceB1455 + difference 1 0) sourceC1455) = raw22379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22379; decide +kernel
    rw [ha]
    exact (canonical22379 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 2) (sourceB1455 + difference 2 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 2) (sourceB1455 + difference 2 0) sourceC1455) = raw22380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22380; decide +kernel
    rw [ha]
    exact (canonical22380 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 3) (sourceB1455 + difference 3 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 3) (sourceB1455 + difference 3 0) sourceC1455) = raw22381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22381; decide +kernel
    rw [ha]
    exact (canonical22381 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 4) (sourceB1455 + difference 4 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 4) (sourceB1455 + difference 4 0) sourceC1455) = raw22382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22382; decide +kernel
    rw [ha]
    exact (canonical22382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 5) (sourceB1455 + difference 5 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 5) (sourceB1455 + difference 5 0) sourceC1455) = raw22383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22383; decide +kernel
    rw [ha]
    exact (canonical22383 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1455 + sourceB1455) sourceC1455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1455 + sourceB1455) sourceC1455) = raw22384 := by
      apply Matrix.ext; unfold doubleCharges sourceA1455 sourceB1455 sourceC1455 raw22384; decide +kernel
    rw [ha]
    exact (canonical22384 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1455 sourceB1455 sourceC1455
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1455, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1457 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1457 + difference 0 1) (sourceB1457 + difference 1 0) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1457 + difference 0 1) (sourceB1457 + difference 1 0) sourceC1457) = raw22392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22392; decide +kernel
    rw [ha]
    exact (canonical22392 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1457 + difference 1 1) (sourceB1457 + difference 1 1) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1457 + difference 1 1) (sourceB1457 + difference 1 1) sourceC1457) = raw22393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22393; decide +kernel
    rw [ha]
    exact (canonical22393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1457 + difference 2 1) (sourceB1457 + difference 1 2) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1457 + difference 2 1) (sourceB1457 + difference 1 2) sourceC1457) = raw22394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22394; decide +kernel
    rw [ha]
    exact (canonical22394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1457 + difference 3 1) (sourceB1457 + difference 1 3) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1457 + difference 3 1) (sourceB1457 + difference 1 3) sourceC1457) = raw22395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22395; decide +kernel
    rw [ha]
    exact (canonical22395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1457 + difference 4 1) (sourceB1457 + difference 1 4) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1457 + difference 4 1) (sourceB1457 + difference 1 4) sourceC1457) = raw22396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22396; decide +kernel
    rw [ha]
    exact (canonical22396 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1457 + difference 5 1) (sourceB1457 + difference 1 5) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1457 + difference 5 1) (sourceB1457 + difference 1 5) sourceC1457) = raw22397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22397; decide +kernel
    rw [ha]
    exact (canonical22397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1457 + sourceB1457) sourceC1457) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1457 + sourceB1457) sourceC1457) = raw22398 := by
      apply Matrix.ext; unfold doubleCharges sourceA1457 sourceB1457 sourceC1457 raw22398; decide +kernel
    rw [ha]
    exact (canonical22398 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1457 sourceB1457 sourceC1457
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1457, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 0) (sourceB1458 + difference 0 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 0) (sourceB1458 + difference 0 1) sourceC1458) = raw22399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22399; decide +kernel
    rw [ha]
    exact (canonical22399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 1) (sourceB1458 + difference 1 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 1) (sourceB1458 + difference 1 1) sourceC1458) = raw22400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22400; decide +kernel
    rw [ha]
    exact (canonical22400 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 2) (sourceB1458 + difference 2 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 2) (sourceB1458 + difference 2 1) sourceC1458) = raw22401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22401; decide +kernel
    rw [ha]
    exact (canonical22401 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 3) (sourceB1458 + difference 3 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 3) (sourceB1458 + difference 3 1) sourceC1458) = raw22402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22402; decide +kernel
    rw [ha]
    exact (canonical22402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 4) (sourceB1458 + difference 4 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 4) (sourceB1458 + difference 4 1) sourceC1458) = raw22403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22403; decide +kernel
    rw [ha]
    exact (canonical22403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 5) (sourceB1458 + difference 5 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 5) (sourceB1458 + difference 5 1) sourceC1458) = raw22404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22404; decide +kernel
    rw [ha]
    exact (canonical22404 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1458 + sourceB1458) sourceC1458) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1458 + sourceB1458) sourceC1458) = raw22405 := by
      apply Matrix.ext; unfold doubleCharges sourceA1458 sourceB1458 sourceC1458 raw22405; decide +kernel
    rw [ha]
    exact (canonical22405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1458 sourceB1458 sourceC1458
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1458, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1234 : Integer.Sparse.reindex keyMap MixedData.row1234 = numericRow1234 := by decide +kernel

theorem numericCheck1234 (x : Master → ℝ) : Integer.Sparse.eval numericRow1234 x =
    (1 : ℝ) * reducedSource1234 x := by
  norm_num [numericRow1234, reducedSource1234, Integer.Sparse.eval, Sparse.eval, nodeValue4058, nodeValue4060, nodeValue4061, nodeValue4064, nodeValue4066, nodeValue4067, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4072, nodeValue4081, nodeValue4084, nodeValue4085]

theorem reindexCheck1235 : Integer.Sparse.reindex keyMap MixedData.row1235 = numericRow1235 := by decide +kernel

theorem numericCheck1235 (x : Master → ℝ) : Integer.Sparse.eval numericRow1235 x =
    (1 : ℝ) * reducedSource1235 x := by
  norm_num [numericRow1235, reducedSource1235, Integer.Sparse.eval, Sparse.eval, nodeValue616, nodeValue935, nodeValue1063, nodeValue1083, nodeValue1087, nodeValue4084]

theorem reindexCheck1236 : Integer.Sparse.reindex keyMap MixedData.row1236 = numericRow1236 := by decide +kernel

theorem numericCheck1236 (x : Master → ℝ) : Integer.Sparse.eval numericRow1236 x =
    (1 : ℝ) * reducedSource1236 x := by
  norm_num [numericRow1236, reducedSource1236, Integer.Sparse.eval, Sparse.eval, nodeValue1318, nodeValue1324, nodeValue1325, nodeValue1375, nodeValue2889, nodeValue4092]

theorem reindexCheck1237 : Integer.Sparse.reindex keyMap MixedData.row1237 = numericRow1237 := by decide +kernel

theorem numericCheck1237 (x : Master → ℝ) : Integer.Sparse.eval numericRow1237 x =
    (1 : ℝ) * reducedSource1237 x := by
  norm_num [numericRow1237, reducedSource1237, Integer.Sparse.eval, Sparse.eval, nodeValue1736, nodeValue1738, nodeValue1740, nodeValue1751, nodeValue3301, nodeValue4071]

theorem reindexCheck1238 : Integer.Sparse.reindex keyMap MixedData.row1238 = numericRow1238 := by decide +kernel

theorem numericCheck1238 (x : Master → ℝ) : Integer.Sparse.eval numericRow1238 x =
    (1 : ℝ) * reducedSource1238 x := by
  norm_num [numericRow1238, reducedSource1238, Integer.Sparse.eval, Sparse.eval, nodeValue858, nodeValue1626, nodeValue1740, nodeValue1751, nodeValue4071]

theorem reindexCheck1239 : Integer.Sparse.reindex keyMap MixedData.row1239 = numericRow1239 := by decide +kernel

theorem numericCheck1239 (x : Master → ℝ) : Integer.Sparse.eval numericRow1239 x =
    (1 : ℝ) * reducedSource1239 x := by
  norm_num [numericRow1239, reducedSource1239, Integer.Sparse.eval, Sparse.eval, nodeValue830, nodeValue1611, nodeValue1660, nodeValue1738, nodeValue1740, nodeValue4071]

theorem reindexCheck1240 : Integer.Sparse.reindex keyMap MixedData.row1240 = numericRow1240 := by decide +kernel

theorem numericCheck1240 (x : Master → ℝ) : Integer.Sparse.eval numericRow1240 x =
    (1 : ℝ) * reducedSource1240 x := by
  norm_num [numericRow1240, reducedSource1240, Integer.Sparse.eval, Sparse.eval, nodeValue586, nodeValue910, nodeValue950, nodeValue1026, nodeValue1041, nodeValue1044, nodeValue4083]

theorem reindexCheck1241 : Integer.Sparse.reindex keyMap MixedData.row1241 = numericRow1241 := by decide +kernel

theorem numericCheck1241 (x : Master → ℝ) : Integer.Sparse.eval numericRow1241 x =
    (1 : ℝ) * reducedSource1241 x := by
  norm_num [numericRow1241, reducedSource1241, Integer.Sparse.eval, Sparse.eval, nodeValue1328, nodeValue1333, nodeValue1334, nodeValue1338, nodeValue1391, nodeValue2931, nodeValue4091]

theorem reindexCheck1242 : Integer.Sparse.reindex keyMap MixedData.row1242 = numericRow1242 := by decide +kernel

theorem numericCheck1242 (x : Master → ℝ) : Integer.Sparse.eval numericRow1242 x =
    (1 : ℝ) * reducedSource1242 x := by
  norm_num [numericRow1242, reducedSource1242, Integer.Sparse.eval, Sparse.eval, nodeValue1736, nodeValue2397, nodeValue3280, nodeValue3284, nodeValue3301, nodeValue4071]

theorem reindexCheck1243 : Integer.Sparse.reindex keyMap MixedData.row1243 = numericRow1243 := by decide +kernel

theorem numericCheck1243 (x : Master → ℝ) : Integer.Sparse.eval numericRow1243 x =
    (1 : ℝ) * reducedSource1243 x := by
  norm_num [numericRow1243, reducedSource1243, Integer.Sparse.eval, Sparse.eval, nodeValue848, nodeValue1614, nodeValue1736, nodeValue1751, nodeValue4071]

theorem reindexCheck1244 : Integer.Sparse.reindex keyMap MixedData.row1244 = numericRow1244 := by decide +kernel

theorem numericCheck1244 (x : Master → ℝ) : Integer.Sparse.eval numericRow1244 x =
    (1 : ℝ) * reducedSource1244 x := by
  norm_num [numericRow1244, reducedSource1244, Integer.Sparse.eval, Sparse.eval, nodeValue823, nodeValue1606, nodeValue1655, nodeValue1736, nodeValue1738, nodeValue4071]

theorem reindexCheck1245 : Integer.Sparse.reindex keyMap MixedData.row1245 = numericRow1245 := by decide +kernel

theorem numericCheck1245 (x : Master → ℝ) : Integer.Sparse.eval numericRow1245 x =
    (1 : ℝ) * reducedSource1245 x := by
  norm_num [numericRow1245, reducedSource1245, Integer.Sparse.eval, Sparse.eval, nodeValue1356, nodeValue2856, nodeValue2911, nodeValue2970, nodeValue3025, nodeValue4088]

theorem reindexCheck1246 : Integer.Sparse.reindex keyMap MixedData.row1246 = numericRow1246 := by decide +kernel

theorem numericCheck1246 (x : Master → ℝ) : Integer.Sparse.eval numericRow1246 x =
    (1 : ℝ) * reducedSource1246 x := by
  norm_num [numericRow1246, reducedSource1246, Integer.Sparse.eval, Sparse.eval, nodeValue1133, nodeValue1143, nodeValue1146, nodeValue1245, nodeValue2522, nodeValue4084]

theorem reindexCheck1247 : Integer.Sparse.reindex keyMap MixedData.row1247 = numericRow1247 := by decide +kernel

theorem numericCheck1247 (x : Master → ℝ) : Integer.Sparse.eval numericRow1247 x =
    (1 : ℝ) * reducedSource1247 x := by
  norm_num [numericRow1247, reducedSource1247, Integer.Sparse.eval, Sparse.eval, nodeValue653, nodeValue1171, nodeValue1273, nodeValue1294, nodeValue1306, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1234 (mixedVector B) = 0 := by
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1439, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4058, h4060, h4061, h4064, h4066, h4067, h4069, h4070, h4071, h4072, h4081, h4084, h4085, reducedSource1234] using sourceEq1439 B hB

theorem rowSound1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1234 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1234, numericCheck1234, reducedZero1234 B hB hF, mul_zero]

theorem reducedZero1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1235 (mixedVector B) = 0 := by
  have h616 : mixedVector B (Sum.inr 616) = Sparse.eval nodeValue616 (mixedVector B) := by
    change mixedMoment B node616 node616Labels = _
    exact sound616 B hB hF
  have h935 : mixedVector B (Sum.inr 935) = Sparse.eval nodeValue935 (mixedVector B) := by
    change mixedMoment B node935 node935Labels = _
    exact sound935 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1440, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h616, h935, h1063, h1083, h1087, h4084, reducedSource1235] using sourceEq1440 B hB

theorem rowSound1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1235 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1235, numericCheck1235, reducedZero1235 B hB hF, mul_zero]

theorem reducedZero1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1236 (mixedVector B) = 0 := by
  have h1318 : mixedVector B (Sum.inr 1318) = Sparse.eval nodeValue1318 (mixedVector B) := by
    change mixedMoment B node1318 node1318Labels = _
    exact sound1318 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1441, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1318, h1324, h1325, h1375, h2889, h4092, reducedSource1236] using sourceEq1441 B hB

theorem rowSound1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1236 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1236, numericCheck1236, reducedZero1236 B hB hF, mul_zero]

theorem reducedZero1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1237 (mixedVector B) = 0 := by
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1443, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1736, h1738, h1740, h1751, h3301, h4071, reducedSource1237] using sourceEq1443 B hB

theorem rowSound1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1237 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1237, numericCheck1237, reducedZero1237 B hB hF, mul_zero]

theorem reducedZero1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1238 (mixedVector B) = 0 := by
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h1626 : mixedVector B (Sum.inr 1626) = Sparse.eval nodeValue1626 (mixedVector B) := by
    change mixedMoment B node1626 node1626Labels = _
    exact sound1626 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1444, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h858, h1626, h1740, h1751, h4071, reducedSource1238] using sourceEq1444 B hB

theorem rowSound1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1238 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1238, numericCheck1238, reducedZero1238 B hB hF, mul_zero]

theorem reducedZero1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1239 (mixedVector B) = 0 := by
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h1611 : mixedVector B (Sum.inr 1611) = Sparse.eval nodeValue1611 (mixedVector B) := by
    change mixedMoment B node1611 node1611Labels = _
    exact sound1611 B hB hF
  have h1660 : mixedVector B (Sum.inr 1660) = Sparse.eval nodeValue1660 (mixedVector B) := by
    change mixedMoment B node1660 node1660Labels = _
    exact sound1660 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1445, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h830, h1611, h1660, h1738, h1740, h4071, reducedSource1239] using sourceEq1445 B hB

theorem rowSound1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1239 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1239, numericCheck1239, reducedZero1239 B hB hF, mul_zero]

theorem reducedZero1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1240 (mixedVector B) = 0 := by
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h586, h910, h950, h1026, h1041, h1044, h4083, reducedSource1240] using sourceEq1448 B hB

theorem rowSound1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1240 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1240, numericCheck1240, reducedZero1240 B hB hF, mul_zero]

theorem reducedZero1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1241 (mixedVector B) = 0 := by
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1449, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1328, h1333, h1334, h1338, h1391, h2931, h4091, reducedSource1241] using sourceEq1449 B hB

theorem rowSound1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1241 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1241, numericCheck1241, reducedZero1241 B hB hF, mul_zero]

theorem reducedZero1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1242 (mixedVector B) = 0 := by
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h2397 : mixedVector B (Sum.inr 2397) = Sparse.eval nodeValue2397 (mixedVector B) := by
    change mixedMoment B node2397 node2397Labels = _
    exact sound2397 B hB hF
  have h3280 : mixedVector B (Sum.inr 3280) = Sparse.eval nodeValue3280 (mixedVector B) := by
    change mixedMoment B node3280 node3280Labels = _
    exact sound3280 B hB hF
  have h3284 : mixedVector B (Sum.inr 3284) = Sparse.eval nodeValue3284 (mixedVector B) := by
    change mixedMoment B node3284 node3284Labels = _
    exact sound3284 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1450, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1736, h2397, h3280, h3284, h3301, h4071, reducedSource1242] using sourceEq1450 B hB

theorem rowSound1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1242 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1242, numericCheck1242, reducedZero1242 B hB hF, mul_zero]

theorem reducedZero1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1243 (mixedVector B) = 0 := by
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h1614 : mixedVector B (Sum.inr 1614) = Sparse.eval nodeValue1614 (mixedVector B) := by
    change mixedMoment B node1614 node1614Labels = _
    exact sound1614 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1452, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h848, h1614, h1736, h1751, h4071, reducedSource1243] using sourceEq1452 B hB

theorem rowSound1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1243 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1243, numericCheck1243, reducedZero1243 B hB hF, mul_zero]

theorem reducedZero1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1244 (mixedVector B) = 0 := by
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1655 : mixedVector B (Sum.inr 1655) = Sparse.eval nodeValue1655 (mixedVector B) := by
    change mixedMoment B node1655 node1655Labels = _
    exact sound1655 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h823, h1606, h1655, h1736, h1738, h4071, reducedSource1244] using sourceEq1453 B hB

theorem rowSound1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1244 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1244, numericCheck1244, reducedZero1244 B hB hF, mul_zero]

theorem reducedZero1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1245 (mixedVector B) = 0 := by
  have h1356 : mixedVector B (Sum.inr 1356) = Sparse.eval nodeValue1356 (mixedVector B) := by
    change mixedMoment B node1356 node1356Labels = _
    exact sound1356 B hB hF
  have h2856 : mixedVector B (Sum.inr 2856) = Sparse.eval nodeValue2856 (mixedVector B) := by
    change mixedMoment B node2856 node2856Labels = _
    exact sound2856 B hB hF
  have h2911 : mixedVector B (Sum.inr 2911) = Sparse.eval nodeValue2911 (mixedVector B) := by
    change mixedMoment B node2911 node2911Labels = _
    exact sound2911 B hB hF
  have h2970 : mixedVector B (Sum.inr 2970) = Sparse.eval nodeValue2970 (mixedVector B) := by
    change mixedMoment B node2970 node2970Labels = _
    exact sound2970 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1356, h2856, h2911, h2970, h3025, h4088, reducedSource1245] using sourceEq1455 B hB

theorem rowSound1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1245 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1245, numericCheck1245, reducedZero1245 B hB hF, mul_zero]

theorem reducedZero1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1246 (mixedVector B) = 0 := by
  have h1133 : mixedVector B (Sum.inr 1133) = Sparse.eval nodeValue1133 (mixedVector B) := by
    change mixedMoment B node1133 node1133Labels = _
    exact sound1133 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1146 : mixedVector B (Sum.inr 1146) = Sparse.eval nodeValue1146 (mixedVector B) := by
    change mixedMoment B node1146 node1146Labels = _
    exact sound1146 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1457, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1133, h1143, h1146, h1245, h2522, h4084, reducedSource1246] using sourceEq1457 B hB

theorem rowSound1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1246 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1246, numericCheck1246, reducedZero1246 B hB hF, mul_zero]

theorem reducedZero1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1247 (mixedVector B) = 0 := by
  have h653 : mixedVector B (Sum.inr 653) = Sparse.eval nodeValue653 (mixedVector B) := by
    change mixedMoment B node653 node653Labels = _
    exact sound653 B hB hF
  have h1171 : mixedVector B (Sum.inr 1171) = Sparse.eval nodeValue1171 (mixedVector B) := by
    change mixedMoment B node1171 node1171Labels = _
    exact sound1171 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h653, h1171, h1273, h1294, h1306, h4092, reducedSource1247] using sourceEq1458 B hB

theorem rowSound1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1247 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1247, numericCheck1247, reducedZero1247 B hB hF, mul_zero]

theorem sourceRowsAt1232 : MixedData.sourceRows (1232 : Fin 2425) =
    MixedData.row1232 := by decide +kernel

theorem sourceRowsAt1233 : MixedData.sourceRows (1233 : Fin 2425) =
    MixedData.row1233 := by decide +kernel

theorem sourceRowsAt1234 : MixedData.sourceRows (1234 : Fin 2425) =
    MixedData.row1234 := by decide +kernel

theorem sourceRowsAt1235 : MixedData.sourceRows (1235 : Fin 2425) =
    MixedData.row1235 := by decide +kernel

theorem sourceRowsAt1236 : MixedData.sourceRows (1236 : Fin 2425) =
    MixedData.row1236 := by decide +kernel

theorem sourceRowsAt1237 : MixedData.sourceRows (1237 : Fin 2425) =
    MixedData.row1237 := by decide +kernel

theorem sourceRowsAt1238 : MixedData.sourceRows (1238 : Fin 2425) =
    MixedData.row1238 := by decide +kernel

theorem sourceRowsAt1239 : MixedData.sourceRows (1239 : Fin 2425) =
    MixedData.row1239 := by decide +kernel

theorem sourceRowsAt1240 : MixedData.sourceRows (1240 : Fin 2425) =
    MixedData.row1240 := by decide +kernel

theorem sourceRowsAt1241 : MixedData.sourceRows (1241 : Fin 2425) =
    MixedData.row1241 := by decide +kernel

theorem sourceRowsAt1242 : MixedData.sourceRows (1242 : Fin 2425) =
    MixedData.row1242 := by decide +kernel

theorem sourceRowsAt1243 : MixedData.sourceRows (1243 : Fin 2425) =
    MixedData.row1243 := by decide +kernel

theorem sourceRowsAt1244 : MixedData.sourceRows (1244 : Fin 2425) =
    MixedData.row1244 := by decide +kernel

theorem sourceRowsAt1245 : MixedData.sourceRows (1245 : Fin 2425) =
    MixedData.row1245 := by decide +kernel

theorem sourceRowsAt1246 : MixedData.sourceRows (1246 : Fin 2425) =
    MixedData.row1246 := by decide +kernel

theorem sourceRowsAt1247 : MixedData.sourceRows (1247 : Fin 2425) =
    MixedData.row1247 := by decide +kernel

theorem chunkSound77_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 77) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1232 ∨ k.val = 1233 ∨ k.val = 1234 ∨ k.val = 1235 ∨ k.val = 1236 ∨ k.val = 1237 ∨ k.val = 1238 ∨ k.val = 1239 ∨ k.val = 1240 ∨ k.val = 1241 ∨ k.val = 1242 ∨ k.val = 1243 ∨ k.val = 1244 ∨ k.val = 1245 ∨ k.val = 1246 ∨ k.val = 1247 := by omega
  rcases heq with h1232 | h1233 | h1234 | h1235 | h1236 | h1237 | h1238 | h1239 | h1240 | h1241 | h1242 | h1243 | h1244 | h1245 | h1246 | h1247
  · have he : k = (1232 : Fin 2425) := Fin.ext h1232
    subst k
    rw [sourceRowsAt1232]
    exact rowSound1232_e B hB hF
  · have he : k = (1233 : Fin 2425) := Fin.ext h1233
    subst k
    rw [sourceRowsAt1233]
    exact rowSound1233_e B hB hF
  · have he : k = (1234 : Fin 2425) := Fin.ext h1234
    subst k
    rw [sourceRowsAt1234]
    exact rowSound1234 B hB hF
  · have he : k = (1235 : Fin 2425) := Fin.ext h1235
    subst k
    rw [sourceRowsAt1235]
    exact rowSound1235 B hB hF
  · have he : k = (1236 : Fin 2425) := Fin.ext h1236
    subst k
    rw [sourceRowsAt1236]
    exact rowSound1236 B hB hF
  · have he : k = (1237 : Fin 2425) := Fin.ext h1237
    subst k
    rw [sourceRowsAt1237]
    exact rowSound1237 B hB hF
  · have he : k = (1238 : Fin 2425) := Fin.ext h1238
    subst k
    rw [sourceRowsAt1238]
    exact rowSound1238 B hB hF
  · have he : k = (1239 : Fin 2425) := Fin.ext h1239
    subst k
    rw [sourceRowsAt1239]
    exact rowSound1239 B hB hF
  · have he : k = (1240 : Fin 2425) := Fin.ext h1240
    subst k
    rw [sourceRowsAt1240]
    exact rowSound1240 B hB hF
  · have he : k = (1241 : Fin 2425) := Fin.ext h1241
    subst k
    rw [sourceRowsAt1241]
    exact rowSound1241 B hB hF
  · have he : k = (1242 : Fin 2425) := Fin.ext h1242
    subst k
    rw [sourceRowsAt1242]
    exact rowSound1242 B hB hF
  · have he : k = (1243 : Fin 2425) := Fin.ext h1243
    subst k
    rw [sourceRowsAt1243]
    exact rowSound1243 B hB hF
  · have he : k = (1244 : Fin 2425) := Fin.ext h1244
    subst k
    rw [sourceRowsAt1244]
    exact rowSound1244 B hB hF
  · have he : k = (1245 : Fin 2425) := Fin.ext h1245
    subst k
    rw [sourceRowsAt1245]
    exact rowSound1245 B hB hF
  · have he : k = (1246 : Fin 2425) := Fin.ext h1246
    subst k
    rw [sourceRowsAt1246]
    exact rowSound1246 B hB hF
  · have he : k = (1247 : Fin 2425) := Fin.ext h1247
    subst k
    rw [sourceRowsAt1247]
    exact rowSound1247 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e_oai
