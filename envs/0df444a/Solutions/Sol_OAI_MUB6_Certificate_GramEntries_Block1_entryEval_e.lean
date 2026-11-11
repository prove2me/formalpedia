-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:46:30.692215+00:00
-- url     : https://prove2.me/submissions/cc90ddbc-3bb7-48e7-a809-9c90deae590e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow8_e

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

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
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
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
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AuxiliaryGram
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Auxiliary-column Gram matrices

The functions in manuscript §4 are interpreted, with the same sampled
column in all factors. Real Gram forms are nonnegative for any real positive
semidefinite coefficient matrix. No numerical certificate is assumed here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

section RealGram
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

lemma realGram_sum_left (F : ι → Ω → ℂ) (G : Ω → ℂ) :
    realGram (fun ω => ∑ i, F i ω) G = ∑ i, realGram (F i) G := by
  simp only [realGram, Finset.sum_mul, Complex.re_sum, average_sum]

lemma realGram_sum_right (F : Ω → ℂ) (G : ι → Ω → ℂ) :
    realGram F (fun ω => ∑ i, G i ω) = ∑ i, realGram F (G i) := by
  simp only [realGram, map_sum, Finset.mul_sum, Complex.re_sum, average_sum]

lemma realGram_smul_left (c : ℝ) (F G : Ω → ℂ) :
    realGram (fun ω => (c : ℂ) * F ω) G = c * realGram F G := by
  simp only [realGram, mul_assoc, Complex.re_ofReal_mul, average_mul]

lemma realGram_smul_right (c : ℝ) (F G : Ω → ℂ) :
    realGram F (fun ω => (c : ℂ) * G ω) = c * realGram F G := by
  simp only [realGram, map_mul, Complex.conj_ofReal]
  simp_rw [mul_left_comm (F _) (c : ℂ), Complex.re_ofReal_mul]
  exact average_mul c _

lemma realGram_weighted_sum {κ : Type*} [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (F : ι → Ω → ℂ) (G : κ → Ω → ℂ) :
    realGram (fun ω => ∑ i, (c i : ℂ) * F i ω)
      (fun ω => ∑ j, (d j : ℂ) * G j ω) =
        ∑ i, ∑ j, c i * d j * realGram (F i) (G j) := by
  simp only [realGram_sum_left, realGram_sum_right, realGram_smul_left,
    realGram_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

lemma realGram_symm (F G : Ω → ℂ) : realGram F G = realGram G F := by
  apply average_congr
  intro ω
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end RealGram

lemma average_column_re (f : Coord → ℂ) :
    average (fun k => (f k).re) = ((6 : ℂ)⁻¹ * ∑ k, f k).re := by
  norm_num [average, Complex.mul_re, Complex.re_sum]

lemma auxiliaryCharacter_product (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a v : Charge) (ω : AuxiliarySample) :
    auxiliaryCharacter B (-a) ω * conj (auxiliaryCharacter B (-v) ω) =
      auxiliaryCharacter B (v - a) ω := by
  let x : Coord → ℂ := fun i => relativeMatrix B ω.1 (ω.2.2.1 0) (ω.2.1 i) ω.2.2.2
  have hx (i : Coord) : Complex.normSq (x i) = 1 :=
    (relativeMatrix_isHadamard B hB ω.1 _).1 _ _
  change character x (-a) * conj (character x (-v)) = character x (v - a)
  rw [character_neg x hx v, Complex.conj_conj, sub_eq_add_neg,
    character_add x (fun i => unit_ne_zero (hx i))]
  ring

lemma elementaryAuxiliary_product (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) (ω : AuxiliarySample) :
    elementaryAuxiliary B s a ω * conj (elementaryAuxiliary B t v ω) =
      rowFourier (relativeMatrix B ω.1 (ω.2.2.1 s)) ω.2.1 a *
      rowFourier (relativeMatrix B ω.1 (ω.2.2.1 t)) ω.2.1 (-v) *
      auxiliaryCharacter B (v - a) ω := by
  simp only [elementaryAuxiliary, map_mul]
  rw [← rowFourier_neg (relativeMatrix_isHadamard B hB ω.1 _) ω.2.1 v]
  have h := auxiliaryCharacter_product B hB a v ω
  calc
    _ = (rowFourier (relativeMatrix B ω.1 (ω.2.2.1 s)) ω.2.1 a *
        rowFourier (relativeMatrix B ω.1 (ω.2.2.1 t)) ω.2.1 (-v)) *
        (auxiliaryCharacter B (-a) ω * conj (auxiliaryCharacter B (-v) ω)) := by ring
    _ = _ := by rw [h]

lemma elementaryAuxiliary_column_average (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) (r : Fin 7) (ρ τ : Coord ↪ Coord) :
    average (fun k => (elementaryAuxiliary B s a (r, ρ, τ, k) *
      conj (elementaryAuxiliary B t v (r, ρ, τ, k))).re) =
      (rowFourier (relativeMatrix B r (τ s)) ρ a *
        rowFourier (relativeMatrix B r (τ t)) ρ (-v) *
        rowFourier (relativeMatrix B r (τ 0)) ρ (v - a)).re := by
  simp_rw [elementaryAuxiliary_product B hB]
  rw [average_column_re]
  simp only [auxiliaryCharacter, rowFourier, character]
  rw [← Finset.mul_sum]
  congr 1
  ring

/-- Integrating out the common column gives a three-factor mixed moment. -/
theorem elementaryAuxiliary_gram (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) :
    realGram (elementaryAuxiliary B s a) (elementaryAuxiliary B t v) =
      mixedMoment B (gramCharges a v) (gramLabels s t) := by
  simp only [realGram, average_prod]
  unfold mixedMoment
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  rw [elementaryAuxiliary_column_average B hB]
  change _ = (mixedIntegrand B (tripleCharges a (-v) (v - a)) ![s, t, 0] r ρ τ).re
  rw [mixedIntegrand_three]
  rfl

private lemma pair_labels_relabel (B : Fin 7 → Basis) (a v : Charge)
    (q : Fin 3 → Fin 2) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (pairLabelEmbedding s ∘ q) =
      mixedMoment B (gramCharges a v) (pairLabelEmbedding 0 ∘ q) :=
  (mixedMoment_label_embedding (by decide) B _ (pairLabelEmbedding s) q).trans
    (mixedMoment_label_embedding (by decide) B _ (pairLabelEmbedding 0) q).symm

lemma gramMoment_zero_succ (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels 0 s.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 0 1) := by
  have h := pair_labels_relabel B a v ![1, 0, 1] s
  have hs : pairLabelEmbedding s ∘ ![1, 0, 1] = gramLabels 0 s.succ := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![1, 0, 1] = gramLabels 0 1 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_zero (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ 0) =
      mixedMoment B (gramCharges a v) (gramLabels 1 0) := by
  have h := pair_labels_relabel B a v ![0, 1, 1] s
  have hs : pairLabelEmbedding s ∘ ![0, 1, 1] = gramLabels s.succ 0 := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![0, 1, 1] = gramLabels 1 0 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_self (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ s.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 1 1) := by
  have h := pair_labels_relabel B a v ![0, 0, 1] s
  have hs : pairLabelEmbedding s ∘ ![0, 0, 1] = gramLabels s.succ s.succ := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![0, 0, 1] = gramLabels 1 1 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_distinct (B : Fin 7 → Basis) (a v : Charge) (s t : Fin 5)
    (hst : s ≠ t) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ t.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
  have h := mixedMoment_label_embedding (by decide) B (gramCharges a v)
    (tripleLabelEmbedding s t hst) id
  have h0 := mixedMoment_label_embedding (by decide) B (gramCharges a v)
    (tripleLabelEmbedding 0 1 (by decide)) id
  exact h.trans h0.symm

lemma auxiliaryF_zero (B : Fin 7 → Basis) (a : Charge) :
    auxiliaryF B 0 a = elementaryAuxiliary B 0 a := by simp [auxiliaryF]

lemma auxiliaryF_one (B : Fin 7 → Basis) (a : Charge) :
    auxiliaryF B 1 a = fun ω => (((5 : ℝ)⁻¹ : ℝ) : ℂ) *
      ∑ s : Fin 5, elementaryAuxiliary B s.succ a ω := by
  simp [auxiliaryF]

/-- The `(0,0)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_zero_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 0 a) (auxiliaryF B 0 v) =
      mixedMoment B (gramCharges a v) (gramLabels 0 0) := by
  rw [auxiliaryF_zero, auxiliaryF_zero, elementaryAuxiliary_gram B hB]

/-- The `(0,1)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_zero_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 0 a) (auxiliaryF B 1 v) =
      mixedMoment B (gramCharges a v) (gramLabels 0 1) := by
  rw [auxiliaryF_zero, auxiliaryF_one, realGram_smul_right, realGram_sum_right]
  simp_rw [elementaryAuxiliary_gram B hB, gramMoment_zero_succ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The `(1,0)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_one_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 1 a) (auxiliaryF B 0 v) =
      mixedMoment B (gramCharges a v) (gramLabels 1 0) := by
  rw [auxiliaryF_one, auxiliaryF_zero, realGram_smul_left, realGram_sum_left]
  simp_rw [elementaryAuxiliary_gram B hB, gramMoment_succ_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma five_by_five_same_different (A C : ℝ) :
    (∑ s : Fin 5, ∑ t : Fin 5, if s = t then A else C) = 5 * A + 20 * C := by
  have h (s t : Fin 5) : (if s = t then A else C) = (if s = t then A - C else 0) + C := by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib]
  simp
  ring

/-- Five diagonal and twenty off-diagonal choices produce the exact `1/5`
and `4/5` coefficients in the `(1,1)` Gram entry. -/
theorem auxiliaryGram_one_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 1 a) (auxiliaryF B 1 v) =
      (1 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 1) +
      (4 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
  rw [auxiliaryF_one, auxiliaryF_one, realGram_smul_left, realGram_smul_right,
    realGram_sum_left]
  simp_rw [realGram_sum_right, elementaryAuxiliary_gram B hB]
  have h (s t : Fin 5) : mixedMoment B (gramCharges a v) (gramLabels s.succ t.succ) =
      if s = t then mixedMoment B (gramCharges a v) (gramLabels 1 1)
      else mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
    by_cases hst : s = t
    · subst t
      rw [ite_eq_left rfl]
      exact gramMoment_succ_self B a v s
    · rw [ite_eq_right hst]
      exact gramMoment_succ_distinct B a v s t hst
  simp_rw [h]
  rw [five_by_five_same_different]
  ring

/-- A uniform statement of all three entries other than `(1,1)`. -/
theorem auxiliaryGram_other (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (hst : ¬ (s = 1 ∧ t = 1)) (a v : Charge) :
    realGram (auxiliaryF B s a) (auxiliaryF B t v) =
      mixedMoment B (gramCharges a v)
        (gramLabels (Fin.castLE (by decide : 2 ≤ 6) s) (Fin.castLE (by decide : 2 ≤ 6) t)) := by
  fin_cases s <;> fin_cases t
  · exact auxiliaryGram_zero_zero B hB a v
  · exact auxiliaryGram_zero_one B hB a v
  · exact auxiliaryGram_one_zero B hB a v
  · exact (hst ⟨rfl, rfl⟩).elim

theorem auxiliaryGram_eq (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    realGram (auxiliaryF B s a) (auxiliaryF B t v) =
      auxiliaryMixedEntry B s t a v := by
  unfold auxiliaryMixedEntry
  split_ifs with hst
  · rcases hst with ⟨rfl, rfl⟩
    exact auxiliaryGram_one_one B hB a v
  · exact auxiliaryGram_other B hB s t hst a v

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_AuxiliaryInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interpreting the certificate's expanded auxiliary functions

The integer tagged terms are ordinary finite linear combinations of the
manuscript's two auxiliary functions. Their real Gram products expand into
the exact mixed-moment expressions used by the certificate. Positive
semidefiniteness of a coefficient matrix proves nonnegativity independently
of how its entries or its finite lists of terms were obtained.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramFunctions

theorem LinearForm.auxiliaryEval_gram (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    realGram (P.auxiliaryEval B) (Q.auxiliaryEval B) = P.mixedGram Q B := by
  unfold LinearForm.auxiliaryEval LinearForm.eval LinearForm.mixedGram
  have hcast (z : ℤ) : (z : ℂ) = ((z : ℝ) : ℂ) := by norm_cast
  simp_rw [hcast]
  rw [realGram_weighted_sum]
  simp_rw [auxiliaryGram_eq B hB]

end MUB6.Certificate.GramFunctions

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

theorem orderedKey_leftCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).leftCharge = a ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.leftCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem orderedKey_rightCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).rightCharge = v ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.rightCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem auxiliaryMixedEntry_row_permutation (B : Fin 7 → Basis)
    (s t : Fin 2) (a v : Charge) (π : Equiv.Perm Coord) :
    auxiliaryMixedEntry B s t (a ∘ π) (v ∘ π) = auxiliaryMixedEntry B s t a v := by
  have h : gramCharges (a ∘ π) (v ∘ π) = fun i j => gramCharges a v (π i) j := rfl
  simp only [auxiliaryMixedEntry, h, mixedMoment_row_permutation]

theorem auxiliaryMixedEntry_symm (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    auxiliaryMixedEntry B s t a v = auxiliaryMixedEntry B t s v a := by
  rw [← auxiliaryGram_eq B hB, ← auxiliaryGram_eq B hB, realGram_symm]

theorem eval_orderedKey (B : Fin 7 → Basis) (s t : Fin 2) (a v : Charge) :
    eval B (orderedKey s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold eval
  rw [orderedKey_leftCharge, orderedKey_rightCharge]
  exact auxiliaryMixedEntry_row_permutation B s t a v (rowPermutation a v)

theorem eval_normalize (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    eval B (normalize s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold normalize
  split <;> rw [eval_orderedKey]
  exact auxiliaryMixedEntry_symm B hB t s v a

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramPolynomial
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite auxiliary Gram products interpreted as sparse normalized keys. -/
namespace MUB6.Certificate.GramPolynomial

open GramFunctions GramNormalization
open scoped BigOperators

theorem normalizedRow_eval (s : Fin 2) (a : Charge) (Q : LinearForm)
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (normalizedRow s a Q) (GramNormalization.eval B) =
      ∑ j, ((Q.terms j).coefficient : ℝ) *
        auxiliaryMixedEntry B s (Q.terms j).tag a (Q.terms j).charge := by
  simp [normalizedRow, Integer.Sparse.eval, List.map_ofFn, List.sum_ofFn,
    GramNormalization.eval_normalize B hB]

theorem mixedGram_eq_rows (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    P.mixedGram Q B = ∑ i, ((P.terms i).coefficient : ℝ) *
      Integer.Sparse.eval (normalizedRow (P.terms i).tag (P.terms i).charge Q)
        (GramNormalization.eval B) := by
  simp_rw [normalizedRow_eval _ _ _ B hB, Finset.mul_sum]
  unfold LinearForm.mixedGram
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mixedGram_symm (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) : P.mixedGram Q B = Q.mixedGram P B := by
  rw [← LinearForm.auxiliaryEval_gram P Q B hB,
    ← LinearForm.auxiliaryEval_gram Q P B hB, realGram_symm]

theorem collectWeightedRows_eval {n : ℕ} (rows : Fin n → Integer.Sparse Key)
    (weights : Fin n → ℤ) (x : Key → ℝ) :
    Integer.Sparse.eval
      (Integer.Sparse.collectLevels keyLess n
        (List.ofFn fun i => Integer.Sparse.scale (weights i) (rows i))) x =
      ∑ i, (weights i : ℝ) * Integer.Sparse.eval (rows i) x := by
  rw [Integer.Sparse.eval_collectLevels]
  simp [List.map_ofFn, List.sum_ofFn]

end MUB6.Certificate.GramPolynomial

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1890 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form9 = rawRow1890 := by decide +kernel

theorem rowCheck1890 : row1890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1890 := by decide +kernel

theorem rowEval1890 (x : Key → ℝ) : Integer.Sparse.eval row1890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1890, Integer.Sparse.eval_collectBalanced, rawRowCheck1890]

theorem rawRowCheck1891 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form9 = rawRow1891 := by decide +kernel

theorem rowCheck1891 : row1891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1891 := by decide +kernel

theorem rowEval1891 (x : Key → ℝ) : Integer.Sparse.eval row1891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1891, Integer.Sparse.eval_collectBalanced, rawRowCheck1891]

theorem rawRowCheck1892 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form9 = rawRow1892 := by decide +kernel

theorem rowCheck1892 : row1892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1892 := by decide +kernel

theorem rowEval1892 (x : Key → ℝ) : Integer.Sparse.eval row1892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1892, Integer.Sparse.eval_collectBalanced, rawRowCheck1892]

theorem rawRowCheck1893 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow1893 := by decide +kernel

theorem rowCheck1893 : row1893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1893 := by decide +kernel

theorem rowEval1893 (x : Key → ℝ) : Integer.Sparse.eval row1893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1893, Integer.Sparse.eval_collectBalanced, rawRowCheck1893]

theorem rawRowCheck1894 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form9 = rawRow1894 := by decide +kernel

theorem rowCheck1894 : row1894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1894 := by decide +kernel

theorem rowEval1894 (x : Key → ℝ) : Integer.Sparse.eval row1894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck1894, Integer.Sparse.eval_collectBalanced, rawRowCheck1894]

theorem rawRowCheck1895 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form9 = rawRow1895 := by decide +kernel

theorem rowCheck1895 : row1895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1895 := by decide +kernel

theorem rowEval1895 (x : Key → ℝ) : Integer.Sparse.eval row1895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1895, Integer.Sparse.eval_collectBalanced, rawRowCheck1895]

theorem rawRowCheck1896 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form9 = rawRow1896 := by decide +kernel

theorem rowCheck1896 : row1896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1896 := by decide +kernel

theorem rowEval1896 (x : Key → ℝ) : Integer.Sparse.eval row1896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1896, Integer.Sparse.eval_collectBalanced, rawRowCheck1896]

theorem rawRowCheck1897 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form9 = rawRow1897 := by decide +kernel

theorem rowCheck1897 : row1897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1897 := by decide +kernel

theorem rowEval1897 (x : Key → ℝ) : Integer.Sparse.eval row1897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1897, Integer.Sparse.eval_collectBalanced, rawRowCheck1897]

theorem rawRowCheck1898 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form9 = rawRow1898 := by decide +kernel

theorem rowCheck1898 : row1898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1898 := by decide +kernel

theorem rowEval1898 (x : Key → ℝ) : Integer.Sparse.eval row1898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1898, Integer.Sparse.eval_collectBalanced, rawRowCheck1898]

theorem rawRowCheck1899 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form9 = rawRow1899 := by decide +kernel

theorem rowCheck1899 : row1899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1899 := by decide +kernel

theorem rowEval1899 (x : Key → ℝ) : Integer.Sparse.eval row1899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck1899, Integer.Sparse.eval_collectBalanced, rawRowCheck1899]

theorem rawRowCheck1900 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form9 = rawRow1900 := by decide +kernel

theorem rowCheck1900 : row1900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1900 := by decide +kernel

theorem rowEval1900 (x : Key → ℝ) : Integer.Sparse.eval row1900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1900, Integer.Sparse.eval_collectBalanced, rawRowCheck1900]

theorem rawRowCheck1901 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form9 = rawRow1901 := by decide +kernel

theorem rowCheck1901 : row1901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1901 := by decide +kernel

theorem rowEval1901 (x : Key → ℝ) : Integer.Sparse.eval row1901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1901, Integer.Sparse.eval_collectBalanced, rawRowCheck1901]

theorem rawRowCheck1902 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form9 = rawRow1902 := by decide +kernel

theorem rowCheck1902 : row1902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1902 := by decide +kernel

theorem rowEval1902 (x : Key → ℝ) : Integer.Sparse.eval row1902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck1902, Integer.Sparse.eval_collectBalanced, rawRowCheck1902]

theorem rawRowCheck1903 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form9 = rawRow1903 := by decide +kernel

theorem rowCheck1903 : row1903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1903 := by decide +kernel

theorem rowEval1903 (x : Key → ℝ) : Integer.Sparse.eval row1903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck1903, Integer.Sparse.eval_collectBalanced, rawRowCheck1903]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval1890 x
  · exact rowEval1891 x
  · exact rowEval1892 x
  · exact rowEval1893 x
  · exact rowEval1894 x
  · exact rowEval1895 x
  · exact rowEval1896 x
  · exact rowEval1897 x
  · exact rowEval1898 x
  · exact rowEval1899 x
  · exact rowEval1900 x
  · exact rowEval1901 x
  · exact rowEval1902 x
  · exact rowEval1903 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2044 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2044 := by decide +kernel

theorem rowCheck2044 : row2044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2044 := by decide +kernel

theorem rowEval2044 (x : Key → ℝ) : Integer.Sparse.eval row2044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2044, Integer.Sparse.eval_collectBalanced, rawRowCheck2044]

theorem rawRowCheck2045 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2045 := by decide +kernel

theorem rowCheck2045 : row2045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2045 := by decide +kernel

theorem rowEval2045 (x : Key → ℝ) : Integer.Sparse.eval row2045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2045, Integer.Sparse.eval_collectBalanced, rawRowCheck2045]

theorem rawRowCheck2046 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2046 := by decide +kernel

theorem rowCheck2046 : row2046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2046 := by decide +kernel

theorem rowEval2046 (x : Key → ℝ) : Integer.Sparse.eval row2046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2046, Integer.Sparse.eval_collectBalanced, rawRowCheck2046]

theorem rawRowCheck2047 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2047 := by decide +kernel

theorem rowCheck2047 : row2047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2047 := by decide +kernel

theorem rowEval2047 (x : Key → ℝ) : Integer.Sparse.eval row2047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2047, Integer.Sparse.eval_collectBalanced, rawRowCheck2047]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2048 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2048 := by decide +kernel

theorem rowCheck2048 : row2048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2048 := by decide +kernel

theorem rowEval2048 (x : Key → ℝ) : Integer.Sparse.eval row2048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2048, Integer.Sparse.eval_collectBalanced, rawRowCheck2048]

theorem rawRowCheck2049 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2049 := by decide +kernel

theorem rowCheck2049 : row2049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2049 := by decide +kernel

theorem rowEval2049 (x : Key → ℝ) : Integer.Sparse.eval row2049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2049, Integer.Sparse.eval_collectBalanced, rawRowCheck2049]

theorem rawRowCheck2050 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2050 := by decide +kernel

theorem rowCheck2050 : row2050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2050 := by decide +kernel

theorem rowEval2050 (x : Key → ℝ) : Integer.Sparse.eval row2050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2050, Integer.Sparse.eval_collectBalanced, rawRowCheck2050]

theorem rawRowCheck2051 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form9 = rawRow2051 := by decide +kernel

theorem rowCheck2051 : row2051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2051 := by decide +kernel

theorem rowEval2051 (x : Key → ℝ) : Integer.Sparse.eval row2051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2051, Integer.Sparse.eval_collectBalanced, rawRowCheck2051]

theorem rawRowCheck2052 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form9 = rawRow2052 := by decide +kernel

theorem rowCheck2052 : row2052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2052 := by decide +kernel

theorem rowEval2052 (x : Key → ℝ) : Integer.Sparse.eval row2052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2052, Integer.Sparse.eval_collectBalanced, rawRowCheck2052]

theorem rawRowCheck2053 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form9 = rawRow2053 := by decide +kernel

theorem rowCheck2053 : row2053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2053 := by decide +kernel

theorem rowEval2053 (x : Key → ℝ) : Integer.Sparse.eval row2053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2053, Integer.Sparse.eval_collectBalanced, rawRowCheck2053]

theorem rawRowCheck2054 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2054 := by decide +kernel

theorem rowCheck2054 : row2054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2054 := by decide +kernel

theorem rowEval2054 (x : Key → ℝ) : Integer.Sparse.eval row2054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2054, Integer.Sparse.eval_collectBalanced, rawRowCheck2054]

theorem rawRowCheck2055 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form9 = rawRow2055 := by decide +kernel

theorem rowCheck2055 : row2055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2055 := by decide +kernel

theorem rowEval2055 (x : Key → ℝ) : Integer.Sparse.eval row2055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2055, Integer.Sparse.eval_collectBalanced, rawRowCheck2055]

theorem rawRowCheck2056 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form9 = rawRow2056 := by decide +kernel

theorem rowCheck2056 : row2056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2056 := by decide +kernel

theorem rowEval2056 (x : Key → ℝ) : Integer.Sparse.eval row2056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2056, Integer.Sparse.eval_collectBalanced, rawRowCheck2056]

theorem rawRowCheck2057 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form9 = rawRow2057 := by decide +kernel

theorem rowCheck2057 : row2057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2057 := by decide +kernel

theorem rowEval2057 (x : Key → ℝ) : Integer.Sparse.eval row2057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2057, Integer.Sparse.eval_collectBalanced, rawRowCheck2057]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2044 x
  · exact rowEval2045 x
  · exact rowEval2046 x
  · exact rowEval2047 x
  · exact rowEval2048 x
  · exact rowEval2049 x
  · exact rowEval2050 x
  · exact rowEval2051 x
  · exact rowEval2052 x
  · exact rowEval2053 x
  · exact rowEval2054 x
  · exact rowEval2055 x
  · exact rowEval2056 x
  · exact rowEval2057 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2602 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2602 := by decide +kernel

theorem rowCheck2602 : row2602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2602 := by decide +kernel

theorem rowEval2602 (x : Key → ℝ) : Integer.Sparse.eval row2602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2602, Integer.Sparse.eval_collectBalanced, rawRowCheck2602]

theorem rawRowCheck2603 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2603 := by decide +kernel

theorem rowCheck2603 : row2603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2603 := by decide +kernel

theorem rowEval2603 (x : Key → ℝ) : Integer.Sparse.eval row2603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2603, Integer.Sparse.eval_collectBalanced, rawRowCheck2603]

theorem rawRowCheck2604 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2604 := by decide +kernel

theorem rowCheck2604 : row2604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2604 := by decide +kernel

theorem rowEval2604 (x : Key → ℝ) : Integer.Sparse.eval row2604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2604, Integer.Sparse.eval_collectBalanced, rawRowCheck2604]

theorem rawRowCheck2605 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2605 := by decide +kernel

theorem rowCheck2605 : row2605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2605 := by decide +kernel

theorem rowEval2605 (x : Key → ℝ) : Integer.Sparse.eval row2605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2605, Integer.Sparse.eval_collectBalanced, rawRowCheck2605]

theorem rawRowCheck2606 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2606 := by decide +kernel

theorem rowCheck2606 : row2606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2606 := by decide +kernel

theorem rowEval2606 (x : Key → ℝ) : Integer.Sparse.eval row2606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2606, Integer.Sparse.eval_collectBalanced, rawRowCheck2606]

theorem rawRowCheck2607 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2607 := by decide +kernel

theorem rowCheck2607 : row2607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2607 := by decide +kernel

theorem rowEval2607 (x : Key → ℝ) : Integer.Sparse.eval row2607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2607, Integer.Sparse.eval_collectBalanced, rawRowCheck2607]

theorem rawRowCheck2608 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2608 := by decide +kernel

theorem rowCheck2608 : row2608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2608 := by decide +kernel

theorem rowEval2608 (x : Key → ℝ) : Integer.Sparse.eval row2608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2608, Integer.Sparse.eval_collectBalanced, rawRowCheck2608]

theorem rawRowCheck2609 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2609 := by decide +kernel

theorem rowCheck2609 : row2609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2609 := by decide +kernel

theorem rowEval2609 (x : Key → ℝ) : Integer.Sparse.eval row2609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2609, Integer.Sparse.eval_collectBalanced, rawRowCheck2609]

theorem rawRowCheck2610 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2610 := by decide +kernel

theorem rowCheck2610 : row2610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2610 := by decide +kernel

theorem rowEval2610 (x : Key → ℝ) : Integer.Sparse.eval row2610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2610, Integer.Sparse.eval_collectBalanced, rawRowCheck2610]

theorem rawRowCheck2611 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2611 := by decide +kernel

theorem rowCheck2611 : row2611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2611 := by decide +kernel

theorem rowEval2611 (x : Key → ℝ) : Integer.Sparse.eval row2611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2611, Integer.Sparse.eval_collectBalanced, rawRowCheck2611]

theorem rawRowCheck2612 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2612 := by decide +kernel

theorem rowCheck2612 : row2612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2612 := by decide +kernel

theorem rowEval2612 (x : Key → ℝ) : Integer.Sparse.eval row2612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2612, Integer.Sparse.eval_collectBalanced, rawRowCheck2612]

theorem rawRowCheck2613 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2613 := by decide +kernel

theorem rowCheck2613 : row2613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2613 := by decide +kernel

theorem rowEval2613 (x : Key → ℝ) : Integer.Sparse.eval row2613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2613, Integer.Sparse.eval_collectBalanced, rawRowCheck2613]

theorem rawRowCheck2614 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2614 := by decide +kernel

theorem rowCheck2614 : row2614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2614 := by decide +kernel

theorem rowEval2614 (x : Key → ℝ) : Integer.Sparse.eval row2614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2614, Integer.Sparse.eval_collectBalanced, rawRowCheck2614]

theorem rawRowCheck2615 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2615 := by decide +kernel

theorem rowCheck2615 : row2615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2615 := by decide +kernel

theorem rowEval2615 (x : Key → ℝ) : Integer.Sparse.eval row2615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2615, Integer.Sparse.eval_collectBalanced, rawRowCheck2615]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck13_9 : entry13_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_9 k)) := by decide +kernel

theorem rowsSound13_9 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2602 x
  · exact rowEval2603 x
  · exact rowEval2604 x
  · exact rowEval2605 x
  · exact rowEval2606 x
  · exact rowEval2607 x
  · exact rowEval2608 x
  · exact rowEval2609 x
  · exact rowEval2610 x
  · exact rowEval2611 x
  · exact rowEval2612 x
  · exact rowEval2613 x
  · exact rowEval2614 x
  · exact rowEval2615 x

theorem entryEval13_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_9 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck13_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_9]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4682 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4682 := by decide +kernel

theorem rowCheck4682 : row4682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4682 := by decide +kernel

theorem rowEval4682 (x : Key → ℝ) : Integer.Sparse.eval row4682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4682, Integer.Sparse.eval_collectBalanced, rawRowCheck4682]

theorem rawRowCheck4683 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4683 := by decide +kernel

theorem rowCheck4683 : row4683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4683 := by decide +kernel

theorem rowEval4683 (x : Key → ℝ) : Integer.Sparse.eval row4683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4683, Integer.Sparse.eval_collectBalanced, rawRowCheck4683]

theorem rawRowCheck4684 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4684 := by decide +kernel

theorem rowCheck4684 : row4684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4684 := by decide +kernel

theorem rowEval4684 (x : Key → ℝ) : Integer.Sparse.eval row4684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4684, Integer.Sparse.eval_collectBalanced, rawRowCheck4684]

theorem rawRowCheck4685 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4685 := by decide +kernel

theorem rowCheck4685 : row4685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4685 := by decide +kernel

theorem rowEval4685 (x : Key → ℝ) : Integer.Sparse.eval row4685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4685, Integer.Sparse.eval_collectBalanced, rawRowCheck4685]

theorem rawRowCheck4686 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4686 := by decide +kernel

theorem rowCheck4686 : row4686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4686 := by decide +kernel

theorem rowEval4686 (x : Key → ℝ) : Integer.Sparse.eval row4686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4686, Integer.Sparse.eval_collectBalanced, rawRowCheck4686]

theorem rawRowCheck4687 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4687 := by decide +kernel

theorem rowCheck4687 : row4687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4687 := by decide +kernel

theorem rowEval4687 (x : Key → ℝ) : Integer.Sparse.eval row4687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4687, Integer.Sparse.eval_collectBalanced, rawRowCheck4687]

theorem rawRowCheck4688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4688 := by decide +kernel

theorem rowCheck4688 : row4688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4688 := by decide +kernel

theorem rowEval4688 (x : Key → ℝ) : Integer.Sparse.eval row4688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4688, Integer.Sparse.eval_collectBalanced, rawRowCheck4688]

theorem rawRowCheck4689 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4689 := by decide +kernel

theorem rowCheck4689 : row4689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4689 := by decide +kernel

theorem rowEval4689 (x : Key → ℝ) : Integer.Sparse.eval row4689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4689, Integer.Sparse.eval_collectBalanced, rawRowCheck4689]

theorem rawRowCheck4690 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4690 := by decide +kernel

theorem rowCheck4690 : row4690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4690 := by decide +kernel

theorem rowEval4690 (x : Key → ℝ) : Integer.Sparse.eval row4690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4690, Integer.Sparse.eval_collectBalanced, rawRowCheck4690]

theorem rawRowCheck4691 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4691 := by decide +kernel

theorem rowCheck4691 : row4691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4691 := by decide +kernel

theorem rowEval4691 (x : Key → ℝ) : Integer.Sparse.eval row4691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4691, Integer.Sparse.eval_collectBalanced, rawRowCheck4691]

theorem rawRowCheck4692 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4692 := by decide +kernel

theorem rowCheck4692 : row4692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4692 := by decide +kernel

theorem rowEval4692 (x : Key → ℝ) : Integer.Sparse.eval row4692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4692, Integer.Sparse.eval_collectBalanced, rawRowCheck4692]

theorem rawRowCheck4693 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4693 := by decide +kernel

theorem rowCheck4693 : row4693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4693 := by decide +kernel

theorem rowEval4693 (x : Key → ℝ) : Integer.Sparse.eval row4693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4693, Integer.Sparse.eval_collectBalanced, rawRowCheck4693]

theorem rawRowCheck4694 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4694 := by decide +kernel

theorem rowCheck4694 : row4694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4694 := by decide +kernel

theorem rowEval4694 (x : Key → ℝ) : Integer.Sparse.eval row4694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4694, Integer.Sparse.eval_collectBalanced, rawRowCheck4694]

theorem rawRowCheck4695 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4695 := by decide +kernel

theorem rowCheck4695 : row4695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4695 := by decide +kernel

theorem rowEval4695 (x : Key → ℝ) : Integer.Sparse.eval row4695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4695, Integer.Sparse.eval_collectBalanced, rawRowCheck4695]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval4682 x
  · exact rowEval4683 x
  · exact rowEval4684 x
  · exact rowEval4685 x
  · exact rowEval4686 x
  · exact rowEval4687 x
  · exact rowEval4688 x
  · exact rowEval4689 x
  · exact rowEval4690 x
  · exact rowEval4691 x
  · exact rowEval4692 x
  · exact rowEval4693 x
  · exact rowEval4694 x
  · exact rowEval4695 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

theorem entryEvalRow9 (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 9 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 9).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval9_0_e B hB
  · exact entryEval9_1_e B hB
  · exact entryEval9_2_e B hB
  · exact entryEval9_3_e B hB
  · exact entryEval9_4_e B hB
  · exact entryEval9_5_e B hB
  · exact entryEval9_6_e B hB
  · exact entryEval9_7_e B hB
  · exact entryEval9_8_e B hB
  · exact entryEval9_9_e B hB
  · exact (entryEval10_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_9 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_9_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEval_e_oai (i j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms i).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases i
  · exact entryEvalRow0_e j B hB
  · exact entryEvalRow1_e j B hB
  · exact entryEvalRow2_e j B hB
  · exact entryEvalRow3_e j B hB
  · exact entryEvalRow4_e j B hB
  · exact entryEvalRow5_e j B hB
  · exact entryEvalRow6_e j B hB
  · exact entryEvalRow7_e j B hB
  · exact entryEvalRow8_e j B hB
  · exact entryEvalRow9 j B hB
  · exact entryEvalRow10_e j B hB
  · exact entryEvalRow11_e j B hB
  · exact entryEvalRow12_e j B hB
  · exact entryEvalRow13_e j B hB
  · exact entryEvalRow14_e j B hB
  · exact entryEvalRow15_e j B hB
  · exact entryEvalRow16_e j B hB
  · exact entryEvalRow17_e j B hB
  · exact entryEvalRow18_e j B hB
  · exact entryEvalRow19_e j B hB
  · exact entryEvalRow20_e j B hB

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e_oai
