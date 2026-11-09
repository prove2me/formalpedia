-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:53:59.123555+00:00
-- url     : https://prove2.me/submissions/8c5209bd-e33a-44f7-b823-8768b5dfdf11

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E022
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_7_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1674 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1674 := by decide +kernel

theorem rowCheck1674 : row1674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1674 := by decide +kernel

theorem rowEval1674 (x : Key → ℝ) : Integer.Sparse.eval row1674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1674, Integer.Sparse.eval_collectBalanced, rawRowCheck1674]

theorem rawRowCheck1675 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1675 := by decide +kernel

theorem rowCheck1675 : row1675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1675 := by decide +kernel

theorem rowEval1675 (x : Key → ℝ) : Integer.Sparse.eval row1675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1675, Integer.Sparse.eval_collectBalanced, rawRowCheck1675]

theorem rawRowCheck1676 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1676 := by decide +kernel

theorem rowCheck1676 : row1676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1676 := by decide +kernel

theorem rowEval1676 (x : Key → ℝ) : Integer.Sparse.eval row1676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1676, Integer.Sparse.eval_collectBalanced, rawRowCheck1676]

theorem rawRowCheck1683 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7 = rawRow1683 := by decide +kernel

theorem rowCheck1683 : row1683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1683 := by decide +kernel

theorem rowEval1683 (x : Key → ℝ) : Integer.Sparse.eval row1683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1683, Integer.Sparse.eval_collectBalanced, rawRowCheck1683]

theorem rawRowCheck1684 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7 = rawRow1684 := by decide +kernel

theorem rowCheck1684 : row1684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1684 := by decide +kernel

theorem rowEval1684 (x : Key → ℝ) : Integer.Sparse.eval row1684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1684, Integer.Sparse.eval_collectBalanced, rawRowCheck1684]

theorem rawRowCheck1685 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7 = rawRow1685 := by decide +kernel

theorem rowCheck1685 : row1685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1685 := by decide +kernel

theorem rowEval1685 (x : Key → ℝ) : Integer.Sparse.eval row1685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1685, Integer.Sparse.eval_collectBalanced, rawRowCheck1685]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck1862 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1862 := by decide +kernel

theorem rowCheck1862 : row1862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1862 := by decide +kernel

theorem rowEval1862 (x : Key → ℝ) : Integer.Sparse.eval row1862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1862, Integer.Sparse.eval_collectBalanced, rawRowCheck1862]

theorem rawRowCheck1863 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1863 := by decide +kernel

theorem rowCheck1863 : row1863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1863 := by decide +kernel

theorem rowEval1863 (x : Key → ℝ) : Integer.Sparse.eval row1863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1863, Integer.Sparse.eval_collectBalanced, rawRowCheck1863]

theorem rawRowCheck1864 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1864 := by decide +kernel

theorem rowCheck1864 : row1864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1864 := by decide +kernel

theorem rowEval1864 (x : Key → ℝ) : Integer.Sparse.eval row1864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1864, Integer.Sparse.eval_collectBalanced, rawRowCheck1864]

theorem rawRowCheck1865 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1865 := by decide +kernel

theorem rowCheck1865 : row1865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1865 := by decide +kernel

theorem rowEval1865 (x : Key → ℝ) : Integer.Sparse.eval row1865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1865, Integer.Sparse.eval_collectBalanced, rawRowCheck1865]

theorem rawRowCheck1866 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1866 := by decide +kernel

theorem rowCheck1866 : row1866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1866 := by decide +kernel

theorem rowEval1866 (x : Key → ℝ) : Integer.Sparse.eval row1866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1866, Integer.Sparse.eval_collectBalanced, rawRowCheck1866]

theorem rawRowCheck1867 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1867 := by decide +kernel

theorem rowCheck1867 : row1867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1867 := by decide +kernel

theorem rowEval1867 (x : Key → ℝ) : Integer.Sparse.eval row1867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1867, Integer.Sparse.eval_collectBalanced, rawRowCheck1867]

theorem rawRowCheck1868 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1868 := by decide +kernel

theorem rowCheck1868 : row1868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1868 := by decide +kernel

theorem rowEval1868 (x : Key → ℝ) : Integer.Sparse.eval row1868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1868, Integer.Sparse.eval_collectBalanced, rawRowCheck1868]

theorem rawRowCheck1869 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1869 := by decide +kernel

theorem rowCheck1869 : row1869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1869 := by decide +kernel

theorem rowEval1869 (x : Key → ℝ) : Integer.Sparse.eval row1869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1869, Integer.Sparse.eval_collectBalanced, rawRowCheck1869]

theorem rawRowCheck1870 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1870 := by decide +kernel

theorem rowCheck1870 : row1870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1870 := by decide +kernel

theorem rowEval1870 (x : Key → ℝ) : Integer.Sparse.eval row1870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1870, Integer.Sparse.eval_collectBalanced, rawRowCheck1870]

theorem rawRowCheck1871 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1871 := by decide +kernel

theorem rowCheck1871 : row1871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1871 := by decide +kernel

theorem rowEval1871 (x : Key → ℝ) : Integer.Sparse.eval row1871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1871, Integer.Sparse.eval_collectBalanced, rawRowCheck1871]

theorem rawRowCheck1872 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1872 := by decide +kernel

theorem rowCheck1872 : row1872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1872 := by decide +kernel

theorem rowEval1872 (x : Key → ℝ) : Integer.Sparse.eval row1872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1872, Integer.Sparse.eval_collectBalanced, rawRowCheck1872]

theorem rawRowCheck1873 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1873 := by decide +kernel

theorem rowCheck1873 : row1873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1873 := by decide +kernel

theorem rowEval1873 (x : Key → ℝ) : Integer.Sparse.eval row1873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1873, Integer.Sparse.eval_collectBalanced, rawRowCheck1873]

theorem rawRowCheck1874 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1874 := by decide +kernel

theorem rowCheck1874 : row1874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1874 := by decide +kernel

theorem rowEval1874 (x : Key → ℝ) : Integer.Sparse.eval row1874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1874, Integer.Sparse.eval_collectBalanced, rawRowCheck1874]

theorem rawRowCheck1875 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1875 := by decide +kernel

theorem rowCheck1875 : row1875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1875 := by decide +kernel

theorem rowEval1875 (x : Key → ℝ) : Integer.Sparse.eval row1875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1875, Integer.Sparse.eval_collectBalanced, rawRowCheck1875]

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

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1862 x
  · exact rowEval1863 x
  · exact rowEval1864 x
  · exact rowEval1865 x
  · exact rowEval1866 x
  · exact rowEval1867 x
  · exact rowEval1868 x
  · exact rowEval1869 x
  · exact rowEval1870 x
  · exact rowEval1871 x
  · exact rowEval1872 x
  · exact rowEval1873 x
  · exact rowEval1874 x
  · exact rowEval1875 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

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

theorem rawRowCheck2016 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2016 := by decide +kernel

theorem rowCheck2016 : row2016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2016 := by decide +kernel

theorem rowEval2016 (x : Key → ℝ) : Integer.Sparse.eval row2016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2016, Integer.Sparse.eval_collectBalanced, rawRowCheck2016]

theorem rawRowCheck2017 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2017 := by decide +kernel

theorem rowCheck2017 : row2017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2017 := by decide +kernel

theorem rowEval2017 (x : Key → ℝ) : Integer.Sparse.eval row2017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2017, Integer.Sparse.eval_collectBalanced, rawRowCheck2017]

theorem rawRowCheck2018 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2018 := by decide +kernel

theorem rowCheck2018 : row2018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2018 := by decide +kernel

theorem rowEval2018 (x : Key → ℝ) : Integer.Sparse.eval row2018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2018, Integer.Sparse.eval_collectBalanced, rawRowCheck2018]

theorem rawRowCheck2019 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2019 := by decide +kernel

theorem rowCheck2019 : row2019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2019 := by decide +kernel

theorem rowEval2019 (x : Key → ℝ) : Integer.Sparse.eval row2019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2019, Integer.Sparse.eval_collectBalanced, rawRowCheck2019]

theorem rawRowCheck2020 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2020 := by decide +kernel

theorem rowCheck2020 : row2020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2020 := by decide +kernel

theorem rowEval2020 (x : Key → ℝ) : Integer.Sparse.eval row2020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2020, Integer.Sparse.eval_collectBalanced, rawRowCheck2020]

theorem rawRowCheck2021 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2021 := by decide +kernel

theorem rowCheck2021 : row2021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2021 := by decide +kernel

theorem rowEval2021 (x : Key → ℝ) : Integer.Sparse.eval row2021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2021, Integer.Sparse.eval_collectBalanced, rawRowCheck2021]

theorem rawRowCheck2022 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2022 := by decide +kernel

theorem rowCheck2022 : row2022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2022 := by decide +kernel

theorem rowEval2022 (x : Key → ℝ) : Integer.Sparse.eval row2022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2022, Integer.Sparse.eval_collectBalanced, rawRowCheck2022]

theorem rawRowCheck2023 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7 = rawRow2023 := by decide +kernel

theorem rowCheck2023 : row2023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2023 := by decide +kernel

theorem rowEval2023 (x : Key → ℝ) : Integer.Sparse.eval row2023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2023, Integer.Sparse.eval_collectBalanced, rawRowCheck2023]

theorem rawRowCheck2024 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7 = rawRow2024 := by decide +kernel

theorem rowCheck2024 : row2024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2024 := by decide +kernel

theorem rowEval2024 (x : Key → ℝ) : Integer.Sparse.eval row2024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2024, Integer.Sparse.eval_collectBalanced, rawRowCheck2024]

theorem rawRowCheck2025 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7 = rawRow2025 := by decide +kernel

theorem rowCheck2025 : row2025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2025 := by decide +kernel

theorem rowEval2025 (x : Key → ℝ) : Integer.Sparse.eval row2025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2025, Integer.Sparse.eval_collectBalanced, rawRowCheck2025]

theorem rawRowCheck2026 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2026 := by decide +kernel

theorem rowCheck2026 : row2026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2026 := by decide +kernel

theorem rowEval2026 (x : Key → ℝ) : Integer.Sparse.eval row2026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2026, Integer.Sparse.eval_collectBalanced, rawRowCheck2026]

theorem rawRowCheck2027 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow2027 := by decide +kernel

theorem rowCheck2027 : row2027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2027 := by decide +kernel

theorem rowEval2027 (x : Key → ℝ) : Integer.Sparse.eval row2027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2027, Integer.Sparse.eval_collectBalanced, rawRowCheck2027]

theorem rawRowCheck2028 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow2028 := by decide +kernel

theorem rowCheck2028 : row2028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2028 := by decide +kernel

theorem rowEval2028 (x : Key → ℝ) : Integer.Sparse.eval row2028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2028, Integer.Sparse.eval_collectBalanced, rawRowCheck2028]

theorem rawRowCheck2029 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow2029 := by decide +kernel

theorem rowCheck2029 : row2029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2029 := by decide +kernel

theorem rowEval2029 (x : Key → ℝ) : Integer.Sparse.eval row2029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck2029, Integer.Sparse.eval_collectBalanced, rawRowCheck2029]

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

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2016 x
  · exact rowEval2017 x
  · exact rowEval2018 x
  · exact rowEval2019 x
  · exact rowEval2020 x
  · exact rowEval2021 x
  · exact rowEval2022 x
  · exact rowEval2023 x
  · exact rowEval2024 x
  · exact rowEval2025 x
  · exact rowEval2026 x
  · exact rowEval2027 x
  · exact rowEval2028 x
  · exact rowEval2029 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

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

theorem rawRowCheck2574 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2574 := by decide +kernel

theorem rowCheck2574 : row2574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2574 := by decide +kernel

theorem rowEval2574 (x : Key → ℝ) : Integer.Sparse.eval row2574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2574, Integer.Sparse.eval_collectBalanced, rawRowCheck2574]

theorem rawRowCheck2575 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2575 := by decide +kernel

theorem rowCheck2575 : row2575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2575 := by decide +kernel

theorem rowEval2575 (x : Key → ℝ) : Integer.Sparse.eval row2575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2575, Integer.Sparse.eval_collectBalanced, rawRowCheck2575]

theorem rawRowCheck2576 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2576 := by decide +kernel

theorem rowCheck2576 : row2576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2576 := by decide +kernel

theorem rowEval2576 (x : Key → ℝ) : Integer.Sparse.eval row2576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2576, Integer.Sparse.eval_collectBalanced, rawRowCheck2576]

theorem rawRowCheck2577 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2577 := by decide +kernel

theorem rowCheck2577 : row2577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2577 := by decide +kernel

theorem rowEval2577 (x : Key → ℝ) : Integer.Sparse.eval row2577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2577, Integer.Sparse.eval_collectBalanced, rawRowCheck2577]

theorem rawRowCheck2578 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2578 := by decide +kernel

theorem rowCheck2578 : row2578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2578 := by decide +kernel

theorem rowEval2578 (x : Key → ℝ) : Integer.Sparse.eval row2578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2578, Integer.Sparse.eval_collectBalanced, rawRowCheck2578]

theorem rawRowCheck2579 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2579 := by decide +kernel

theorem rowCheck2579 : row2579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2579 := by decide +kernel

theorem rowEval2579 (x : Key → ℝ) : Integer.Sparse.eval row2579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2579, Integer.Sparse.eval_collectBalanced, rawRowCheck2579]

theorem rawRowCheck2580 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2580 := by decide +kernel

theorem rowCheck2580 : row2580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2580 := by decide +kernel

theorem rowEval2580 (x : Key → ℝ) : Integer.Sparse.eval row2580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2580, Integer.Sparse.eval_collectBalanced, rawRowCheck2580]

theorem rawRowCheck2581 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2581 := by decide +kernel

theorem rowCheck2581 : row2581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2581 := by decide +kernel

theorem rowEval2581 (x : Key → ℝ) : Integer.Sparse.eval row2581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2581, Integer.Sparse.eval_collectBalanced, rawRowCheck2581]

theorem rawRowCheck2582 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2582 := by decide +kernel

theorem rowCheck2582 : row2582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2582 := by decide +kernel

theorem rowEval2582 (x : Key → ℝ) : Integer.Sparse.eval row2582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2582, Integer.Sparse.eval_collectBalanced, rawRowCheck2582]

theorem rawRowCheck2583 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2583 := by decide +kernel

theorem rowCheck2583 : row2583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2583 := by decide +kernel

theorem rowEval2583 (x : Key → ℝ) : Integer.Sparse.eval row2583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2583, Integer.Sparse.eval_collectBalanced, rawRowCheck2583]

theorem rawRowCheck2584 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2584 := by decide +kernel

theorem rowCheck2584 : row2584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2584 := by decide +kernel

theorem rowEval2584 (x : Key → ℝ) : Integer.Sparse.eval row2584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2584, Integer.Sparse.eval_collectBalanced, rawRowCheck2584]

theorem rawRowCheck2585 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2585 := by decide +kernel

theorem rowCheck2585 : row2585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2585 := by decide +kernel

theorem rowEval2585 (x : Key → ℝ) : Integer.Sparse.eval row2585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2585, Integer.Sparse.eval_collectBalanced, rawRowCheck2585]

theorem rawRowCheck2586 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2586 := by decide +kernel

theorem rowCheck2586 : row2586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2586 := by decide +kernel

theorem rowEval2586 (x : Key → ℝ) : Integer.Sparse.eval row2586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2586, Integer.Sparse.eval_collectBalanced, rawRowCheck2586]

theorem rawRowCheck2587 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2587 := by decide +kernel

theorem rowCheck2587 : row2587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2587 := by decide +kernel

theorem rowEval2587 (x : Key → ℝ) : Integer.Sparse.eval row2587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2587, Integer.Sparse.eval_collectBalanced, rawRowCheck2587]

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

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2574 x
  · exact rowEval2575 x
  · exact rowEval2576 x
  · exact rowEval2577 x
  · exact rowEval2578 x
  · exact rowEval2579 x
  · exact rowEval2580 x
  · exact rowEval2581 x
  · exact rowEval2582 x
  · exact rowEval2583 x
  · exact rowEval2584 x
  · exact rowEval2585 x
  · exact rowEval2586 x
  · exact rowEval2587 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

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

theorem rawRowCheck4654 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4654 := by decide +kernel

theorem rowCheck4654 : row4654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4654 := by decide +kernel

theorem rowEval4654 (x : Key → ℝ) : Integer.Sparse.eval row4654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4654, Integer.Sparse.eval_collectBalanced, rawRowCheck4654]

theorem rawRowCheck4655 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4655 := by decide +kernel

theorem rowCheck4655 : row4655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4655 := by decide +kernel

theorem rowEval4655 (x : Key → ℝ) : Integer.Sparse.eval row4655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4655, Integer.Sparse.eval_collectBalanced, rawRowCheck4655]

theorem rawRowCheck4656 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4656 := by decide +kernel

theorem rowCheck4656 : row4656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4656 := by decide +kernel

theorem rowEval4656 (x : Key → ℝ) : Integer.Sparse.eval row4656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4656, Integer.Sparse.eval_collectBalanced, rawRowCheck4656]

theorem rawRowCheck4657 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4657 := by decide +kernel

theorem rowCheck4657 : row4657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4657 := by decide +kernel

theorem rowEval4657 (x : Key → ℝ) : Integer.Sparse.eval row4657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4657, Integer.Sparse.eval_collectBalanced, rawRowCheck4657]

theorem rawRowCheck4658 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4658 := by decide +kernel

theorem rowCheck4658 : row4658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4658 := by decide +kernel

theorem rowEval4658 (x : Key → ℝ) : Integer.Sparse.eval row4658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4658, Integer.Sparse.eval_collectBalanced, rawRowCheck4658]

theorem rawRowCheck4659 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4659 := by decide +kernel

theorem rowCheck4659 : row4659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4659 := by decide +kernel

theorem rowEval4659 (x : Key → ℝ) : Integer.Sparse.eval row4659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4659, Integer.Sparse.eval_collectBalanced, rawRowCheck4659]

theorem rawRowCheck4660 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4660 := by decide +kernel

theorem rowCheck4660 : row4660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4660 := by decide +kernel

theorem rowEval4660 (x : Key → ℝ) : Integer.Sparse.eval row4660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4660, Integer.Sparse.eval_collectBalanced, rawRowCheck4660]

theorem rawRowCheck4661 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4661 := by decide +kernel

theorem rowCheck4661 : row4661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4661 := by decide +kernel

theorem rowEval4661 (x : Key → ℝ) : Integer.Sparse.eval row4661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4661, Integer.Sparse.eval_collectBalanced, rawRowCheck4661]

theorem rawRowCheck4662 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4662 := by decide +kernel

theorem rowCheck4662 : row4662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4662 := by decide +kernel

theorem rowEval4662 (x : Key → ℝ) : Integer.Sparse.eval row4662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4662, Integer.Sparse.eval_collectBalanced, rawRowCheck4662]

theorem rawRowCheck4663 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4663 := by decide +kernel

theorem rowCheck4663 : row4663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4663 := by decide +kernel

theorem rowEval4663 (x : Key → ℝ) : Integer.Sparse.eval row4663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4663, Integer.Sparse.eval_collectBalanced, rawRowCheck4663]

theorem rawRowCheck4664 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4664 := by decide +kernel

theorem rowCheck4664 : row4664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4664 := by decide +kernel

theorem rowEval4664 (x : Key → ℝ) : Integer.Sparse.eval row4664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4664, Integer.Sparse.eval_collectBalanced, rawRowCheck4664]

theorem rawRowCheck4665 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4665 := by decide +kernel

theorem rowCheck4665 : row4665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4665 := by decide +kernel

theorem rowEval4665 (x : Key → ℝ) : Integer.Sparse.eval row4665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4665, Integer.Sparse.eval_collectBalanced, rawRowCheck4665]

theorem rawRowCheck4666 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4666 := by decide +kernel

theorem rowCheck4666 : row4666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4666 := by decide +kernel

theorem rowEval4666 (x : Key → ℝ) : Integer.Sparse.eval row4666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4666, Integer.Sparse.eval_collectBalanced, rawRowCheck4666]

theorem rawRowCheck4667 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4667 := by decide +kernel

theorem rowCheck4667 : row4667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4667 := by decide +kernel

theorem rowEval4667 (x : Key → ℝ) : Integer.Sparse.eval row4667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4667, Integer.Sparse.eval_collectBalanced, rawRowCheck4667]

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

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4654 x
  · exact rowEval4655 x
  · exact rowEval4656 x
  · exact rowEval4657 x
  · exact rowEval4658 x
  · exact rowEval4659 x
  · exact rowEval4660 x
  · exact rowEval4661 x
  · exact rowEval4662 x
  · exact rowEval4663 x
  · exact rowEval4664 x
  · exact rowEval4665 x
  · exact rowEval4666 x
  · exact rowEval4667 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1448 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow1448 := by decide +kernel

theorem rowCheck1448 : row1448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1448 := by decide +kernel

theorem rowEval1448 (x : Key → ℝ) : Integer.Sparse.eval row1448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1448, Integer.Sparse.eval_collectBalanced, rawRowCheck1448]

theorem rawRowCheck1449 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow1449 := by decide +kernel

theorem rowCheck1449 : row1449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1449 := by decide +kernel

theorem rowEval1449 (x : Key → ℝ) : Integer.Sparse.eval row1449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1449, Integer.Sparse.eval_collectBalanced, rawRowCheck1449]

theorem rawRowCheck1450 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow1450 := by decide +kernel

theorem rowCheck1450 : row1450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1450 := by decide +kernel

theorem rowEval1450 (x : Key → ℝ) : Integer.Sparse.eval row1450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1450, Integer.Sparse.eval_collectBalanced, rawRowCheck1450]

theorem rawRowCheck1451 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1451 := by decide +kernel

theorem rowCheck1451 : row1451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1451 := by decide +kernel

theorem rowEval1451 (x : Key → ℝ) : Integer.Sparse.eval row1451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1451, Integer.Sparse.eval_collectBalanced, rawRowCheck1451]

theorem rawRowCheck1452 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7 = rawRow1452 := by decide +kernel

theorem rowCheck1452 : row1452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1452 := by decide +kernel

theorem rowEval1452 (x : Key → ℝ) : Integer.Sparse.eval row1452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1452, Integer.Sparse.eval_collectBalanced, rawRowCheck1452]

theorem rawRowCheck1453 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7 = rawRow1453 := by decide +kernel

theorem rowCheck1453 : row1453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1453 := by decide +kernel

theorem rowEval1453 (x : Key → ℝ) : Integer.Sparse.eval row1453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1453, Integer.Sparse.eval_collectBalanced, rawRowCheck1453]

theorem rawRowCheck1454 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7 = rawRow1454 := by decide +kernel

theorem rowCheck1454 : row1454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1454 := by decide +kernel

theorem rowEval1454 (x : Key → ℝ) : Integer.Sparse.eval row1454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1454, Integer.Sparse.eval_collectBalanced, rawRowCheck1454]

theorem rawRowCheck1455 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1455 := by decide +kernel

theorem rowCheck1455 : row1455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1455 := by decide +kernel

theorem rowEval1455 (x : Key → ℝ) : Integer.Sparse.eval row1455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1455, Integer.Sparse.eval_collectBalanced, rawRowCheck1455]

theorem rawRowCheck1456 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1456 := by decide +kernel

theorem rowCheck1456 : row1456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1456 := by decide +kernel

theorem rowEval1456 (x : Key → ℝ) : Integer.Sparse.eval row1456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1456, Integer.Sparse.eval_collectBalanced, rawRowCheck1456]

theorem rawRowCheck1457 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1457 := by decide +kernel

theorem rowCheck1457 : row1457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1457 := by decide +kernel

theorem rowEval1457 (x : Key → ℝ) : Integer.Sparse.eval row1457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1457, Integer.Sparse.eval_collectBalanced, rawRowCheck1457]

theorem rawRowCheck1458 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7 = rawRow1458 := by decide +kernel

theorem rowCheck1458 : row1458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1458 := by decide +kernel

theorem rowEval1458 (x : Key → ℝ) : Integer.Sparse.eval row1458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1458, Integer.Sparse.eval_collectBalanced, rawRowCheck1458]

theorem rawRowCheck1459 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7 = rawRow1459 := by decide +kernel

theorem rowCheck1459 : row1459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1459 := by decide +kernel

theorem rowEval1459 (x : Key → ℝ) : Integer.Sparse.eval row1459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1459, Integer.Sparse.eval_collectBalanced, rawRowCheck1459]

theorem rawRowCheck1460 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7 = rawRow1460 := by decide +kernel

theorem rowCheck1460 : row1460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1460 := by decide +kernel

theorem rowEval1460 (x : Key → ℝ) : Integer.Sparse.eval row1460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1460, Integer.Sparse.eval_collectBalanced, rawRowCheck1460]

theorem rawRowCheck1461 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7 = rawRow1461 := by decide +kernel

theorem rowCheck1461 : row1461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1461 := by decide +kernel

theorem rowEval1461 (x : Key → ℝ) : Integer.Sparse.eval row1461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form7) x := by
  rw [rowCheck1461, Integer.Sparse.eval_collectBalanced, rawRowCheck1461]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4914 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4914 := by decide +kernel

theorem rowCheck4914 : row4914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4914 := by decide +kernel

theorem rowEval4914 (x : Key → ℝ) : Integer.Sparse.eval row4914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4914, Integer.Sparse.eval_collectBalanced, rawRowCheck4914]

theorem rawRowCheck4915 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4915 := by decide +kernel

theorem rowCheck4915 : row4915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4915 := by decide +kernel

theorem rowEval4915 (x : Key → ℝ) : Integer.Sparse.eval row4915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4915, Integer.Sparse.eval_collectBalanced, rawRowCheck4915]

theorem rawRowCheck4916 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4916 := by decide +kernel

theorem rowCheck4916 : row4916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4916 := by decide +kernel

theorem rowEval4916 (x : Key → ℝ) : Integer.Sparse.eval row4916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4916, Integer.Sparse.eval_collectBalanced, rawRowCheck4916]

theorem rawRowCheck4917 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7 = rawRow4917 := by decide +kernel

theorem rowCheck4917 : row4917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4917 := by decide +kernel

theorem rowEval4917 (x : Key → ℝ) : Integer.Sparse.eval row4917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4917, Integer.Sparse.eval_collectBalanced, rawRowCheck4917]

theorem rawRowCheck4918 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7 = rawRow4918 := by decide +kernel

theorem rowCheck4918 : row4918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4918 := by decide +kernel

theorem rowEval4918 (x : Key → ℝ) : Integer.Sparse.eval row4918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4918, Integer.Sparse.eval_collectBalanced, rawRowCheck4918]

theorem rawRowCheck4919 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7 = rawRow4919 := by decide +kernel

theorem rowCheck4919 : row4919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4919 := by decide +kernel

theorem rowEval4919 (x : Key → ℝ) : Integer.Sparse.eval row4919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4919, Integer.Sparse.eval_collectBalanced, rawRowCheck4919]

theorem rawRowCheck4920 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4920 := by decide +kernel

theorem rowCheck4920 : row4920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4920 := by decide +kernel

theorem rowEval4920 (x : Key → ℝ) : Integer.Sparse.eval row4920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4920, Integer.Sparse.eval_collectBalanced, rawRowCheck4920]

theorem rawRowCheck4921 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4921 := by decide +kernel

theorem rowCheck4921 : row4921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4921 := by decide +kernel

theorem rowEval4921 (x : Key → ℝ) : Integer.Sparse.eval row4921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4921, Integer.Sparse.eval_collectBalanced, rawRowCheck4921]

theorem rawRowCheck4922 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4922 := by decide +kernel

theorem rowCheck4922 : row4922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4922 := by decide +kernel

theorem rowEval4922 (x : Key → ℝ) : Integer.Sparse.eval row4922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4922, Integer.Sparse.eval_collectBalanced, rawRowCheck4922]

theorem rawRowCheck4923 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7 = rawRow4923 := by decide +kernel

theorem rowCheck4923 : row4923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4923 := by decide +kernel

theorem rowEval4923 (x : Key → ℝ) : Integer.Sparse.eval row4923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4923, Integer.Sparse.eval_collectBalanced, rawRowCheck4923]

theorem rawRowCheck4924 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7 = rawRow4924 := by decide +kernel

theorem rowCheck4924 : row4924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4924 := by decide +kernel

theorem rowEval4924 (x : Key → ℝ) : Integer.Sparse.eval row4924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4924, Integer.Sparse.eval_collectBalanced, rawRowCheck4924]

theorem rawRowCheck4925 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7 = rawRow4925 := by decide +kernel

theorem rowCheck4925 : row4925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4925 := by decide +kernel

theorem rowEval4925 (x : Key → ℝ) : Integer.Sparse.eval row4925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4925, Integer.Sparse.eval_collectBalanced, rawRowCheck4925]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4914 x
  · exact rowEval4915 x
  · exact rowEval4916 x
  · exact rowEval1674 x
  · exact rowEval1675 x
  · exact rowEval1676 x
  · exact rowEval4917 x
  · exact rowEval4918 x
  · exact rowEval4919 x
  · exact rowEval4920 x
  · exact rowEval4921 x
  · exact rowEval4922 x
  · exact rowEval1683 x
  · exact rowEval1684 x
  · exact rowEval1685 x
  · exact rowEval4923 x
  · exact rowEval4924 x
  · exact rowEval4925 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck934 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1 = rawRow934 := by decide +kernel

theorem rowCheck934 : row934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow934 := by decide +kernel

theorem rowEval934 (x : Key → ℝ) : Integer.Sparse.eval row934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck934, Integer.Sparse.eval_collectBalanced, rawRowCheck934]

theorem rawRowCheck935 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1 = rawRow935 := by decide +kernel

theorem rowCheck935 : row935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow935 := by decide +kernel

theorem rowEval935 (x : Key → ℝ) : Integer.Sparse.eval row935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck935, Integer.Sparse.eval_collectBalanced, rawRowCheck935]

theorem rawRowCheck936 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1 = rawRow936 := by decide +kernel

theorem rowCheck936 : row936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow936 := by decide +kernel

theorem rowEval936 (x : Key → ℝ) : Integer.Sparse.eval row936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck936, Integer.Sparse.eval_collectBalanced, rawRowCheck936]

theorem rawRowCheck937 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1 = rawRow937 := by decide +kernel

theorem rowCheck937 : row937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow937 := by decide +kernel

theorem rowEval937 (x : Key → ℝ) : Integer.Sparse.eval row937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck937, Integer.Sparse.eval_collectBalanced, rawRowCheck937]

theorem rawRowCheck938 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1 = rawRow938 := by decide +kernel

theorem rowCheck938 : row938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow938 := by decide +kernel

theorem rowEval938 (x : Key → ℝ) : Integer.Sparse.eval row938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck938, Integer.Sparse.eval_collectBalanced, rawRowCheck938]

theorem rawRowCheck939 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1 = rawRow939 := by decide +kernel

theorem rowCheck939 : row939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow939 := by decide +kernel

theorem rowEval939 (x : Key → ℝ) : Integer.Sparse.eval row939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck939, Integer.Sparse.eval_collectBalanced, rawRowCheck939]

theorem rawRowCheck943 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1 = rawRow943 := by decide +kernel

theorem rowCheck943 : row943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow943 := by decide +kernel

theorem rowEval943 (x : Key → ℝ) : Integer.Sparse.eval row943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck943, Integer.Sparse.eval_collectBalanced, rawRowCheck943]

theorem rawRowCheck944 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1 = rawRow944 := by decide +kernel

theorem rowCheck944 : row944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow944 := by decide +kernel

theorem rowEval944 (x : Key → ℝ) : Integer.Sparse.eval row944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck944, Integer.Sparse.eval_collectBalanced, rawRowCheck944]

theorem rawRowCheck945 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1 = rawRow945 := by decide +kernel

theorem rowCheck945 : row945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow945 := by decide +kernel

theorem rowEval945 (x : Key → ℝ) : Integer.Sparse.eval row945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck945, Integer.Sparse.eval_collectBalanced, rawRowCheck945]

theorem rawRowCheck946 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1 = rawRow946 := by decide +kernel

theorem rowCheck946 : row946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow946 := by decide +kernel

theorem rowEval946 (x : Key → ℝ) : Integer.Sparse.eval row946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck946, Integer.Sparse.eval_collectBalanced, rawRowCheck946]

theorem rawRowCheck947 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1 = rawRow947 := by decide +kernel

theorem rowCheck947 : row947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow947 := by decide +kernel

theorem rowEval947 (x : Key → ℝ) : Integer.Sparse.eval row947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck947, Integer.Sparse.eval_collectBalanced, rawRowCheck947]

theorem rawRowCheck948 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1 = rawRow948 := by decide +kernel

theorem rowCheck948 : row948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow948 := by decide +kernel

theorem rowEval948 (x : Key → ℝ) : Integer.Sparse.eval row948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck948, Integer.Sparse.eval_collectBalanced, rawRowCheck948]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck994 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3 = rawRow994 := by decide +kernel

theorem rowCheck994 : row994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow994 := by decide +kernel

theorem rowEval994 (x : Key → ℝ) : Integer.Sparse.eval row994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck994, Integer.Sparse.eval_collectBalanced, rawRowCheck994]

theorem rawRowCheck995 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3 = rawRow995 := by decide +kernel

theorem rowCheck995 : row995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow995 := by decide +kernel

theorem rowEval995 (x : Key → ℝ) : Integer.Sparse.eval row995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck995, Integer.Sparse.eval_collectBalanced, rawRowCheck995]

theorem rawRowCheck996 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3 = rawRow996 := by decide +kernel

theorem rowCheck996 : row996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow996 := by decide +kernel

theorem rowEval996 (x : Key → ℝ) : Integer.Sparse.eval row996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck996, Integer.Sparse.eval_collectBalanced, rawRowCheck996]

theorem rawRowCheck997 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3 = rawRow997 := by decide +kernel

theorem rowCheck997 : row997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow997 := by decide +kernel

theorem rowEval997 (x : Key → ℝ) : Integer.Sparse.eval row997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck997, Integer.Sparse.eval_collectBalanced, rawRowCheck997]

theorem rawRowCheck998 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3 = rawRow998 := by decide +kernel

theorem rowCheck998 : row998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow998 := by decide +kernel

theorem rowEval998 (x : Key → ℝ) : Integer.Sparse.eval row998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck998, Integer.Sparse.eval_collectBalanced, rawRowCheck998]

theorem rawRowCheck999 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3 = rawRow999 := by decide +kernel

theorem rowCheck999 : row999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow999 := by decide +kernel

theorem rowEval999 (x : Key → ℝ) : Integer.Sparse.eval row999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck999, Integer.Sparse.eval_collectBalanced, rawRowCheck999]

theorem rawRowCheck1003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3 = rawRow1003 := by decide +kernel

theorem rowCheck1003 : row1003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1003 := by decide +kernel

theorem rowEval1003 (x : Key → ℝ) : Integer.Sparse.eval row1003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1003, Integer.Sparse.eval_collectBalanced, rawRowCheck1003]

theorem rawRowCheck1004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3 = rawRow1004 := by decide +kernel

theorem rowCheck1004 : row1004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1004 := by decide +kernel

theorem rowEval1004 (x : Key → ℝ) : Integer.Sparse.eval row1004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1004, Integer.Sparse.eval_collectBalanced, rawRowCheck1004]

theorem rawRowCheck1005 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3 = rawRow1005 := by decide +kernel

theorem rowCheck1005 : row1005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1005 := by decide +kernel

theorem rowEval1005 (x : Key → ℝ) : Integer.Sparse.eval row1005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1005, Integer.Sparse.eval_collectBalanced, rawRowCheck1005]

theorem rawRowCheck1006 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3 = rawRow1006 := by decide +kernel

theorem rowCheck1006 : row1006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1006 := by decide +kernel

theorem rowEval1006 (x : Key → ℝ) : Integer.Sparse.eval row1006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1006, Integer.Sparse.eval_collectBalanced, rawRowCheck1006]

theorem rawRowCheck1007 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3 = rawRow1007 := by decide +kernel

theorem rowCheck1007 : row1007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1007 := by decide +kernel

theorem rowEval1007 (x : Key → ℝ) : Integer.Sparse.eval row1007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1007, Integer.Sparse.eval_collectBalanced, rawRowCheck1007]

theorem rawRowCheck1008 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3 = rawRow1008 := by decide +kernel

theorem rowCheck1008 : row1008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1008 := by decide +kernel

theorem rowEval1008 (x : Key → ℝ) : Integer.Sparse.eval row1008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1008, Integer.Sparse.eval_collectBalanced, rawRowCheck1008]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1024 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4 = rawRow1024 := by decide +kernel

theorem rowCheck1024 : row1024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1024 := by decide +kernel

theorem rowEval1024 (x : Key → ℝ) : Integer.Sparse.eval row1024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1024, Integer.Sparse.eval_collectBalanced, rawRowCheck1024]

theorem rawRowCheck1025 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4 = rawRow1025 := by decide +kernel

theorem rowCheck1025 : row1025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1025 := by decide +kernel

theorem rowEval1025 (x : Key → ℝ) : Integer.Sparse.eval row1025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1025, Integer.Sparse.eval_collectBalanced, rawRowCheck1025]

theorem rawRowCheck1026 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4 = rawRow1026 := by decide +kernel

theorem rowCheck1026 : row1026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1026 := by decide +kernel

theorem rowEval1026 (x : Key → ℝ) : Integer.Sparse.eval row1026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1026, Integer.Sparse.eval_collectBalanced, rawRowCheck1026]

theorem rawRowCheck1027 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4 = rawRow1027 := by decide +kernel

theorem rowCheck1027 : row1027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1027 := by decide +kernel

theorem rowEval1027 (x : Key → ℝ) : Integer.Sparse.eval row1027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1027, Integer.Sparse.eval_collectBalanced, rawRowCheck1027]

theorem rawRowCheck1028 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4 = rawRow1028 := by decide +kernel

theorem rowCheck1028 : row1028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1028 := by decide +kernel

theorem rowEval1028 (x : Key → ℝ) : Integer.Sparse.eval row1028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1028, Integer.Sparse.eval_collectBalanced, rawRowCheck1028]

theorem rawRowCheck1029 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4 = rawRow1029 := by decide +kernel

theorem rowCheck1029 : row1029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1029 := by decide +kernel

theorem rowEval1029 (x : Key → ℝ) : Integer.Sparse.eval row1029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1029, Integer.Sparse.eval_collectBalanced, rawRowCheck1029]

theorem rawRowCheck1033 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4 = rawRow1033 := by decide +kernel

theorem rowCheck1033 : row1033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1033 := by decide +kernel

theorem rowEval1033 (x : Key → ℝ) : Integer.Sparse.eval row1033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1033, Integer.Sparse.eval_collectBalanced, rawRowCheck1033]

theorem rawRowCheck1034 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4 = rawRow1034 := by decide +kernel

theorem rowCheck1034 : row1034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1034 := by decide +kernel

theorem rowEval1034 (x : Key → ℝ) : Integer.Sparse.eval row1034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1034, Integer.Sparse.eval_collectBalanced, rawRowCheck1034]

theorem rawRowCheck1035 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4 = rawRow1035 := by decide +kernel

theorem rowCheck1035 : row1035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1035 := by decide +kernel

theorem rowEval1035 (x : Key → ℝ) : Integer.Sparse.eval row1035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1035, Integer.Sparse.eval_collectBalanced, rawRowCheck1035]

theorem rawRowCheck1036 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4 = rawRow1036 := by decide +kernel

theorem rowCheck1036 : row1036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1036 := by decide +kernel

theorem rowEval1036 (x : Key → ℝ) : Integer.Sparse.eval row1036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1036, Integer.Sparse.eval_collectBalanced, rawRowCheck1036]

theorem rawRowCheck1037 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4 = rawRow1037 := by decide +kernel

theorem rowCheck1037 : row1037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1037 := by decide +kernel

theorem rowEval1037 (x : Key → ℝ) : Integer.Sparse.eval row1037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1037, Integer.Sparse.eval_collectBalanced, rawRowCheck1037]

theorem rawRowCheck1038 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4 = rawRow1038 := by decide +kernel

theorem rowCheck1038 : row1038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1038 := by decide +kernel

theorem rowEval1038 (x : Key → ℝ) : Integer.Sparse.eval row1038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1038, Integer.Sparse.eval_collectBalanced, rawRowCheck1038]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1200 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1200 := by decide +kernel

theorem rowCheck1200 : row1200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1200 := by decide +kernel

theorem rowEval1200 (x : Key → ℝ) : Integer.Sparse.eval row1200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1200, Integer.Sparse.eval_collectBalanced, rawRowCheck1200]

theorem rawRowCheck1201 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1201 := by decide +kernel

theorem rowCheck1201 : row1201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1201 := by decide +kernel

theorem rowEval1201 (x : Key → ℝ) : Integer.Sparse.eval row1201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1201, Integer.Sparse.eval_collectBalanced, rawRowCheck1201]

theorem rawRowCheck1202 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1202 := by decide +kernel

theorem rowCheck1202 : row1202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1202 := by decide +kernel

theorem rowEval1202 (x : Key → ℝ) : Integer.Sparse.eval row1202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1202, Integer.Sparse.eval_collectBalanced, rawRowCheck1202]

theorem rawRowCheck1203 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1 = rawRow1203 := by decide +kernel

theorem rowCheck1203 : row1203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1203 := by decide +kernel

theorem rowEval1203 (x : Key → ℝ) : Integer.Sparse.eval row1203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1203, Integer.Sparse.eval_collectBalanced, rawRowCheck1203]

theorem rawRowCheck1204 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1 = rawRow1204 := by decide +kernel

theorem rowCheck1204 : row1204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1204 := by decide +kernel

theorem rowEval1204 (x : Key → ℝ) : Integer.Sparse.eval row1204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1204, Integer.Sparse.eval_collectBalanced, rawRowCheck1204]

theorem rawRowCheck1205 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1 = rawRow1205 := by decide +kernel

theorem rowCheck1205 : row1205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1205 := by decide +kernel

theorem rowEval1205 (x : Key → ℝ) : Integer.Sparse.eval row1205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1205, Integer.Sparse.eval_collectBalanced, rawRowCheck1205]

theorem rawRowCheck1206 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1 = rawRow1206 := by decide +kernel

theorem rowCheck1206 : row1206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1206 := by decide +kernel

theorem rowEval1206 (x : Key → ℝ) : Integer.Sparse.eval row1206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1206, Integer.Sparse.eval_collectBalanced, rawRowCheck1206]

theorem rawRowCheck1207 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1 = rawRow1207 := by decide +kernel

theorem rowCheck1207 : row1207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1207 := by decide +kernel

theorem rowEval1207 (x : Key → ℝ) : Integer.Sparse.eval row1207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1207, Integer.Sparse.eval_collectBalanced, rawRowCheck1207]

theorem rawRowCheck1208 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1 = rawRow1208 := by decide +kernel

theorem rowCheck1208 : row1208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1208 := by decide +kernel

theorem rowEval1208 (x : Key → ℝ) : Integer.Sparse.eval row1208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1208, Integer.Sparse.eval_collectBalanced, rawRowCheck1208]

theorem rawRowCheck1209 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1209 := by decide +kernel

theorem rowCheck1209 : row1209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1209 := by decide +kernel

theorem rowEval1209 (x : Key → ℝ) : Integer.Sparse.eval row1209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1209, Integer.Sparse.eval_collectBalanced, rawRowCheck1209]

theorem rawRowCheck1210 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1210 := by decide +kernel

theorem rowCheck1210 : row1210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1210 := by decide +kernel

theorem rowEval1210 (x : Key → ℝ) : Integer.Sparse.eval row1210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1210, Integer.Sparse.eval_collectBalanced, rawRowCheck1210]

theorem rawRowCheck1211 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1211 := by decide +kernel

theorem rowCheck1211 : row1211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1211 := by decide +kernel

theorem rowEval1211 (x : Key → ℝ) : Integer.Sparse.eval row1211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1211, Integer.Sparse.eval_collectBalanced, rawRowCheck1211]

theorem rawRowCheck1212 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1 = rawRow1212 := by decide +kernel

theorem rowCheck1212 : row1212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1212 := by decide +kernel

theorem rowEval1212 (x : Key → ℝ) : Integer.Sparse.eval row1212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1212, Integer.Sparse.eval_collectBalanced, rawRowCheck1212]

theorem rawRowCheck1213 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1 = rawRow1213 := by decide +kernel

theorem rowCheck1213 : row1213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1213 := by decide +kernel

theorem rowEval1213 (x : Key → ℝ) : Integer.Sparse.eval row1213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1213, Integer.Sparse.eval_collectBalanced, rawRowCheck1213]

theorem rawRowCheck1214 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1 = rawRow1214 := by decide +kernel

theorem rowCheck1214 : row1214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1214 := by decide +kernel

theorem rowEval1214 (x : Key → ℝ) : Integer.Sparse.eval row1214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1214, Integer.Sparse.eval_collectBalanced, rawRowCheck1214]

theorem rawRowCheck1215 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1 = rawRow1215 := by decide +kernel

theorem rowCheck1215 : row1215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1215 := by decide +kernel

theorem rowEval1215 (x : Key → ℝ) : Integer.Sparse.eval row1215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1215, Integer.Sparse.eval_collectBalanced, rawRowCheck1215]

theorem rawRowCheck1216 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1 = rawRow1216 := by decide +kernel

theorem rowCheck1216 : row1216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1216 := by decide +kernel

theorem rowEval1216 (x : Key → ℝ) : Integer.Sparse.eval row1216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1216, Integer.Sparse.eval_collectBalanced, rawRowCheck1216]

theorem rawRowCheck1217 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1 = rawRow1217 := by decide +kernel

theorem rowCheck1217 : row1217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1217 := by decide +kernel

theorem rowEval1217 (x : Key → ℝ) : Integer.Sparse.eval row1217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1217, Integer.Sparse.eval_collectBalanced, rawRowCheck1217]

theorem rawRowCheck1236 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1236 := by decide +kernel

theorem rowCheck1236 : row1236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1236 := by decide +kernel

theorem rowEval1236 (x : Key → ℝ) : Integer.Sparse.eval row1236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1236, Integer.Sparse.eval_collectBalanced, rawRowCheck1236]

theorem rawRowCheck1237 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1237 := by decide +kernel

theorem rowCheck1237 : row1237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1237 := by decide +kernel

theorem rowEval1237 (x : Key → ℝ) : Integer.Sparse.eval row1237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1237, Integer.Sparse.eval_collectBalanced, rawRowCheck1237]

theorem rawRowCheck1238 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1238 := by decide +kernel

theorem rowCheck1238 : row1238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1238 := by decide +kernel

theorem rowEval1238 (x : Key → ℝ) : Integer.Sparse.eval row1238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1238, Integer.Sparse.eval_collectBalanced, rawRowCheck1238]

theorem rawRowCheck1239 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form3 = rawRow1239 := by decide +kernel

theorem rowCheck1239 : row1239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1239 := by decide +kernel

theorem rowEval1239 (x : Key → ℝ) : Integer.Sparse.eval row1239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1239, Integer.Sparse.eval_collectBalanced, rawRowCheck1239]

theorem rawRowCheck1240 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form3 = rawRow1240 := by decide +kernel

theorem rowCheck1240 : row1240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1240 := by decide +kernel

theorem rowEval1240 (x : Key → ℝ) : Integer.Sparse.eval row1240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1240, Integer.Sparse.eval_collectBalanced, rawRowCheck1240]

theorem rawRowCheck1241 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form3 = rawRow1241 := by decide +kernel

theorem rowCheck1241 : row1241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1241 := by decide +kernel

theorem rowEval1241 (x : Key → ℝ) : Integer.Sparse.eval row1241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1241, Integer.Sparse.eval_collectBalanced, rawRowCheck1241]

theorem rawRowCheck1242 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form3 = rawRow1242 := by decide +kernel

theorem rowCheck1242 : row1242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1242 := by decide +kernel

theorem rowEval1242 (x : Key → ℝ) : Integer.Sparse.eval row1242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1242, Integer.Sparse.eval_collectBalanced, rawRowCheck1242]

theorem rawRowCheck1243 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form3 = rawRow1243 := by decide +kernel

theorem rowCheck1243 : row1243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1243 := by decide +kernel

theorem rowEval1243 (x : Key → ℝ) : Integer.Sparse.eval row1243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1243, Integer.Sparse.eval_collectBalanced, rawRowCheck1243]

theorem rawRowCheck1244 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form3 = rawRow1244 := by decide +kernel

theorem rowCheck1244 : row1244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1244 := by decide +kernel

theorem rowEval1244 (x : Key → ℝ) : Integer.Sparse.eval row1244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1244, Integer.Sparse.eval_collectBalanced, rawRowCheck1244]

theorem rawRowCheck1245 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1245 := by decide +kernel

theorem rowCheck1245 : row1245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1245 := by decide +kernel

theorem rowEval1245 (x : Key → ℝ) : Integer.Sparse.eval row1245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1245, Integer.Sparse.eval_collectBalanced, rawRowCheck1245]

theorem rawRowCheck1246 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1246 := by decide +kernel

theorem rowCheck1246 : row1246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1246 := by decide +kernel

theorem rowEval1246 (x : Key → ℝ) : Integer.Sparse.eval row1246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1246, Integer.Sparse.eval_collectBalanced, rawRowCheck1246]

theorem rawRowCheck1247 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1247 := by decide +kernel

theorem rowCheck1247 : row1247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1247 := by decide +kernel

theorem rowEval1247 (x : Key → ℝ) : Integer.Sparse.eval row1247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1247, Integer.Sparse.eval_collectBalanced, rawRowCheck1247]

theorem rawRowCheck1248 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form3 = rawRow1248 := by decide +kernel

theorem rowCheck1248 : row1248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1248 := by decide +kernel

theorem rowEval1248 (x : Key → ℝ) : Integer.Sparse.eval row1248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1248, Integer.Sparse.eval_collectBalanced, rawRowCheck1248]

theorem rawRowCheck1249 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form3 = rawRow1249 := by decide +kernel

theorem rowCheck1249 : row1249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1249 := by decide +kernel

theorem rowEval1249 (x : Key → ℝ) : Integer.Sparse.eval row1249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1249, Integer.Sparse.eval_collectBalanced, rawRowCheck1249]

theorem rawRowCheck1250 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form3 = rawRow1250 := by decide +kernel

theorem rowCheck1250 : row1250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1250 := by decide +kernel

theorem rowEval1250 (x : Key → ℝ) : Integer.Sparse.eval row1250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1250, Integer.Sparse.eval_collectBalanced, rawRowCheck1250]

theorem rawRowCheck1251 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form3 = rawRow1251 := by decide +kernel

theorem rowCheck1251 : row1251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1251 := by decide +kernel

theorem rowEval1251 (x : Key → ℝ) : Integer.Sparse.eval row1251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1251, Integer.Sparse.eval_collectBalanced, rawRowCheck1251]

theorem rawRowCheck1252 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form3 = rawRow1252 := by decide +kernel

theorem rowCheck1252 : row1252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1252 := by decide +kernel

theorem rowEval1252 (x : Key → ℝ) : Integer.Sparse.eval row1252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1252, Integer.Sparse.eval_collectBalanced, rawRowCheck1252]

theorem rawRowCheck1253 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form3 = rawRow1253 := by decide +kernel

theorem rowCheck1253 : row1253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1253 := by decide +kernel

theorem rowEval1253 (x : Key → ℝ) : Integer.Sparse.eval row1253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1253, Integer.Sparse.eval_collectBalanced, rawRowCheck1253]

theorem rawRowCheck1254 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1254 := by decide +kernel

theorem rowCheck1254 : row1254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1254 := by decide +kernel

theorem rowEval1254 (x : Key → ℝ) : Integer.Sparse.eval row1254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1254, Integer.Sparse.eval_collectBalanced, rawRowCheck1254]

theorem rawRowCheck1255 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1255 := by decide +kernel

theorem rowCheck1255 : row1255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1255 := by decide +kernel

theorem rowEval1255 (x : Key → ℝ) : Integer.Sparse.eval row1255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1255, Integer.Sparse.eval_collectBalanced, rawRowCheck1255]

theorem rawRowCheck1256 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1256 := by decide +kernel

theorem rowCheck1256 : row1256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1256 := by decide +kernel

theorem rowEval1256 (x : Key → ℝ) : Integer.Sparse.eval row1256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1256, Integer.Sparse.eval_collectBalanced, rawRowCheck1256]

theorem rawRowCheck1257 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form4 = rawRow1257 := by decide +kernel

theorem rowCheck1257 : row1257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1257 := by decide +kernel

theorem rowEval1257 (x : Key → ℝ) : Integer.Sparse.eval row1257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1257, Integer.Sparse.eval_collectBalanced, rawRowCheck1257]

theorem rawRowCheck1258 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form4 = rawRow1258 := by decide +kernel

theorem rowCheck1258 : row1258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1258 := by decide +kernel

theorem rowEval1258 (x : Key → ℝ) : Integer.Sparse.eval row1258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1258, Integer.Sparse.eval_collectBalanced, rawRowCheck1258]

theorem rawRowCheck1259 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form4 = rawRow1259 := by decide +kernel

theorem rowCheck1259 : row1259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1259 := by decide +kernel

theorem rowEval1259 (x : Key → ℝ) : Integer.Sparse.eval row1259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1259, Integer.Sparse.eval_collectBalanced, rawRowCheck1259]

theorem rawRowCheck1260 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form4 = rawRow1260 := by decide +kernel

theorem rowCheck1260 : row1260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1260 := by decide +kernel

theorem rowEval1260 (x : Key → ℝ) : Integer.Sparse.eval row1260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1260, Integer.Sparse.eval_collectBalanced, rawRowCheck1260]

theorem rawRowCheck1261 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form4 = rawRow1261 := by decide +kernel

theorem rowCheck1261 : row1261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1261 := by decide +kernel

theorem rowEval1261 (x : Key → ℝ) : Integer.Sparse.eval row1261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1261, Integer.Sparse.eval_collectBalanced, rawRowCheck1261]

theorem rawRowCheck1262 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form4 = rawRow1262 := by decide +kernel

theorem rowCheck1262 : row1262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1262 := by decide +kernel

theorem rowEval1262 (x : Key → ℝ) : Integer.Sparse.eval row1262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1262, Integer.Sparse.eval_collectBalanced, rawRowCheck1262]

theorem rawRowCheck1263 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1263 := by decide +kernel

theorem rowCheck1263 : row1263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1263 := by decide +kernel

theorem rowEval1263 (x : Key → ℝ) : Integer.Sparse.eval row1263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1263, Integer.Sparse.eval_collectBalanced, rawRowCheck1263]

theorem rawRowCheck1264 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1264 := by decide +kernel

theorem rowCheck1264 : row1264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1264 := by decide +kernel

theorem rowEval1264 (x : Key → ℝ) : Integer.Sparse.eval row1264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1264, Integer.Sparse.eval_collectBalanced, rawRowCheck1264]

theorem rawRowCheck1265 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1265 := by decide +kernel

theorem rowCheck1265 : row1265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1265 := by decide +kernel

theorem rowEval1265 (x : Key → ℝ) : Integer.Sparse.eval row1265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1265, Integer.Sparse.eval_collectBalanced, rawRowCheck1265]

theorem rawRowCheck1266 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form4 = rawRow1266 := by decide +kernel

theorem rowCheck1266 : row1266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1266 := by decide +kernel

theorem rowEval1266 (x : Key → ℝ) : Integer.Sparse.eval row1266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1266, Integer.Sparse.eval_collectBalanced, rawRowCheck1266]

theorem rawRowCheck1267 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form4 = rawRow1267 := by decide +kernel

theorem rowCheck1267 : row1267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1267 := by decide +kernel

theorem rowEval1267 (x : Key → ℝ) : Integer.Sparse.eval row1267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1267, Integer.Sparse.eval_collectBalanced, rawRowCheck1267]

theorem rawRowCheck1268 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form4 = rawRow1268 := by decide +kernel

theorem rowCheck1268 : row1268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1268 := by decide +kernel

theorem rowEval1268 (x : Key → ℝ) : Integer.Sparse.eval row1268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1268, Integer.Sparse.eval_collectBalanced, rawRowCheck1268]

theorem rawRowCheck1269 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form4 = rawRow1269 := by decide +kernel

theorem rowCheck1269 : row1269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1269 := by decide +kernel

theorem rowEval1269 (x : Key → ℝ) : Integer.Sparse.eval row1269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1269, Integer.Sparse.eval_collectBalanced, rawRowCheck1269]

theorem rawRowCheck1270 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form4 = rawRow1270 := by decide +kernel

theorem rowCheck1270 : row1270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1270 := by decide +kernel

theorem rowEval1270 (x : Key → ℝ) : Integer.Sparse.eval row1270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1270, Integer.Sparse.eval_collectBalanced, rawRowCheck1270]

theorem rawRowCheck1271 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form4 = rawRow1271 := by decide +kernel

theorem rowCheck1271 : row1271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1271 := by decide +kernel

theorem rowEval1271 (x : Key → ℝ) : Integer.Sparse.eval row1271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1271, Integer.Sparse.eval_collectBalanced, rawRowCheck1271]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1290 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1290 := by decide +kernel

theorem rowCheck1290 : row1290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1290 := by decide +kernel

theorem rowEval1290 (x : Key → ℝ) : Integer.Sparse.eval row1290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1290, Integer.Sparse.eval_collectBalanced, rawRowCheck1290]

theorem rawRowCheck1291 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1291 := by decide +kernel

theorem rowCheck1291 : row1291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1291 := by decide +kernel

theorem rowEval1291 (x : Key → ℝ) : Integer.Sparse.eval row1291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1291, Integer.Sparse.eval_collectBalanced, rawRowCheck1291]

theorem rawRowCheck1292 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1292 := by decide +kernel

theorem rowCheck1292 : row1292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1292 := by decide +kernel

theorem rowEval1292 (x : Key → ℝ) : Integer.Sparse.eval row1292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1292, Integer.Sparse.eval_collectBalanced, rawRowCheck1292]

theorem rawRowCheck1293 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form6 = rawRow1293 := by decide +kernel

theorem rowCheck1293 : row1293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1293 := by decide +kernel

theorem rowEval1293 (x : Key → ℝ) : Integer.Sparse.eval row1293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1293, Integer.Sparse.eval_collectBalanced, rawRowCheck1293]

theorem rawRowCheck1294 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form6 = rawRow1294 := by decide +kernel

theorem rowCheck1294 : row1294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1294 := by decide +kernel

theorem rowEval1294 (x : Key → ℝ) : Integer.Sparse.eval row1294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1294, Integer.Sparse.eval_collectBalanced, rawRowCheck1294]

theorem rawRowCheck1295 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form6 = rawRow1295 := by decide +kernel

theorem rowCheck1295 : row1295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1295 := by decide +kernel

theorem rowEval1295 (x : Key → ℝ) : Integer.Sparse.eval row1295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1295, Integer.Sparse.eval_collectBalanced, rawRowCheck1295]

theorem rawRowCheck1296 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form6 = rawRow1296 := by decide +kernel

theorem rowCheck1296 : row1296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1296 := by decide +kernel

theorem rowEval1296 (x : Key → ℝ) : Integer.Sparse.eval row1296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1296, Integer.Sparse.eval_collectBalanced, rawRowCheck1296]

theorem rawRowCheck1297 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form6 = rawRow1297 := by decide +kernel

theorem rowCheck1297 : row1297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1297 := by decide +kernel

theorem rowEval1297 (x : Key → ℝ) : Integer.Sparse.eval row1297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1297, Integer.Sparse.eval_collectBalanced, rawRowCheck1297]

theorem rawRowCheck1298 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form6 = rawRow1298 := by decide +kernel

theorem rowCheck1298 : row1298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1298 := by decide +kernel

theorem rowEval1298 (x : Key → ℝ) : Integer.Sparse.eval row1298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1298, Integer.Sparse.eval_collectBalanced, rawRowCheck1298]

theorem rawRowCheck1299 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1299 := by decide +kernel

theorem rowCheck1299 : row1299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1299 := by decide +kernel

theorem rowEval1299 (x : Key → ℝ) : Integer.Sparse.eval row1299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1299, Integer.Sparse.eval_collectBalanced, rawRowCheck1299]

theorem rawRowCheck1300 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1300 := by decide +kernel

theorem rowCheck1300 : row1300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1300 := by decide +kernel

theorem rowEval1300 (x : Key → ℝ) : Integer.Sparse.eval row1300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1300, Integer.Sparse.eval_collectBalanced, rawRowCheck1300]

theorem rawRowCheck1301 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1301 := by decide +kernel

theorem rowCheck1301 : row1301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1301 := by decide +kernel

theorem rowEval1301 (x : Key → ℝ) : Integer.Sparse.eval row1301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1301, Integer.Sparse.eval_collectBalanced, rawRowCheck1301]

theorem rawRowCheck1302 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6 = rawRow1302 := by decide +kernel

theorem rowCheck1302 : row1302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1302 := by decide +kernel

theorem rowEval1302 (x : Key → ℝ) : Integer.Sparse.eval row1302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1302, Integer.Sparse.eval_collectBalanced, rawRowCheck1302]

theorem rawRowCheck1303 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6 = rawRow1303 := by decide +kernel

theorem rowCheck1303 : row1303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1303 := by decide +kernel

theorem rowEval1303 (x : Key → ℝ) : Integer.Sparse.eval row1303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1303, Integer.Sparse.eval_collectBalanced, rawRowCheck1303]

theorem rawRowCheck1304 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6 = rawRow1304 := by decide +kernel

theorem rowCheck1304 : row1304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1304 := by decide +kernel

theorem rowEval1304 (x : Key → ℝ) : Integer.Sparse.eval row1304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1304, Integer.Sparse.eval_collectBalanced, rawRowCheck1304]

theorem rawRowCheck1305 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6 = rawRow1305 := by decide +kernel

theorem rowCheck1305 : row1305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1305 := by decide +kernel

theorem rowEval1305 (x : Key → ℝ) : Integer.Sparse.eval row1305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1305, Integer.Sparse.eval_collectBalanced, rawRowCheck1305]

theorem rawRowCheck1306 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6 = rawRow1306 := by decide +kernel

theorem rowCheck1306 : row1306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1306 := by decide +kernel

theorem rowEval1306 (x : Key → ℝ) : Integer.Sparse.eval row1306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1306, Integer.Sparse.eval_collectBalanced, rawRowCheck1306]

theorem rawRowCheck1307 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6 = rawRow1307 := by decide +kernel

theorem rowCheck1307 : row1307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1307 := by decide +kernel

theorem rowEval1307 (x : Key → ℝ) : Integer.Sparse.eval row1307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1307, Integer.Sparse.eval_collectBalanced, rawRowCheck1307]

theorem rawRowCheck1308 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form6 = rawRow1308 := by decide +kernel

theorem rowCheck1308 : row1308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1308 := by decide +kernel

theorem rowEval1308 (x : Key → ℝ) : Integer.Sparse.eval row1308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1308, Integer.Sparse.eval_collectBalanced, rawRowCheck1308]

theorem rawRowCheck1309 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form6 = rawRow1309 := by decide +kernel

theorem rowCheck1309 : row1309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1309 := by decide +kernel

theorem rowEval1309 (x : Key → ℝ) : Integer.Sparse.eval row1309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1309, Integer.Sparse.eval_collectBalanced, rawRowCheck1309]

theorem rawRowCheck1310 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form6 = rawRow1310 := by decide +kernel

theorem rowCheck1310 : row1310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1310 := by decide +kernel

theorem rowEval1310 (x : Key → ℝ) : Integer.Sparse.eval row1310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1310, Integer.Sparse.eval_collectBalanced, rawRowCheck1310]

theorem rawRowCheck1311 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form6 = rawRow1311 := by decide +kernel

theorem rowCheck1311 : row1311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1311 := by decide +kernel

theorem rowEval1311 (x : Key → ℝ) : Integer.Sparse.eval row1311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1311, Integer.Sparse.eval_collectBalanced, rawRowCheck1311]

theorem rawRowCheck1312 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form6 = rawRow1312 := by decide +kernel

theorem rowCheck1312 : row1312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1312 := by decide +kernel

theorem rowEval1312 (x : Key → ℝ) : Integer.Sparse.eval row1312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1312, Integer.Sparse.eval_collectBalanced, rawRowCheck1312]

theorem rawRowCheck1313 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form6 = rawRow1313 := by decide +kernel

theorem rowCheck1313 : row1313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1313 := by decide +kernel

theorem rowEval1313 (x : Key → ℝ) : Integer.Sparse.eval row1313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1313, Integer.Sparse.eval_collectBalanced, rawRowCheck1313]

theorem rawRowCheck1314 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6 = rawRow1314 := by decide +kernel

theorem rowCheck1314 : row1314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1314 := by decide +kernel

theorem rowEval1314 (x : Key → ℝ) : Integer.Sparse.eval row1314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1314, Integer.Sparse.eval_collectBalanced, rawRowCheck1314]

theorem rawRowCheck1315 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6 = rawRow1315 := by decide +kernel

theorem rowCheck1315 : row1315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1315 := by decide +kernel

theorem rowEval1315 (x : Key → ℝ) : Integer.Sparse.eval row1315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1315, Integer.Sparse.eval_collectBalanced, rawRowCheck1315]

theorem rawRowCheck1316 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6 = rawRow1316 := by decide +kernel

theorem rowCheck1316 : row1316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1316 := by decide +kernel

theorem rowEval1316 (x : Key → ℝ) : Integer.Sparse.eval row1316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1316, Integer.Sparse.eval_collectBalanced, rawRowCheck1316]

theorem rawRowCheck1317 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6 = rawRow1317 := by decide +kernel

theorem rowCheck1317 : row1317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1317 := by decide +kernel

theorem rowEval1317 (x : Key → ℝ) : Integer.Sparse.eval row1317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1317, Integer.Sparse.eval_collectBalanced, rawRowCheck1317]

theorem rawRowCheck1318 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6 = rawRow1318 := by decide +kernel

theorem rowCheck1318 : row1318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1318 := by decide +kernel

theorem rowEval1318 (x : Key → ℝ) : Integer.Sparse.eval row1318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1318, Integer.Sparse.eval_collectBalanced, rawRowCheck1318]

theorem rawRowCheck1319 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6 = rawRow1319 := by decide +kernel

theorem rowCheck1319 : row1319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1319 := by decide +kernel

theorem rowEval1319 (x : Key → ℝ) : Integer.Sparse.eval row1319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1319, Integer.Sparse.eval_collectBalanced, rawRowCheck1319]

theorem rawRowCheck1320 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1320 := by decide +kernel

theorem rowCheck1320 : row1320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1320 := by decide +kernel

theorem rowEval1320 (x : Key → ℝ) : Integer.Sparse.eval row1320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1320, Integer.Sparse.eval_collectBalanced, rawRowCheck1320]

theorem rawRowCheck1321 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1321 := by decide +kernel

theorem rowCheck1321 : row1321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1321 := by decide +kernel

theorem rowEval1321 (x : Key → ℝ) : Integer.Sparse.eval row1321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1321, Integer.Sparse.eval_collectBalanced, rawRowCheck1321]

theorem rawRowCheck1322 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1322 := by decide +kernel

theorem rowCheck1322 : row1322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1322 := by decide +kernel

theorem rowEval1322 (x : Key → ℝ) : Integer.Sparse.eval row1322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1322, Integer.Sparse.eval_collectBalanced, rawRowCheck1322]

theorem rawRowCheck1323 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form7 = rawRow1323 := by decide +kernel

theorem rowCheck1323 : row1323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1323 := by decide +kernel

theorem rowEval1323 (x : Key → ℝ) : Integer.Sparse.eval row1323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1323, Integer.Sparse.eval_collectBalanced, rawRowCheck1323]

theorem rawRowCheck1324 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form7 = rawRow1324 := by decide +kernel

theorem rowCheck1324 : row1324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1324 := by decide +kernel

theorem rowEval1324 (x : Key → ℝ) : Integer.Sparse.eval row1324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1324, Integer.Sparse.eval_collectBalanced, rawRowCheck1324]

theorem rawRowCheck1325 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form7 = rawRow1325 := by decide +kernel

theorem rowCheck1325 : row1325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1325 := by decide +kernel

theorem rowEval1325 (x : Key → ℝ) : Integer.Sparse.eval row1325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1325, Integer.Sparse.eval_collectBalanced, rawRowCheck1325]

theorem rawRowCheck1326 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form7 = rawRow1326 := by decide +kernel

theorem rowCheck1326 : row1326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1326 := by decide +kernel

theorem rowEval1326 (x : Key → ℝ) : Integer.Sparse.eval row1326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1326, Integer.Sparse.eval_collectBalanced, rawRowCheck1326]

theorem rawRowCheck1327 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form7 = rawRow1327 := by decide +kernel

theorem rowCheck1327 : row1327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1327 := by decide +kernel

theorem rowEval1327 (x : Key → ℝ) : Integer.Sparse.eval row1327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1327, Integer.Sparse.eval_collectBalanced, rawRowCheck1327]

theorem rawRowCheck1328 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form7 = rawRow1328 := by decide +kernel

theorem rowCheck1328 : row1328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1328 := by decide +kernel

theorem rowEval1328 (x : Key → ℝ) : Integer.Sparse.eval row1328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1328, Integer.Sparse.eval_collectBalanced, rawRowCheck1328]

theorem rawRowCheck1329 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1329 := by decide +kernel

theorem rowCheck1329 : row1329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1329 := by decide +kernel

theorem rowEval1329 (x : Key → ℝ) : Integer.Sparse.eval row1329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1329, Integer.Sparse.eval_collectBalanced, rawRowCheck1329]

theorem rawRowCheck1330 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1330 := by decide +kernel

theorem rowCheck1330 : row1330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1330 := by decide +kernel

theorem rowEval1330 (x : Key → ℝ) : Integer.Sparse.eval row1330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1330, Integer.Sparse.eval_collectBalanced, rawRowCheck1330]

theorem rawRowCheck1331 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1331 := by decide +kernel

theorem rowCheck1331 : row1331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1331 := by decide +kernel

theorem rowEval1331 (x : Key → ℝ) : Integer.Sparse.eval row1331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1331, Integer.Sparse.eval_collectBalanced, rawRowCheck1331]

theorem rawRowCheck1332 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7 = rawRow1332 := by decide +kernel

theorem rowCheck1332 : row1332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1332 := by decide +kernel

theorem rowEval1332 (x : Key → ℝ) : Integer.Sparse.eval row1332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1332, Integer.Sparse.eval_collectBalanced, rawRowCheck1332]

theorem rawRowCheck1333 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7 = rawRow1333 := by decide +kernel

theorem rowCheck1333 : row1333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1333 := by decide +kernel

theorem rowEval1333 (x : Key → ℝ) : Integer.Sparse.eval row1333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1333, Integer.Sparse.eval_collectBalanced, rawRowCheck1333]

theorem rawRowCheck1334 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7 = rawRow1334 := by decide +kernel

theorem rowCheck1334 : row1334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1334 := by decide +kernel

theorem rowEval1334 (x : Key → ℝ) : Integer.Sparse.eval row1334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1334, Integer.Sparse.eval_collectBalanced, rawRowCheck1334]

theorem rawRowCheck1335 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7 = rawRow1335 := by decide +kernel

theorem rowCheck1335 : row1335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1335 := by decide +kernel

theorem rowEval1335 (x : Key → ℝ) : Integer.Sparse.eval row1335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1335, Integer.Sparse.eval_collectBalanced, rawRowCheck1335]

theorem rawRowCheck1336 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7 = rawRow1336 := by decide +kernel

theorem rowCheck1336 : row1336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1336 := by decide +kernel

theorem rowEval1336 (x : Key → ℝ) : Integer.Sparse.eval row1336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1336, Integer.Sparse.eval_collectBalanced, rawRowCheck1336]

theorem rawRowCheck1337 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7 = rawRow1337 := by decide +kernel

theorem rowCheck1337 : row1337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1337 := by decide +kernel

theorem rowEval1337 (x : Key → ℝ) : Integer.Sparse.eval row1337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1337, Integer.Sparse.eval_collectBalanced, rawRowCheck1337]

theorem rawRowCheck1338 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form7 = rawRow1338 := by decide +kernel

theorem rowCheck1338 : row1338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1338 := by decide +kernel

theorem rowEval1338 (x : Key → ℝ) : Integer.Sparse.eval row1338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1338, Integer.Sparse.eval_collectBalanced, rawRowCheck1338]

theorem rawRowCheck1339 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form7 = rawRow1339 := by decide +kernel

theorem rowCheck1339 : row1339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1339 := by decide +kernel

theorem rowEval1339 (x : Key → ℝ) : Integer.Sparse.eval row1339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1339, Integer.Sparse.eval_collectBalanced, rawRowCheck1339]

theorem rawRowCheck1340 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form7 = rawRow1340 := by decide +kernel

theorem rowCheck1340 : row1340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1340 := by decide +kernel

theorem rowEval1340 (x : Key → ℝ) : Integer.Sparse.eval row1340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1340, Integer.Sparse.eval_collectBalanced, rawRowCheck1340]

theorem rawRowCheck1341 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form7 = rawRow1341 := by decide +kernel

theorem rowCheck1341 : row1341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1341 := by decide +kernel

theorem rowEval1341 (x : Key → ℝ) : Integer.Sparse.eval row1341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1341, Integer.Sparse.eval_collectBalanced, rawRowCheck1341]

theorem rawRowCheck1342 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form7 = rawRow1342 := by decide +kernel

theorem rowCheck1342 : row1342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1342 := by decide +kernel

theorem rowEval1342 (x : Key → ℝ) : Integer.Sparse.eval row1342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1342, Integer.Sparse.eval_collectBalanced, rawRowCheck1342]

theorem rawRowCheck1343 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form7 = rawRow1343 := by decide +kernel

theorem rowCheck1343 : row1343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1343 := by decide +kernel

theorem rowEval1343 (x : Key → ℝ) : Integer.Sparse.eval row1343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1343, Integer.Sparse.eval_collectBalanced, rawRowCheck1343]

theorem rawRowCheck1344 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7 = rawRow1344 := by decide +kernel

theorem rowCheck1344 : row1344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1344 := by decide +kernel

theorem rowEval1344 (x : Key → ℝ) : Integer.Sparse.eval row1344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1344, Integer.Sparse.eval_collectBalanced, rawRowCheck1344]

theorem rawRowCheck1345 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7 = rawRow1345 := by decide +kernel

theorem rowCheck1345 : row1345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1345 := by decide +kernel

theorem rowEval1345 (x : Key → ℝ) : Integer.Sparse.eval row1345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1345, Integer.Sparse.eval_collectBalanced, rawRowCheck1345]

theorem rawRowCheck1346 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7 = rawRow1346 := by decide +kernel

theorem rowCheck1346 : row1346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1346 := by decide +kernel

theorem rowEval1346 (x : Key → ℝ) : Integer.Sparse.eval row1346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1346, Integer.Sparse.eval_collectBalanced, rawRowCheck1346]

theorem rawRowCheck1347 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7 = rawRow1347 := by decide +kernel

theorem rowCheck1347 : row1347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1347 := by decide +kernel

theorem rowEval1347 (x : Key → ℝ) : Integer.Sparse.eval row1347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1347, Integer.Sparse.eval_collectBalanced, rawRowCheck1347]

theorem rawRowCheck1348 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7 = rawRow1348 := by decide +kernel

theorem rowCheck1348 : row1348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1348 := by decide +kernel

theorem rowEval1348 (x : Key → ℝ) : Integer.Sparse.eval row1348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1348, Integer.Sparse.eval_collectBalanced, rawRowCheck1348]

theorem rawRowCheck1349 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7 = rawRow1349 := by decide +kernel

theorem rowCheck1349 : row1349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1349 := by decide +kernel

theorem rowEval1349 (x : Key → ℝ) : Integer.Sparse.eval row1349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1349, Integer.Sparse.eval_collectBalanced, rawRowCheck1349]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1200 x
  · exact rowEval1201 x
  · exact rowEval1202 x
  · exact rowEval1203 x
  · exact rowEval1204 x
  · exact rowEval1205 x
  · exact rowEval1206 x
  · exact rowEval1207 x
  · exact rowEval1208 x
  · exact rowEval1209 x
  · exact rowEval1210 x
  · exact rowEval1211 x
  · exact rowEval934 x
  · exact rowEval935 x
  · exact rowEval936 x
  · exact rowEval937 x
  · exact rowEval938 x
  · exact rowEval939 x
  · exact rowEval1212 x
  · exact rowEval1213 x
  · exact rowEval1214 x
  · exact rowEval1215 x
  · exact rowEval1216 x
  · exact rowEval1217 x
  · exact rowEval943 x
  · exact rowEval944 x
  · exact rowEval945 x
  · exact rowEval946 x
  · exact rowEval947 x
  · exact rowEval948 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1236 x
  · exact rowEval1237 x
  · exact rowEval1238 x
  · exact rowEval1239 x
  · exact rowEval1240 x
  · exact rowEval1241 x
  · exact rowEval1242 x
  · exact rowEval1243 x
  · exact rowEval1244 x
  · exact rowEval1245 x
  · exact rowEval1246 x
  · exact rowEval1247 x
  · exact rowEval994 x
  · exact rowEval995 x
  · exact rowEval996 x
  · exact rowEval997 x
  · exact rowEval998 x
  · exact rowEval999 x
  · exact rowEval1248 x
  · exact rowEval1249 x
  · exact rowEval1250 x
  · exact rowEval1251 x
  · exact rowEval1252 x
  · exact rowEval1253 x
  · exact rowEval1003 x
  · exact rowEval1004 x
  · exact rowEval1005 x
  · exact rowEval1006 x
  · exact rowEval1007 x
  · exact rowEval1008 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1254 x
  · exact rowEval1255 x
  · exact rowEval1256 x
  · exact rowEval1257 x
  · exact rowEval1258 x
  · exact rowEval1259 x
  · exact rowEval1260 x
  · exact rowEval1261 x
  · exact rowEval1262 x
  · exact rowEval1263 x
  · exact rowEval1264 x
  · exact rowEval1265 x
  · exact rowEval1024 x
  · exact rowEval1025 x
  · exact rowEval1026 x
  · exact rowEval1027 x
  · exact rowEval1028 x
  · exact rowEval1029 x
  · exact rowEval1266 x
  · exact rowEval1267 x
  · exact rowEval1268 x
  · exact rowEval1269 x
  · exact rowEval1270 x
  · exact rowEval1271 x
  · exact rowEval1033 x
  · exact rowEval1034 x
  · exact rowEval1035 x
  · exact rowEval1036 x
  · exact rowEval1037 x
  · exact rowEval1038 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1290 x
  · exact rowEval1291 x
  · exact rowEval1292 x
  · exact rowEval1293 x
  · exact rowEval1294 x
  · exact rowEval1295 x
  · exact rowEval1296 x
  · exact rowEval1297 x
  · exact rowEval1298 x
  · exact rowEval1299 x
  · exact rowEval1300 x
  · exact rowEval1301 x
  · exact rowEval1302 x
  · exact rowEval1303 x
  · exact rowEval1304 x
  · exact rowEval1305 x
  · exact rowEval1306 x
  · exact rowEval1307 x
  · exact rowEval1308 x
  · exact rowEval1309 x
  · exact rowEval1310 x
  · exact rowEval1311 x
  · exact rowEval1312 x
  · exact rowEval1313 x
  · exact rowEval1314 x
  · exact rowEval1315 x
  · exact rowEval1316 x
  · exact rowEval1317 x
  · exact rowEval1318 x
  · exact rowEval1319 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1320 x
  · exact rowEval1321 x
  · exact rowEval1322 x
  · exact rowEval1323 x
  · exact rowEval1324 x
  · exact rowEval1325 x
  · exact rowEval1326 x
  · exact rowEval1327 x
  · exact rowEval1328 x
  · exact rowEval1329 x
  · exact rowEval1330 x
  · exact rowEval1331 x
  · exact rowEval1332 x
  · exact rowEval1333 x
  · exact rowEval1334 x
  · exact rowEval1335 x
  · exact rowEval1336 x
  · exact rowEval1337 x
  · exact rowEval1338 x
  · exact rowEval1339 x
  · exact rowEval1340 x
  · exact rowEval1341 x
  · exact rowEval1342 x
  · exact rowEval1343 x
  · exact rowEval1344 x
  · exact rowEval1345 x
  · exact rowEval1346 x
  · exact rowEval1347 x
  · exact rowEval1348 x
  · exact rowEval1349 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1448 x
  · exact rowEval1449 x
  · exact rowEval1450 x
  · exact rowEval1451 x
  · exact rowEval1452 x
  · exact rowEval1453 x
  · exact rowEval1454 x
  · exact rowEval1455 x
  · exact rowEval1456 x
  · exact rowEval1457 x
  · exact rowEval1458 x
  · exact rowEval1459 x
  · exact rowEval1460 x
  · exact rowEval1461 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

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

theorem entryEvalRow7_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 7 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 7).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval7_0_e B hB
  · exact entryEval7_1 B hB
  · exact entryEval7_2_e B hB
  · exact entryEval7_3 B hB
  · exact entryEval7_4 B hB
  · exact entryEval7_5_e B hB
  · exact entryEval7_6 B hB
  · exact entryEval7_7 B hB
  · exact (entryEval8_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_7_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_7 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e_oai
