-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:40:24.34368+00:00
-- url     : https://prove2.me/submissions/ae5af5f6-e87e-42d2-b6ae-7e2ce56b8b3c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E020
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_4_e

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

theorem rawRowCheck1820 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1820 := by decide +kernel

theorem rowCheck1820 : row1820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1820 := by decide +kernel

theorem rowEval1820 (x : Key → ℝ) : Integer.Sparse.eval row1820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1820, Integer.Sparse.eval_collectBalanced, rawRowCheck1820]

theorem rawRowCheck1821 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1821 := by decide +kernel

theorem rowCheck1821 : row1821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1821 := by decide +kernel

theorem rowEval1821 (x : Key → ℝ) : Integer.Sparse.eval row1821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1821, Integer.Sparse.eval_collectBalanced, rawRowCheck1821]

theorem rawRowCheck1822 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1822 := by decide +kernel

theorem rowCheck1822 : row1822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1822 := by decide +kernel

theorem rowEval1822 (x : Key → ℝ) : Integer.Sparse.eval row1822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1822, Integer.Sparse.eval_collectBalanced, rawRowCheck1822]

theorem rawRowCheck1823 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1823 := by decide +kernel

theorem rowCheck1823 : row1823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1823 := by decide +kernel

theorem rowEval1823 (x : Key → ℝ) : Integer.Sparse.eval row1823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1823, Integer.Sparse.eval_collectBalanced, rawRowCheck1823]

theorem rawRowCheck1824 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form4 = rawRow1824 := by decide +kernel

theorem rowCheck1824 : row1824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1824 := by decide +kernel

theorem rowEval1824 (x : Key → ℝ) : Integer.Sparse.eval row1824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1824, Integer.Sparse.eval_collectBalanced, rawRowCheck1824]

theorem rawRowCheck1825 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form4 = rawRow1825 := by decide +kernel

theorem rowCheck1825 : row1825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1825 := by decide +kernel

theorem rowEval1825 (x : Key → ℝ) : Integer.Sparse.eval row1825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1825, Integer.Sparse.eval_collectBalanced, rawRowCheck1825]

theorem rawRowCheck1826 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form4 = rawRow1826 := by decide +kernel

theorem rowCheck1826 : row1826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1826 := by decide +kernel

theorem rowEval1826 (x : Key → ℝ) : Integer.Sparse.eval row1826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1826, Integer.Sparse.eval_collectBalanced, rawRowCheck1826]

theorem rawRowCheck1827 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1827 := by decide +kernel

theorem rowCheck1827 : row1827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1827 := by decide +kernel

theorem rowEval1827 (x : Key → ℝ) : Integer.Sparse.eval row1827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1827, Integer.Sparse.eval_collectBalanced, rawRowCheck1827]

theorem rawRowCheck1828 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1828 := by decide +kernel

theorem rowCheck1828 : row1828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1828 := by decide +kernel

theorem rowEval1828 (x : Key → ℝ) : Integer.Sparse.eval row1828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1828, Integer.Sparse.eval_collectBalanced, rawRowCheck1828]

theorem rawRowCheck1829 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1829 := by decide +kernel

theorem rowCheck1829 : row1829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1829 := by decide +kernel

theorem rowEval1829 (x : Key → ℝ) : Integer.Sparse.eval row1829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1829, Integer.Sparse.eval_collectBalanced, rawRowCheck1829]

theorem rawRowCheck1830 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1830 := by decide +kernel

theorem rowCheck1830 : row1830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1830 := by decide +kernel

theorem rowEval1830 (x : Key → ℝ) : Integer.Sparse.eval row1830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1830, Integer.Sparse.eval_collectBalanced, rawRowCheck1830]

theorem rawRowCheck1831 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1831 := by decide +kernel

theorem rowCheck1831 : row1831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1831 := by decide +kernel

theorem rowEval1831 (x : Key → ℝ) : Integer.Sparse.eval row1831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1831, Integer.Sparse.eval_collectBalanced, rawRowCheck1831]

theorem rawRowCheck1832 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1832 := by decide +kernel

theorem rowCheck1832 : row1832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1832 := by decide +kernel

theorem rowEval1832 (x : Key → ℝ) : Integer.Sparse.eval row1832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1832, Integer.Sparse.eval_collectBalanced, rawRowCheck1832]

theorem rawRowCheck1833 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1833 := by decide +kernel

theorem rowCheck1833 : row1833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1833 := by decide +kernel

theorem rowEval1833 (x : Key → ℝ) : Integer.Sparse.eval row1833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1833, Integer.Sparse.eval_collectBalanced, rawRowCheck1833]

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

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1820 x
  · exact rowEval1821 x
  · exact rowEval1822 x
  · exact rowEval1823 x
  · exact rowEval1824 x
  · exact rowEval1825 x
  · exact rowEval1826 x
  · exact rowEval1827 x
  · exact rowEval1828 x
  · exact rowEval1829 x
  · exact rowEval1830 x
  · exact rowEval1831 x
  · exact rowEval1832 x
  · exact rowEval1833 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

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

theorem rawRowCheck1974 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1974 := by decide +kernel

theorem rowCheck1974 : row1974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1974 := by decide +kernel

theorem rowEval1974 (x : Key → ℝ) : Integer.Sparse.eval row1974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1974, Integer.Sparse.eval_collectBalanced, rawRowCheck1974]

theorem rawRowCheck1975 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1975 := by decide +kernel

theorem rowCheck1975 : row1975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1975 := by decide +kernel

theorem rowEval1975 (x : Key → ℝ) : Integer.Sparse.eval row1975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1975, Integer.Sparse.eval_collectBalanced, rawRowCheck1975]

theorem rawRowCheck1976 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1976 := by decide +kernel

theorem rowCheck1976 : row1976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1976 := by decide +kernel

theorem rowEval1976 (x : Key → ℝ) : Integer.Sparse.eval row1976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1976, Integer.Sparse.eval_collectBalanced, rawRowCheck1976]

theorem rawRowCheck1977 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1977 := by decide +kernel

theorem rowCheck1977 : row1977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1977 := by decide +kernel

theorem rowEval1977 (x : Key → ℝ) : Integer.Sparse.eval row1977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1977, Integer.Sparse.eval_collectBalanced, rawRowCheck1977]

theorem rawRowCheck1978 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1978 := by decide +kernel

theorem rowCheck1978 : row1978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1978 := by decide +kernel

theorem rowEval1978 (x : Key → ℝ) : Integer.Sparse.eval row1978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1978, Integer.Sparse.eval_collectBalanced, rawRowCheck1978]

theorem rawRowCheck1979 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1979 := by decide +kernel

theorem rowCheck1979 : row1979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1979 := by decide +kernel

theorem rowEval1979 (x : Key → ℝ) : Integer.Sparse.eval row1979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1979, Integer.Sparse.eval_collectBalanced, rawRowCheck1979]

theorem rawRowCheck1980 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1980 := by decide +kernel

theorem rowCheck1980 : row1980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1980 := by decide +kernel

theorem rowEval1980 (x : Key → ℝ) : Integer.Sparse.eval row1980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1980, Integer.Sparse.eval_collectBalanced, rawRowCheck1980]

theorem rawRowCheck1981 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1981 := by decide +kernel

theorem rowCheck1981 : row1981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1981 := by decide +kernel

theorem rowEval1981 (x : Key → ℝ) : Integer.Sparse.eval row1981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1981, Integer.Sparse.eval_collectBalanced, rawRowCheck1981]

theorem rawRowCheck1982 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1982 := by decide +kernel

theorem rowCheck1982 : row1982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1982 := by decide +kernel

theorem rowEval1982 (x : Key → ℝ) : Integer.Sparse.eval row1982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1982, Integer.Sparse.eval_collectBalanced, rawRowCheck1982]

theorem rawRowCheck1983 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1983 := by decide +kernel

theorem rowCheck1983 : row1983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1983 := by decide +kernel

theorem rowEval1983 (x : Key → ℝ) : Integer.Sparse.eval row1983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1983, Integer.Sparse.eval_collectBalanced, rawRowCheck1983]

theorem rawRowCheck1984 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1984 := by decide +kernel

theorem rowCheck1984 : row1984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1984 := by decide +kernel

theorem rowEval1984 (x : Key → ℝ) : Integer.Sparse.eval row1984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1984, Integer.Sparse.eval_collectBalanced, rawRowCheck1984]

theorem rawRowCheck1985 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1985 := by decide +kernel

theorem rowCheck1985 : row1985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1985 := by decide +kernel

theorem rowEval1985 (x : Key → ℝ) : Integer.Sparse.eval row1985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1985, Integer.Sparse.eval_collectBalanced, rawRowCheck1985]

theorem rawRowCheck1986 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1986 := by decide +kernel

theorem rowCheck1986 : row1986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1986 := by decide +kernel

theorem rowEval1986 (x : Key → ℝ) : Integer.Sparse.eval row1986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1986, Integer.Sparse.eval_collectBalanced, rawRowCheck1986]

theorem rawRowCheck1987 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1987 := by decide +kernel

theorem rowCheck1987 : row1987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1987 := by decide +kernel

theorem rowEval1987 (x : Key → ℝ) : Integer.Sparse.eval row1987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1987, Integer.Sparse.eval_collectBalanced, rawRowCheck1987]

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

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1974 x
  · exact rowEval1975 x
  · exact rowEval1976 x
  · exact rowEval1977 x
  · exact rowEval1978 x
  · exact rowEval1979 x
  · exact rowEval1980 x
  · exact rowEval1981 x
  · exact rowEval1982 x
  · exact rowEval1983 x
  · exact rowEval1984 x
  · exact rowEval1985 x
  · exact rowEval1986 x
  · exact rowEval1987 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2206 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2206 := by decide +kernel

theorem rowCheck2206 : row2206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2206 := by decide +kernel

theorem rowEval2206 (x : Key → ℝ) : Integer.Sparse.eval row2206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2206, Integer.Sparse.eval_collectBalanced, rawRowCheck2206]

theorem rawRowCheck2207 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2207 := by decide +kernel

theorem rowCheck2207 : row2207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2207 := by decide +kernel

theorem rowEval2207 (x : Key → ℝ) : Integer.Sparse.eval row2207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2207, Integer.Sparse.eval_collectBalanced, rawRowCheck2207]

theorem rawRowCheck2208 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2208 := by decide +kernel

theorem rowCheck2208 : row2208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2208 := by decide +kernel

theorem rowEval2208 (x : Key → ℝ) : Integer.Sparse.eval row2208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2208, Integer.Sparse.eval_collectBalanced, rawRowCheck2208]

theorem rawRowCheck2209 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form4 = rawRow2209 := by decide +kernel

theorem rowCheck2209 : row2209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2209 := by decide +kernel

theorem rowEval2209 (x : Key → ℝ) : Integer.Sparse.eval row2209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2209, Integer.Sparse.eval_collectBalanced, rawRowCheck2209]

theorem rawRowCheck2210 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form4 = rawRow2210 := by decide +kernel

theorem rowCheck2210 : row2210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2210 := by decide +kernel

theorem rowEval2210 (x : Key → ℝ) : Integer.Sparse.eval row2210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2210, Integer.Sparse.eval_collectBalanced, rawRowCheck2210]

theorem rawRowCheck2211 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form4 = rawRow2211 := by decide +kernel

theorem rowCheck2211 : row2211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2211 := by decide +kernel

theorem rowEval2211 (x : Key → ℝ) : Integer.Sparse.eval row2211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2211, Integer.Sparse.eval_collectBalanced, rawRowCheck2211]

theorem rawRowCheck2212 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form4 = rawRow2212 := by decide +kernel

theorem rowCheck2212 : row2212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2212 := by decide +kernel

theorem rowEval2212 (x : Key → ℝ) : Integer.Sparse.eval row2212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2212, Integer.Sparse.eval_collectBalanced, rawRowCheck2212]

theorem rawRowCheck2213 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form4 = rawRow2213 := by decide +kernel

theorem rowCheck2213 : row2213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2213 := by decide +kernel

theorem rowEval2213 (x : Key → ℝ) : Integer.Sparse.eval row2213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2213, Integer.Sparse.eval_collectBalanced, rawRowCheck2213]

theorem rawRowCheck2214 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form4 = rawRow2214 := by decide +kernel

theorem rowCheck2214 : row2214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2214 := by decide +kernel

theorem rowEval2214 (x : Key → ℝ) : Integer.Sparse.eval row2214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2214, Integer.Sparse.eval_collectBalanced, rawRowCheck2214]

theorem rawRowCheck2215 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2215 := by decide +kernel

theorem rowCheck2215 : row2215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2215 := by decide +kernel

theorem rowEval2215 (x : Key → ℝ) : Integer.Sparse.eval row2215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2215, Integer.Sparse.eval_collectBalanced, rawRowCheck2215]

theorem rawRowCheck2216 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2216 := by decide +kernel

theorem rowCheck2216 : row2216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2216 := by decide +kernel

theorem rowEval2216 (x : Key → ℝ) : Integer.Sparse.eval row2216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2216, Integer.Sparse.eval_collectBalanced, rawRowCheck2216]

theorem rawRowCheck2217 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2217 := by decide +kernel

theorem rowCheck2217 : row2217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2217 := by decide +kernel

theorem rowEval2217 (x : Key → ℝ) : Integer.Sparse.eval row2217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2217, Integer.Sparse.eval_collectBalanced, rawRowCheck2217]

theorem rawRowCheck2218 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4 = rawRow2218 := by decide +kernel

theorem rowCheck2218 : row2218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2218 := by decide +kernel

theorem rowEval2218 (x : Key → ℝ) : Integer.Sparse.eval row2218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2218, Integer.Sparse.eval_collectBalanced, rawRowCheck2218]

theorem rawRowCheck2219 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4 = rawRow2219 := by decide +kernel

theorem rowCheck2219 : row2219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2219 := by decide +kernel

theorem rowEval2219 (x : Key → ℝ) : Integer.Sparse.eval row2219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2219, Integer.Sparse.eval_collectBalanced, rawRowCheck2219]

theorem rawRowCheck2220 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4 = rawRow2220 := by decide +kernel

theorem rowCheck2220 : row2220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2220 := by decide +kernel

theorem rowEval2220 (x : Key → ℝ) : Integer.Sparse.eval row2220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2220, Integer.Sparse.eval_collectBalanced, rawRowCheck2220]

theorem rawRowCheck2221 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4 = rawRow2221 := by decide +kernel

theorem rowCheck2221 : row2221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2221 := by decide +kernel

theorem rowEval2221 (x : Key → ℝ) : Integer.Sparse.eval row2221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2221, Integer.Sparse.eval_collectBalanced, rawRowCheck2221]

theorem rawRowCheck2222 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4 = rawRow2222 := by decide +kernel

theorem rowCheck2222 : row2222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2222 := by decide +kernel

theorem rowEval2222 (x : Key → ℝ) : Integer.Sparse.eval row2222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2222, Integer.Sparse.eval_collectBalanced, rawRowCheck2222]

theorem rawRowCheck2223 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4 = rawRow2223 := by decide +kernel

theorem rowCheck2223 : row2223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2223 := by decide +kernel

theorem rowEval2223 (x : Key → ℝ) : Integer.Sparse.eval row2223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2223, Integer.Sparse.eval_collectBalanced, rawRowCheck2223]

theorem rawRowCheck2224 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form4 = rawRow2224 := by decide +kernel

theorem rowCheck2224 : row2224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2224 := by decide +kernel

theorem rowEval2224 (x : Key → ℝ) : Integer.Sparse.eval row2224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2224, Integer.Sparse.eval_collectBalanced, rawRowCheck2224]

theorem rawRowCheck2225 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form4 = rawRow2225 := by decide +kernel

theorem rowCheck2225 : row2225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2225 := by decide +kernel

theorem rowEval2225 (x : Key → ℝ) : Integer.Sparse.eval row2225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2225, Integer.Sparse.eval_collectBalanced, rawRowCheck2225]

theorem rawRowCheck2226 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form4 = rawRow2226 := by decide +kernel

theorem rowCheck2226 : row2226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2226 := by decide +kernel

theorem rowEval2226 (x : Key → ℝ) : Integer.Sparse.eval row2226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2226, Integer.Sparse.eval_collectBalanced, rawRowCheck2226]

theorem rawRowCheck2227 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form4 = rawRow2227 := by decide +kernel

theorem rowCheck2227 : row2227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2227 := by decide +kernel

theorem rowEval2227 (x : Key → ℝ) : Integer.Sparse.eval row2227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2227, Integer.Sparse.eval_collectBalanced, rawRowCheck2227]

theorem rawRowCheck2228 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form4 = rawRow2228 := by decide +kernel

theorem rowCheck2228 : row2228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2228 := by decide +kernel

theorem rowEval2228 (x : Key → ℝ) : Integer.Sparse.eval row2228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2228, Integer.Sparse.eval_collectBalanced, rawRowCheck2228]

theorem rawRowCheck2229 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form4 = rawRow2229 := by decide +kernel

theorem rowCheck2229 : row2229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2229 := by decide +kernel

theorem rowEval2229 (x : Key → ℝ) : Integer.Sparse.eval row2229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2229, Integer.Sparse.eval_collectBalanced, rawRowCheck2229]

theorem rawRowCheck2230 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4 = rawRow2230 := by decide +kernel

theorem rowCheck2230 : row2230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2230 := by decide +kernel

theorem rowEval2230 (x : Key → ℝ) : Integer.Sparse.eval row2230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2230, Integer.Sparse.eval_collectBalanced, rawRowCheck2230]

theorem rawRowCheck2231 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4 = rawRow2231 := by decide +kernel

theorem rowCheck2231 : row2231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2231 := by decide +kernel

theorem rowEval2231 (x : Key → ℝ) : Integer.Sparse.eval row2231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2231, Integer.Sparse.eval_collectBalanced, rawRowCheck2231]

theorem rawRowCheck2232 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4 = rawRow2232 := by decide +kernel

theorem rowCheck2232 : row2232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2232 := by decide +kernel

theorem rowEval2232 (x : Key → ℝ) : Integer.Sparse.eval row2232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2232, Integer.Sparse.eval_collectBalanced, rawRowCheck2232]

theorem rawRowCheck2233 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4 = rawRow2233 := by decide +kernel

theorem rowCheck2233 : row2233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2233 := by decide +kernel

theorem rowEval2233 (x : Key → ℝ) : Integer.Sparse.eval row2233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2233, Integer.Sparse.eval_collectBalanced, rawRowCheck2233]

theorem rawRowCheck2234 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4 = rawRow2234 := by decide +kernel

theorem rowCheck2234 : row2234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2234 := by decide +kernel

theorem rowEval2234 (x : Key → ℝ) : Integer.Sparse.eval row2234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2234, Integer.Sparse.eval_collectBalanced, rawRowCheck2234]

theorem rawRowCheck2235 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4 = rawRow2235 := by decide +kernel

theorem rowCheck2235 : row2235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2235 := by decide +kernel

theorem rowEval2235 (x : Key → ℝ) : Integer.Sparse.eval row2235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2235, Integer.Sparse.eval_collectBalanced, rawRowCheck2235]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2532 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2532 := by decide +kernel

theorem rowCheck2532 : row2532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2532 := by decide +kernel

theorem rowEval2532 (x : Key → ℝ) : Integer.Sparse.eval row2532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2532, Integer.Sparse.eval_collectBalanced, rawRowCheck2532]

theorem rawRowCheck2533 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2533 := by decide +kernel

theorem rowCheck2533 : row2533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2533 := by decide +kernel

theorem rowEval2533 (x : Key → ℝ) : Integer.Sparse.eval row2533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2533, Integer.Sparse.eval_collectBalanced, rawRowCheck2533]

theorem rawRowCheck2534 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2534 := by decide +kernel

theorem rowCheck2534 : row2534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2534 := by decide +kernel

theorem rowEval2534 (x : Key → ℝ) : Integer.Sparse.eval row2534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2534, Integer.Sparse.eval_collectBalanced, rawRowCheck2534]

theorem rawRowCheck2535 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2535 := by decide +kernel

theorem rowCheck2535 : row2535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2535 := by decide +kernel

theorem rowEval2535 (x : Key → ℝ) : Integer.Sparse.eval row2535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2535, Integer.Sparse.eval_collectBalanced, rawRowCheck2535]

theorem rawRowCheck2536 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2536 := by decide +kernel

theorem rowCheck2536 : row2536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2536 := by decide +kernel

theorem rowEval2536 (x : Key → ℝ) : Integer.Sparse.eval row2536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2536, Integer.Sparse.eval_collectBalanced, rawRowCheck2536]

theorem rawRowCheck2537 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2537 := by decide +kernel

theorem rowCheck2537 : row2537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2537 := by decide +kernel

theorem rowEval2537 (x : Key → ℝ) : Integer.Sparse.eval row2537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2537, Integer.Sparse.eval_collectBalanced, rawRowCheck2537]

theorem rawRowCheck2538 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2538 := by decide +kernel

theorem rowCheck2538 : row2538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2538 := by decide +kernel

theorem rowEval2538 (x : Key → ℝ) : Integer.Sparse.eval row2538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2538, Integer.Sparse.eval_collectBalanced, rawRowCheck2538]

theorem rawRowCheck2539 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2539 := by decide +kernel

theorem rowCheck2539 : row2539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2539 := by decide +kernel

theorem rowEval2539 (x : Key → ℝ) : Integer.Sparse.eval row2539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2539, Integer.Sparse.eval_collectBalanced, rawRowCheck2539]

theorem rawRowCheck2540 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2540 := by decide +kernel

theorem rowCheck2540 : row2540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2540 := by decide +kernel

theorem rowEval2540 (x : Key → ℝ) : Integer.Sparse.eval row2540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2540, Integer.Sparse.eval_collectBalanced, rawRowCheck2540]

theorem rawRowCheck2541 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2541 := by decide +kernel

theorem rowCheck2541 : row2541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2541 := by decide +kernel

theorem rowEval2541 (x : Key → ℝ) : Integer.Sparse.eval row2541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2541, Integer.Sparse.eval_collectBalanced, rawRowCheck2541]

theorem rawRowCheck2542 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2542 := by decide +kernel

theorem rowCheck2542 : row2542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2542 := by decide +kernel

theorem rowEval2542 (x : Key → ℝ) : Integer.Sparse.eval row2542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2542, Integer.Sparse.eval_collectBalanced, rawRowCheck2542]

theorem rawRowCheck2543 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2543 := by decide +kernel

theorem rowCheck2543 : row2543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2543 := by decide +kernel

theorem rowEval2543 (x : Key → ℝ) : Integer.Sparse.eval row2543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2543, Integer.Sparse.eval_collectBalanced, rawRowCheck2543]

theorem rawRowCheck2544 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2544 := by decide +kernel

theorem rowCheck2544 : row2544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2544 := by decide +kernel

theorem rowEval2544 (x : Key → ℝ) : Integer.Sparse.eval row2544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2544, Integer.Sparse.eval_collectBalanced, rawRowCheck2544]

theorem rawRowCheck2545 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2545 := by decide +kernel

theorem rowCheck2545 : row2545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2545 := by decide +kernel

theorem rowEval2545 (x : Key → ℝ) : Integer.Sparse.eval row2545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2545, Integer.Sparse.eval_collectBalanced, rawRowCheck2545]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2206 x
  · exact rowEval2207 x
  · exact rowEval2208 x
  · exact rowEval2209 x
  · exact rowEval2210 x
  · exact rowEval2211 x
  · exact rowEval2212 x
  · exact rowEval2213 x
  · exact rowEval2214 x
  · exact rowEval2215 x
  · exact rowEval2216 x
  · exact rowEval2217 x
  · exact rowEval2218 x
  · exact rowEval2219 x
  · exact rowEval2220 x
  · exact rowEval2221 x
  · exact rowEval2222 x
  · exact rowEval2223 x
  · exact rowEval2224 x
  · exact rowEval2225 x
  · exact rowEval2226 x
  · exact rowEval2227 x
  · exact rowEval2228 x
  · exact rowEval2229 x
  · exact rowEval2230 x
  · exact rowEval2231 x
  · exact rowEval2232 x
  · exact rowEval2233 x
  · exact rowEval2234 x
  · exact rowEval2235 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

end MUB6.Certificate.GramEntries.Block1

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

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2532 x
  · exact rowEval2533 x
  · exact rowEval2534 x
  · exact rowEval2535 x
  · exact rowEval2536 x
  · exact rowEval2537 x
  · exact rowEval2538 x
  · exact rowEval2539 x
  · exact rowEval2540 x
  · exact rowEval2541 x
  · exact rowEval2542 x
  · exact rowEval2543 x
  · exact rowEval2544 x
  · exact rowEval2545 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2768 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form4 = rawRow2768 := by decide +kernel

theorem rowCheck2768 : row2768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2768 := by decide +kernel

theorem rowEval2768 (x : Key → ℝ) : Integer.Sparse.eval row2768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2768, Integer.Sparse.eval_collectBalanced, rawRowCheck2768]

theorem rawRowCheck2769 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form4 = rawRow2769 := by decide +kernel

theorem rowCheck2769 : row2769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2769 := by decide +kernel

theorem rowEval2769 (x : Key → ℝ) : Integer.Sparse.eval row2769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2769, Integer.Sparse.eval_collectBalanced, rawRowCheck2769]

theorem rawRowCheck2770 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form4 = rawRow2770 := by decide +kernel

theorem rowCheck2770 : row2770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2770 := by decide +kernel

theorem rowEval2770 (x : Key → ℝ) : Integer.Sparse.eval row2770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2770, Integer.Sparse.eval_collectBalanced, rawRowCheck2770]

theorem rawRowCheck2771 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2771 := by decide +kernel

theorem rowCheck2771 : row2771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2771 := by decide +kernel

theorem rowEval2771 (x : Key → ℝ) : Integer.Sparse.eval row2771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2771, Integer.Sparse.eval_collectBalanced, rawRowCheck2771]

theorem rawRowCheck2772 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2772 := by decide +kernel

theorem rowCheck2772 : row2772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2772 := by decide +kernel

theorem rowEval2772 (x : Key → ℝ) : Integer.Sparse.eval row2772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2772, Integer.Sparse.eval_collectBalanced, rawRowCheck2772]

theorem rawRowCheck2773 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2773 := by decide +kernel

theorem rowCheck2773 : row2773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2773 := by decide +kernel

theorem rowEval2773 (x : Key → ℝ) : Integer.Sparse.eval row2773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2773, Integer.Sparse.eval_collectBalanced, rawRowCheck2773]

theorem rawRowCheck2774 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form4 = rawRow2774 := by decide +kernel

theorem rowCheck2774 : row2774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2774 := by decide +kernel

theorem rowEval2774 (x : Key → ℝ) : Integer.Sparse.eval row2774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2774, Integer.Sparse.eval_collectBalanced, rawRowCheck2774]

theorem rawRowCheck2775 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form4 = rawRow2775 := by decide +kernel

theorem rowCheck2775 : row2775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2775 := by decide +kernel

theorem rowEval2775 (x : Key → ℝ) : Integer.Sparse.eval row2775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2775, Integer.Sparse.eval_collectBalanced, rawRowCheck2775]

theorem rawRowCheck2776 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form4 = rawRow2776 := by decide +kernel

theorem rowCheck2776 : row2776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2776 := by decide +kernel

theorem rowEval2776 (x : Key → ℝ) : Integer.Sparse.eval row2776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2776, Integer.Sparse.eval_collectBalanced, rawRowCheck2776]

theorem rawRowCheck2777 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form4 = rawRow2777 := by decide +kernel

theorem rowCheck2777 : row2777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2777 := by decide +kernel

theorem rowEval2777 (x : Key → ℝ) : Integer.Sparse.eval row2777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2777, Integer.Sparse.eval_collectBalanced, rawRowCheck2777]

theorem rawRowCheck2778 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form4 = rawRow2778 := by decide +kernel

theorem rowCheck2778 : row2778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2778 := by decide +kernel

theorem rowEval2778 (x : Key → ℝ) : Integer.Sparse.eval row2778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2778, Integer.Sparse.eval_collectBalanced, rawRowCheck2778]

theorem rawRowCheck2779 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form4 = rawRow2779 := by decide +kernel

theorem rowCheck2779 : row2779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2779 := by decide +kernel

theorem rowEval2779 (x : Key → ℝ) : Integer.Sparse.eval row2779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2779, Integer.Sparse.eval_collectBalanced, rawRowCheck2779]

theorem rawRowCheck2780 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form4 = rawRow2780 := by decide +kernel

theorem rowCheck2780 : row2780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2780 := by decide +kernel

theorem rowEval2780 (x : Key → ℝ) : Integer.Sparse.eval row2780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2780, Integer.Sparse.eval_collectBalanced, rawRowCheck2780]

theorem rawRowCheck2781 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form4 = rawRow2781 := by decide +kernel

theorem rowCheck2781 : row2781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2781 := by decide +kernel

theorem rowEval2781 (x : Key → ℝ) : Integer.Sparse.eval row2781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2781, Integer.Sparse.eval_collectBalanced, rawRowCheck2781]

theorem rawRowCheck2782 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form4 = rawRow2782 := by decide +kernel

theorem rowCheck2782 : row2782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2782 := by decide +kernel

theorem rowEval2782 (x : Key → ℝ) : Integer.Sparse.eval row2782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2782, Integer.Sparse.eval_collectBalanced, rawRowCheck2782]

theorem rawRowCheck2783 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow2783 := by decide +kernel

theorem rowCheck2783 : row2783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2783 := by decide +kernel

theorem rowEval2783 (x : Key → ℝ) : Integer.Sparse.eval row2783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2783, Integer.Sparse.eval_collectBalanced, rawRowCheck2783]

theorem rawRowCheck2784 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow2784 := by decide +kernel

theorem rowCheck2784 : row2784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2784 := by decide +kernel

theorem rowEval2784 (x : Key → ℝ) : Integer.Sparse.eval row2784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2784, Integer.Sparse.eval_collectBalanced, rawRowCheck2784]

theorem rawRowCheck2785 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow2785 := by decide +kernel

theorem rowCheck2785 : row2785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2785 := by decide +kernel

theorem rowEval2785 (x : Key → ℝ) : Integer.Sparse.eval row2785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2785, Integer.Sparse.eval_collectBalanced, rawRowCheck2785]

theorem rawRowCheck2786 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form4 = rawRow2786 := by decide +kernel

theorem rowCheck2786 : row2786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2786 := by decide +kernel

theorem rowEval2786 (x : Key → ℝ) : Integer.Sparse.eval row2786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2786, Integer.Sparse.eval_collectBalanced, rawRowCheck2786]

theorem rawRowCheck2787 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form4 = rawRow2787 := by decide +kernel

theorem rowCheck2787 : row2787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2787 := by decide +kernel

theorem rowEval2787 (x : Key → ℝ) : Integer.Sparse.eval row2787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2787, Integer.Sparse.eval_collectBalanced, rawRowCheck2787]

theorem rawRowCheck2788 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form4 = rawRow2788 := by decide +kernel

theorem rowCheck2788 : row2788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2788 := by decide +kernel

theorem rowEval2788 (x : Key → ℝ) : Integer.Sparse.eval row2788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2788, Integer.Sparse.eval_collectBalanced, rawRowCheck2788]

theorem rawRowCheck2789 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form4 = rawRow2789 := by decide +kernel

theorem rowCheck2789 : row2789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2789 := by decide +kernel

theorem rowEval2789 (x : Key → ℝ) : Integer.Sparse.eval row2789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2789, Integer.Sparse.eval_collectBalanced, rawRowCheck2789]

theorem rawRowCheck2790 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form4 = rawRow2790 := by decide +kernel

theorem rowCheck2790 : row2790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2790 := by decide +kernel

theorem rowEval2790 (x : Key → ℝ) : Integer.Sparse.eval row2790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2790, Integer.Sparse.eval_collectBalanced, rawRowCheck2790]

theorem rawRowCheck2791 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form4 = rawRow2791 := by decide +kernel

theorem rowCheck2791 : row2791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2791 := by decide +kernel

theorem rowEval2791 (x : Key → ℝ) : Integer.Sparse.eval row2791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck2791, Integer.Sparse.eval_collectBalanced, rawRowCheck2791]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2768 x
  · exact rowEval2769 x
  · exact rowEval2770 x
  · exact rowEval2771 x
  · exact rowEval2772 x
  · exact rowEval2773 x
  · exact rowEval2774 x
  · exact rowEval2775 x
  · exact rowEval2776 x
  · exact rowEval2777 x
  · exact rowEval2778 x
  · exact rowEval2779 x
  · exact rowEval2780 x
  · exact rowEval2781 x
  · exact rowEval2782 x
  · exact rowEval2783 x
  · exact rowEval2784 x
  · exact rowEval2785 x
  · exact rowEval2786 x
  · exact rowEval2787 x
  · exact rowEval2788 x
  · exact rowEval2789 x
  · exact rowEval2790 x
  · exact rowEval2791 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck3524 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form4 = rawRow3524 := by decide +kernel

theorem rowCheck3524 : row3524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3524 := by decide +kernel

theorem rowEval3524 (x : Key → ℝ) : Integer.Sparse.eval row3524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3524, Integer.Sparse.eval_collectBalanced, rawRowCheck3524]

theorem rawRowCheck3525 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form4 = rawRow3525 := by decide +kernel

theorem rowCheck3525 : row3525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3525 := by decide +kernel

theorem rowEval3525 (x : Key → ℝ) : Integer.Sparse.eval row3525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3525, Integer.Sparse.eval_collectBalanced, rawRowCheck3525]

theorem rawRowCheck3526 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form4 = rawRow3526 := by decide +kernel

theorem rowCheck3526 : row3526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3526 := by decide +kernel

theorem rowEval3526 (x : Key → ℝ) : Integer.Sparse.eval row3526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3526, Integer.Sparse.eval_collectBalanced, rawRowCheck3526]

theorem rawRowCheck3527 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3527 := by decide +kernel

theorem rowCheck3527 : row3527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3527 := by decide +kernel

theorem rowEval3527 (x : Key → ℝ) : Integer.Sparse.eval row3527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3527, Integer.Sparse.eval_collectBalanced, rawRowCheck3527]

theorem rawRowCheck3528 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3528 := by decide +kernel

theorem rowCheck3528 : row3528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3528 := by decide +kernel

theorem rowEval3528 (x : Key → ℝ) : Integer.Sparse.eval row3528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3528, Integer.Sparse.eval_collectBalanced, rawRowCheck3528]

theorem rawRowCheck3529 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3529 := by decide +kernel

theorem rowCheck3529 : row3529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3529 := by decide +kernel

theorem rowEval3529 (x : Key → ℝ) : Integer.Sparse.eval row3529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3529, Integer.Sparse.eval_collectBalanced, rawRowCheck3529]

theorem rawRowCheck3530 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow3530 := by decide +kernel

theorem rowCheck3530 : row3530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3530 := by decide +kernel

theorem rowEval3530 (x : Key → ℝ) : Integer.Sparse.eval row3530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3530, Integer.Sparse.eval_collectBalanced, rawRowCheck3530]

theorem rawRowCheck3531 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow3531 := by decide +kernel

theorem rowCheck3531 : row3531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3531 := by decide +kernel

theorem rowEval3531 (x : Key → ℝ) : Integer.Sparse.eval row3531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3531, Integer.Sparse.eval_collectBalanced, rawRowCheck3531]

theorem rawRowCheck3532 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow3532 := by decide +kernel

theorem rowCheck3532 : row3532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3532 := by decide +kernel

theorem rowEval3532 (x : Key → ℝ) : Integer.Sparse.eval row3532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck3532, Integer.Sparse.eval_collectBalanced, rawRowCheck3532]

theorem rawRowCheck3533 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow3533 := by decide +kernel

theorem rowCheck3533 : row3533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3533 := by decide +kernel

theorem rowEval3533 (x : Key → ℝ) : Integer.Sparse.eval row3533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3533, Integer.Sparse.eval_collectBalanced, rawRowCheck3533]

theorem rawRowCheck3534 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow3534 := by decide +kernel

theorem rowCheck3534 : row3534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3534 := by decide +kernel

theorem rowEval3534 (x : Key → ℝ) : Integer.Sparse.eval row3534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck3534, Integer.Sparse.eval_collectBalanced, rawRowCheck3534]

theorem rawRowCheck3535 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow3535 := by decide +kernel

theorem rowCheck3535 : row3535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3535 := by decide +kernel

theorem rowEval3535 (x : Key → ℝ) : Integer.Sparse.eval row3535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck3535, Integer.Sparse.eval_collectBalanced, rawRowCheck3535]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck16_4 : entry16_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_4 k)) := by decide +kernel

theorem rowsSound16_4 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2206 x
  · exact rowEval2207 x
  · exact rowEval2208 x
  · exact rowEval3524 x
  · exact rowEval3525 x
  · exact rowEval3526 x
  · exact rowEval2215 x
  · exact rowEval2216 x
  · exact rowEval2217 x
  · exact rowEval3527 x
  · exact rowEval3528 x
  · exact rowEval3529 x
  · exact rowEval3530 x
  · exact rowEval3531 x
  · exact rowEval3532 x
  · exact rowEval3533 x
  · exact rowEval3534 x
  · exact rowEval3535 x

theorem entryEval16_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_4 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck16_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_4]

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

theorem rawRowCheck4612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4612 := by decide +kernel

theorem rowCheck4612 : row4612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4612 := by decide +kernel

theorem rowEval4612 (x : Key → ℝ) : Integer.Sparse.eval row4612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4612, Integer.Sparse.eval_collectBalanced, rawRowCheck4612]

theorem rawRowCheck4613 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4613 := by decide +kernel

theorem rowCheck4613 : row4613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4613 := by decide +kernel

theorem rowEval4613 (x : Key → ℝ) : Integer.Sparse.eval row4613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4613, Integer.Sparse.eval_collectBalanced, rawRowCheck4613]

theorem rawRowCheck4614 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4614 := by decide +kernel

theorem rowCheck4614 : row4614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4614 := by decide +kernel

theorem rowEval4614 (x : Key → ℝ) : Integer.Sparse.eval row4614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4614, Integer.Sparse.eval_collectBalanced, rawRowCheck4614]

theorem rawRowCheck4615 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4615 := by decide +kernel

theorem rowCheck4615 : row4615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4615 := by decide +kernel

theorem rowEval4615 (x : Key → ℝ) : Integer.Sparse.eval row4615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4615, Integer.Sparse.eval_collectBalanced, rawRowCheck4615]

theorem rawRowCheck4616 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4616 := by decide +kernel

theorem rowCheck4616 : row4616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4616 := by decide +kernel

theorem rowEval4616 (x : Key → ℝ) : Integer.Sparse.eval row4616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4616, Integer.Sparse.eval_collectBalanced, rawRowCheck4616]

theorem rawRowCheck4617 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4617 := by decide +kernel

theorem rowCheck4617 : row4617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4617 := by decide +kernel

theorem rowEval4617 (x : Key → ℝ) : Integer.Sparse.eval row4617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4617, Integer.Sparse.eval_collectBalanced, rawRowCheck4617]

theorem rawRowCheck4618 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4618 := by decide +kernel

theorem rowCheck4618 : row4618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4618 := by decide +kernel

theorem rowEval4618 (x : Key → ℝ) : Integer.Sparse.eval row4618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4618, Integer.Sparse.eval_collectBalanced, rawRowCheck4618]

theorem rawRowCheck4619 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4619 := by decide +kernel

theorem rowCheck4619 : row4619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4619 := by decide +kernel

theorem rowEval4619 (x : Key → ℝ) : Integer.Sparse.eval row4619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4619, Integer.Sparse.eval_collectBalanced, rawRowCheck4619]

theorem rawRowCheck4620 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4620 := by decide +kernel

theorem rowCheck4620 : row4620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4620 := by decide +kernel

theorem rowEval4620 (x : Key → ℝ) : Integer.Sparse.eval row4620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4620, Integer.Sparse.eval_collectBalanced, rawRowCheck4620]

theorem rawRowCheck4621 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4621 := by decide +kernel

theorem rowCheck4621 : row4621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4621 := by decide +kernel

theorem rowEval4621 (x : Key → ℝ) : Integer.Sparse.eval row4621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4621, Integer.Sparse.eval_collectBalanced, rawRowCheck4621]

theorem rawRowCheck4622 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4622 := by decide +kernel

theorem rowCheck4622 : row4622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4622 := by decide +kernel

theorem rowEval4622 (x : Key → ℝ) : Integer.Sparse.eval row4622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4622, Integer.Sparse.eval_collectBalanced, rawRowCheck4622]

theorem rawRowCheck4623 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4623 := by decide +kernel

theorem rowCheck4623 : row4623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4623 := by decide +kernel

theorem rowEval4623 (x : Key → ℝ) : Integer.Sparse.eval row4623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4623, Integer.Sparse.eval_collectBalanced, rawRowCheck4623]

theorem rawRowCheck4624 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4624 := by decide +kernel

theorem rowCheck4624 : row4624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4624 := by decide +kernel

theorem rowEval4624 (x : Key → ℝ) : Integer.Sparse.eval row4624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4624, Integer.Sparse.eval_collectBalanced, rawRowCheck4624]

theorem rawRowCheck4625 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4625 := by decide +kernel

theorem rowCheck4625 : row4625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4625 := by decide +kernel

theorem rowEval4625 (x : Key → ℝ) : Integer.Sparse.eval row4625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4625, Integer.Sparse.eval_collectBalanced, rawRowCheck4625]

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

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4612 x
  · exact rowEval4613 x
  · exact rowEval4614 x
  · exact rowEval4615 x
  · exact rowEval4616 x
  · exact rowEval4617 x
  · exact rowEval4618 x
  · exact rowEval4619 x
  · exact rowEval4620 x
  · exact rowEval4621 x
  · exact rowEval4622 x
  · exact rowEval4623 x
  · exact rowEval4624 x
  · exact rowEval4625 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

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

theorem rawRowCheck1408 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1408 := by decide +kernel

theorem rowCheck1408 : row1408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1408 := by decide +kernel

theorem rowEval1408 (x : Key → ℝ) : Integer.Sparse.eval row1408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1408, Integer.Sparse.eval_collectBalanced, rawRowCheck1408]

theorem rawRowCheck1409 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1409 := by decide +kernel

theorem rowCheck1409 : row1409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1409 := by decide +kernel

theorem rowEval1409 (x : Key → ℝ) : Integer.Sparse.eval row1409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1409, Integer.Sparse.eval_collectBalanced, rawRowCheck1409]

theorem rawRowCheck1410 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1410 := by decide +kernel

theorem rowCheck1410 : row1410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1410 := by decide +kernel

theorem rowEval1410 (x : Key → ℝ) : Integer.Sparse.eval row1410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1410, Integer.Sparse.eval_collectBalanced, rawRowCheck1410]

theorem rawRowCheck1411 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1411 := by decide +kernel

theorem rowCheck1411 : row1411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1411 := by decide +kernel

theorem rowEval1411 (x : Key → ℝ) : Integer.Sparse.eval row1411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1411, Integer.Sparse.eval_collectBalanced, rawRowCheck1411]

theorem rawRowCheck1412 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4 = rawRow1412 := by decide +kernel

theorem rowCheck1412 : row1412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1412 := by decide +kernel

theorem rowEval1412 (x : Key → ℝ) : Integer.Sparse.eval row1412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1412, Integer.Sparse.eval_collectBalanced, rawRowCheck1412]

theorem rawRowCheck1413 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1413 := by decide +kernel

theorem rowCheck1413 : row1413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1413 := by decide +kernel

theorem rowEval1413 (x : Key → ℝ) : Integer.Sparse.eval row1413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1413, Integer.Sparse.eval_collectBalanced, rawRowCheck1413]

theorem rawRowCheck1414 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1414 := by decide +kernel

theorem rowCheck1414 : row1414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1414 := by decide +kernel

theorem rowEval1414 (x : Key → ℝ) : Integer.Sparse.eval row1414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1414, Integer.Sparse.eval_collectBalanced, rawRowCheck1414]

theorem rawRowCheck1415 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1415 := by decide +kernel

theorem rowCheck1415 : row1415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1415 := by decide +kernel

theorem rowEval1415 (x : Key → ℝ) : Integer.Sparse.eval row1415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1415, Integer.Sparse.eval_collectBalanced, rawRowCheck1415]

theorem rawRowCheck1416 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4 = rawRow1416 := by decide +kernel

theorem rowCheck1416 : row1416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1416 := by decide +kernel

theorem rowEval1416 (x : Key → ℝ) : Integer.Sparse.eval row1416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1416, Integer.Sparse.eval_collectBalanced, rawRowCheck1416]

theorem rawRowCheck1417 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4 = rawRow1417 := by decide +kernel

theorem rowCheck1417 : row1417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1417 := by decide +kernel

theorem rowEval1417 (x : Key → ℝ) : Integer.Sparse.eval row1417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1417, Integer.Sparse.eval_collectBalanced, rawRowCheck1417]

theorem rawRowCheck1418 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4 = rawRow1418 := by decide +kernel

theorem rowCheck1418 : row1418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1418 := by decide +kernel

theorem rowEval1418 (x : Key → ℝ) : Integer.Sparse.eval row1418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1418, Integer.Sparse.eval_collectBalanced, rawRowCheck1418]

theorem rawRowCheck1419 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4 = rawRow1419 := by decide +kernel

theorem rowCheck1419 : row1419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1419 := by decide +kernel

theorem rowEval1419 (x : Key → ℝ) : Integer.Sparse.eval row1419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form4) x := by
  rw [rowCheck1419, Integer.Sparse.eval_collectBalanced, rawRowCheck1419]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1584 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1584 := by decide +kernel

theorem rowCheck1584 : row1584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1584 := by decide +kernel

theorem rowEval1584 (x : Key → ℝ) : Integer.Sparse.eval row1584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1584, Integer.Sparse.eval_collectBalanced, rawRowCheck1584]

theorem rawRowCheck1585 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1585 := by decide +kernel

theorem rowCheck1585 : row1585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1585 := by decide +kernel

theorem rowEval1585 (x : Key → ℝ) : Integer.Sparse.eval row1585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1585, Integer.Sparse.eval_collectBalanced, rawRowCheck1585]

theorem rawRowCheck1586 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1586 := by decide +kernel

theorem rowCheck1586 : row1586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1586 := by decide +kernel

theorem rowEval1586 (x : Key → ℝ) : Integer.Sparse.eval row1586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1586, Integer.Sparse.eval_collectBalanced, rawRowCheck1586]

theorem rawRowCheck1593 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1593 := by decide +kernel

theorem rowCheck1593 : row1593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1593 := by decide +kernel

theorem rowEval1593 (x : Key → ℝ) : Integer.Sparse.eval row1593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1593, Integer.Sparse.eval_collectBalanced, rawRowCheck1593]

theorem rawRowCheck1594 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1594 := by decide +kernel

theorem rowCheck1594 : row1594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1594 := by decide +kernel

theorem rowEval1594 (x : Key → ℝ) : Integer.Sparse.eval row1594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1594, Integer.Sparse.eval_collectBalanced, rawRowCheck1594]

theorem rawRowCheck1595 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1595 := by decide +kernel

theorem rowCheck1595 : row1595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1595 := by decide +kernel

theorem rowEval1595 (x : Key → ℝ) : Integer.Sparse.eval row1595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1595, Integer.Sparse.eval_collectBalanced, rawRowCheck1595]

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

theorem rawRowCheck4878 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4878 := by decide +kernel

theorem rowCheck4878 : row4878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4878 := by decide +kernel

theorem rowEval4878 (x : Key → ℝ) : Integer.Sparse.eval row4878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4878, Integer.Sparse.eval_collectBalanced, rawRowCheck4878]

theorem rawRowCheck4879 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4879 := by decide +kernel

theorem rowCheck4879 : row4879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4879 := by decide +kernel

theorem rowEval4879 (x : Key → ℝ) : Integer.Sparse.eval row4879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4879, Integer.Sparse.eval_collectBalanced, rawRowCheck4879]

theorem rawRowCheck4880 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4880 := by decide +kernel

theorem rowCheck4880 : row4880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4880 := by decide +kernel

theorem rowEval4880 (x : Key → ℝ) : Integer.Sparse.eval row4880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4880, Integer.Sparse.eval_collectBalanced, rawRowCheck4880]

theorem rawRowCheck4881 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4 = rawRow4881 := by decide +kernel

theorem rowCheck4881 : row4881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4881 := by decide +kernel

theorem rowEval4881 (x : Key → ℝ) : Integer.Sparse.eval row4881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4881, Integer.Sparse.eval_collectBalanced, rawRowCheck4881]

theorem rawRowCheck4882 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4 = rawRow4882 := by decide +kernel

theorem rowCheck4882 : row4882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4882 := by decide +kernel

theorem rowEval4882 (x : Key → ℝ) : Integer.Sparse.eval row4882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4882, Integer.Sparse.eval_collectBalanced, rawRowCheck4882]

theorem rawRowCheck4883 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4 = rawRow4883 := by decide +kernel

theorem rowCheck4883 : row4883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4883 := by decide +kernel

theorem rowEval4883 (x : Key → ℝ) : Integer.Sparse.eval row4883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4883, Integer.Sparse.eval_collectBalanced, rawRowCheck4883]

theorem rawRowCheck4884 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4884 := by decide +kernel

theorem rowCheck4884 : row4884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4884 := by decide +kernel

theorem rowEval4884 (x : Key → ℝ) : Integer.Sparse.eval row4884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4884, Integer.Sparse.eval_collectBalanced, rawRowCheck4884]

theorem rawRowCheck4885 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4885 := by decide +kernel

theorem rowCheck4885 : row4885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4885 := by decide +kernel

theorem rowEval4885 (x : Key → ℝ) : Integer.Sparse.eval row4885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4885, Integer.Sparse.eval_collectBalanced, rawRowCheck4885]

theorem rawRowCheck4886 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4886 := by decide +kernel

theorem rowCheck4886 : row4886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4886 := by decide +kernel

theorem rowEval4886 (x : Key → ℝ) : Integer.Sparse.eval row4886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4886, Integer.Sparse.eval_collectBalanced, rawRowCheck4886]

theorem rawRowCheck4887 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4 = rawRow4887 := by decide +kernel

theorem rowCheck4887 : row4887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4887 := by decide +kernel

theorem rowEval4887 (x : Key → ℝ) : Integer.Sparse.eval row4887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4887, Integer.Sparse.eval_collectBalanced, rawRowCheck4887]

theorem rawRowCheck4888 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4 = rawRow4888 := by decide +kernel

theorem rowCheck4888 : row4888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4888 := by decide +kernel

theorem rowEval4888 (x : Key → ℝ) : Integer.Sparse.eval row4888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4888, Integer.Sparse.eval_collectBalanced, rawRowCheck4888]

theorem rawRowCheck4889 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4 = rawRow4889 := by decide +kernel

theorem rowCheck4889 : row4889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4889 := by decide +kernel

theorem rowEval4889 (x : Key → ℝ) : Integer.Sparse.eval row4889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4889, Integer.Sparse.eval_collectBalanced, rawRowCheck4889]

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

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4878 x
  · exact rowEval4879 x
  · exact rowEval4880 x
  · exact rowEval1584 x
  · exact rowEval1585 x
  · exact rowEval1586 x
  · exact rowEval4881 x
  · exact rowEval4882 x
  · exact rowEval4883 x
  · exact rowEval4884 x
  · exact rowEval4885 x
  · exact rowEval4886 x
  · exact rowEval1593 x
  · exact rowEval1594 x
  · exact rowEval1595 x
  · exact rowEval4887 x
  · exact rowEval4888 x
  · exact rowEval4889 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck834 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow834 := by decide +kernel

theorem rowCheck834 : row834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow834 := by decide +kernel

theorem rowEval834 (x : Key → ℝ) : Integer.Sparse.eval row834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck834, Integer.Sparse.eval_collectBalanced, rawRowCheck834]

theorem rawRowCheck835 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow835 := by decide +kernel

theorem rowCheck835 : row835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow835 := by decide +kernel

theorem rowEval835 (x : Key → ℝ) : Integer.Sparse.eval row835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck835, Integer.Sparse.eval_collectBalanced, rawRowCheck835]

theorem rawRowCheck836 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow836 := by decide +kernel

theorem rowCheck836 : row836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow836 := by decide +kernel

theorem rowEval836 (x : Key → ℝ) : Integer.Sparse.eval row836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck836, Integer.Sparse.eval_collectBalanced, rawRowCheck836]

theorem rawRowCheck837 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow837 := by decide +kernel

theorem rowCheck837 : row837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow837 := by decide +kernel

theorem rowEval837 (x : Key → ℝ) : Integer.Sparse.eval row837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck837, Integer.Sparse.eval_collectBalanced, rawRowCheck837]

theorem rawRowCheck838 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow838 := by decide +kernel

theorem rowCheck838 : row838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow838 := by decide +kernel

theorem rowEval838 (x : Key → ℝ) : Integer.Sparse.eval row838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck838, Integer.Sparse.eval_collectBalanced, rawRowCheck838]

theorem rawRowCheck839 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow839 := by decide +kernel

theorem rowCheck839 : row839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow839 := by decide +kernel

theorem rowEval839 (x : Key → ℝ) : Integer.Sparse.eval row839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck839, Integer.Sparse.eval_collectBalanced, rawRowCheck839]

theorem rawRowCheck840 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow840 := by decide +kernel

theorem rowCheck840 : row840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow840 := by decide +kernel

theorem rowEval840 (x : Key → ℝ) : Integer.Sparse.eval row840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck840, Integer.Sparse.eval_collectBalanced, rawRowCheck840]

theorem rawRowCheck841 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow841 := by decide +kernel

theorem rowCheck841 : row841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow841 := by decide +kernel

theorem rowEval841 (x : Key → ℝ) : Integer.Sparse.eval row841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck841, Integer.Sparse.eval_collectBalanced, rawRowCheck841]

theorem rawRowCheck842 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow842 := by decide +kernel

theorem rowCheck842 : row842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow842 := by decide +kernel

theorem rowEval842 (x : Key → ℝ) : Integer.Sparse.eval row842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck842, Integer.Sparse.eval_collectBalanced, rawRowCheck842]

theorem rawRowCheck843 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow843 := by decide +kernel

theorem rowCheck843 : row843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow843 := by decide +kernel

theorem rowEval843 (x : Key → ℝ) : Integer.Sparse.eval row843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck843, Integer.Sparse.eval_collectBalanced, rawRowCheck843]

theorem rawRowCheck844 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow844 := by decide +kernel

theorem rowCheck844 : row844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow844 := by decide +kernel

theorem rowEval844 (x : Key → ℝ) : Integer.Sparse.eval row844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck844, Integer.Sparse.eval_collectBalanced, rawRowCheck844]

theorem rawRowCheck845 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow845 := by decide +kernel

theorem rowCheck845 : row845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow845 := by decide +kernel

theorem rowEval845 (x : Key → ℝ) : Integer.Sparse.eval row845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck845, Integer.Sparse.eval_collectBalanced, rawRowCheck845]

theorem rawRowCheck846 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow846 := by decide +kernel

theorem rowCheck846 : row846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow846 := by decide +kernel

theorem rowEval846 (x : Key → ℝ) : Integer.Sparse.eval row846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck846, Integer.Sparse.eval_collectBalanced, rawRowCheck846]

theorem rawRowCheck847 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow847 := by decide +kernel

theorem rowCheck847 : row847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow847 := by decide +kernel

theorem rowEval847 (x : Key → ℝ) : Integer.Sparse.eval row847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck847, Integer.Sparse.eval_collectBalanced, rawRowCheck847]

theorem rawRowCheck848 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow848 := by decide +kernel

theorem rowCheck848 : row848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow848 := by decide +kernel

theorem rowEval848 (x : Key → ℝ) : Integer.Sparse.eval row848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck848, Integer.Sparse.eval_collectBalanced, rawRowCheck848]

theorem rawRowCheck849 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow849 := by decide +kernel

theorem rowCheck849 : row849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow849 := by decide +kernel

theorem rowEval849 (x : Key → ℝ) : Integer.Sparse.eval row849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck849, Integer.Sparse.eval_collectBalanced, rawRowCheck849]

theorem rawRowCheck850 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow850 := by decide +kernel

theorem rowCheck850 : row850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow850 := by decide +kernel

theorem rowEval850 (x : Key → ℝ) : Integer.Sparse.eval row850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck850, Integer.Sparse.eval_collectBalanced, rawRowCheck850]

theorem rawRowCheck851 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow851 := by decide +kernel

theorem rowCheck851 : row851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow851 := by decide +kernel

theorem rowEval851 (x : Key → ℝ) : Integer.Sparse.eval row851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck851, Integer.Sparse.eval_collectBalanced, rawRowCheck851]

theorem rawRowCheck852 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow852 := by decide +kernel

theorem rowCheck852 : row852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow852 := by decide +kernel

theorem rowEval852 (x : Key → ℝ) : Integer.Sparse.eval row852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck852, Integer.Sparse.eval_collectBalanced, rawRowCheck852]

theorem rawRowCheck853 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow853 := by decide +kernel

theorem rowCheck853 : row853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow853 := by decide +kernel

theorem rowEval853 (x : Key → ℝ) : Integer.Sparse.eval row853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck853, Integer.Sparse.eval_collectBalanced, rawRowCheck853]

theorem rawRowCheck854 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow854 := by decide +kernel

theorem rowCheck854 : row854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow854 := by decide +kernel

theorem rowEval854 (x : Key → ℝ) : Integer.Sparse.eval row854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck854, Integer.Sparse.eval_collectBalanced, rawRowCheck854]

theorem rawRowCheck855 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow855 := by decide +kernel

theorem rowCheck855 : row855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow855 := by decide +kernel

theorem rowEval855 (x : Key → ℝ) : Integer.Sparse.eval row855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck855, Integer.Sparse.eval_collectBalanced, rawRowCheck855]

theorem rawRowCheck856 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow856 := by decide +kernel

theorem rowCheck856 : row856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow856 := by decide +kernel

theorem rowEval856 (x : Key → ℝ) : Integer.Sparse.eval row856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck856, Integer.Sparse.eval_collectBalanced, rawRowCheck856]

theorem rawRowCheck857 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow857 := by decide +kernel

theorem rowCheck857 : row857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow857 := by decide +kernel

theorem rowEval857 (x : Key → ℝ) : Integer.Sparse.eval row857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck857, Integer.Sparse.eval_collectBalanced, rawRowCheck857]

theorem rawRowCheck858 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow858 := by decide +kernel

theorem rowCheck858 : row858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow858 := by decide +kernel

theorem rowEval858 (x : Key → ℝ) : Integer.Sparse.eval row858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck858, Integer.Sparse.eval_collectBalanced, rawRowCheck858]

theorem rawRowCheck859 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow859 := by decide +kernel

theorem rowCheck859 : row859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow859 := by decide +kernel

theorem rowEval859 (x : Key → ℝ) : Integer.Sparse.eval row859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck859, Integer.Sparse.eval_collectBalanced, rawRowCheck859]

theorem rawRowCheck860 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow860 := by decide +kernel

theorem rowCheck860 : row860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow860 := by decide +kernel

theorem rowEval860 (x : Key → ℝ) : Integer.Sparse.eval row860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck860, Integer.Sparse.eval_collectBalanced, rawRowCheck860]

theorem rawRowCheck861 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow861 := by decide +kernel

theorem rowCheck861 : row861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow861 := by decide +kernel

theorem rowEval861 (x : Key → ℝ) : Integer.Sparse.eval row861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck861, Integer.Sparse.eval_collectBalanced, rawRowCheck861]

theorem rawRowCheck862 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow862 := by decide +kernel

theorem rowCheck862 : row862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow862 := by decide +kernel

theorem rowEval862 (x : Key → ℝ) : Integer.Sparse.eval row862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck862, Integer.Sparse.eval_collectBalanced, rawRowCheck862]

theorem rawRowCheck863 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2 = rawRow863 := by decide +kernel

theorem rowCheck863 : row863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow863 := by decide +kernel

theorem rowEval863 (x : Key → ℝ) : Integer.Sparse.eval row863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck863, Integer.Sparse.eval_collectBalanced, rawRowCheck863]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck864 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2 = rawRow864 := by decide +kernel

theorem rowCheck864 : row864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow864 := by decide +kernel

theorem rowEval864 (x : Key → ℝ) : Integer.Sparse.eval row864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck864, Integer.Sparse.eval_collectBalanced, rawRowCheck864]

theorem rawRowCheck865 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2 = rawRow865 := by decide +kernel

theorem rowCheck865 : row865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow865 := by decide +kernel

theorem rowEval865 (x : Key → ℝ) : Integer.Sparse.eval row865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck865, Integer.Sparse.eval_collectBalanced, rawRowCheck865]

theorem rawRowCheck866 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow866 := by decide +kernel

theorem rowCheck866 : row866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow866 := by decide +kernel

theorem rowEval866 (x : Key → ℝ) : Integer.Sparse.eval row866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck866, Integer.Sparse.eval_collectBalanced, rawRowCheck866]

theorem rawRowCheck867 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2 = rawRow867 := by decide +kernel

theorem rowCheck867 : row867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow867 := by decide +kernel

theorem rowEval867 (x : Key → ℝ) : Integer.Sparse.eval row867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck867, Integer.Sparse.eval_collectBalanced, rawRowCheck867]

theorem rawRowCheck868 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2 = rawRow868 := by decide +kernel

theorem rowCheck868 : row868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow868 := by decide +kernel

theorem rowEval868 (x : Key → ℝ) : Integer.Sparse.eval row868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck868, Integer.Sparse.eval_collectBalanced, rawRowCheck868]

theorem rawRowCheck869 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2 = rawRow869 := by decide +kernel

theorem rowCheck869 : row869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow869 := by decide +kernel

theorem rowEval869 (x : Key → ℝ) : Integer.Sparse.eval row869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck869, Integer.Sparse.eval_collectBalanced, rawRowCheck869]

theorem rawRowCheck870 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow870 := by decide +kernel

theorem rowCheck870 : row870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow870 := by decide +kernel

theorem rowEval870 (x : Key → ℝ) : Integer.Sparse.eval row870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck870, Integer.Sparse.eval_collectBalanced, rawRowCheck870]

theorem rawRowCheck871 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow871 := by decide +kernel

theorem rowCheck871 : row871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow871 := by decide +kernel

theorem rowEval871 (x : Key → ℝ) : Integer.Sparse.eval row871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck871, Integer.Sparse.eval_collectBalanced, rawRowCheck871]

theorem rawRowCheck872 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow872 := by decide +kernel

theorem rowCheck872 : row872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow872 := by decide +kernel

theorem rowEval872 (x : Key → ℝ) : Integer.Sparse.eval row872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck872, Integer.Sparse.eval_collectBalanced, rawRowCheck872]

theorem rawRowCheck873 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow873 := by decide +kernel

theorem rowCheck873 : row873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow873 := by decide +kernel

theorem rowEval873 (x : Key → ℝ) : Integer.Sparse.eval row873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck873, Integer.Sparse.eval_collectBalanced, rawRowCheck873]

theorem rawRowCheck874 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow874 := by decide +kernel

theorem rowCheck874 : row874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow874 := by decide +kernel

theorem rowEval874 (x : Key → ℝ) : Integer.Sparse.eval row874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck874, Integer.Sparse.eval_collectBalanced, rawRowCheck874]

theorem rawRowCheck875 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow875 := by decide +kernel

theorem rowCheck875 : row875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow875 := by decide +kernel

theorem rowEval875 (x : Key → ℝ) : Integer.Sparse.eval row875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck875, Integer.Sparse.eval_collectBalanced, rawRowCheck875]

theorem rawRowCheck876 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow876 := by decide +kernel

theorem rowCheck876 : row876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow876 := by decide +kernel

theorem rowEval876 (x : Key → ℝ) : Integer.Sparse.eval row876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck876, Integer.Sparse.eval_collectBalanced, rawRowCheck876]

theorem rawRowCheck877 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form3 = rawRow877 := by decide +kernel

theorem rowCheck877 : row877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow877 := by decide +kernel

theorem rowEval877 (x : Key → ℝ) : Integer.Sparse.eval row877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck877, Integer.Sparse.eval_collectBalanced, rawRowCheck877]

theorem rawRowCheck878 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form3 = rawRow878 := by decide +kernel

theorem rowCheck878 : row878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow878 := by decide +kernel

theorem rowEval878 (x : Key → ℝ) : Integer.Sparse.eval row878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck878, Integer.Sparse.eval_collectBalanced, rawRowCheck878]

theorem rawRowCheck879 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form3 = rawRow879 := by decide +kernel

theorem rowCheck879 : row879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow879 := by decide +kernel

theorem rowEval879 (x : Key → ℝ) : Integer.Sparse.eval row879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck879, Integer.Sparse.eval_collectBalanced, rawRowCheck879]

theorem rawRowCheck880 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow880 := by decide +kernel

theorem rowCheck880 : row880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow880 := by decide +kernel

theorem rowEval880 (x : Key → ℝ) : Integer.Sparse.eval row880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck880, Integer.Sparse.eval_collectBalanced, rawRowCheck880]

theorem rawRowCheck881 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form3 = rawRow881 := by decide +kernel

theorem rowCheck881 : row881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow881 := by decide +kernel

theorem rowEval881 (x : Key → ℝ) : Integer.Sparse.eval row881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck881, Integer.Sparse.eval_collectBalanced, rawRowCheck881]

theorem rawRowCheck882 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form3 = rawRow882 := by decide +kernel

theorem rowCheck882 : row882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow882 := by decide +kernel

theorem rowEval882 (x : Key → ℝ) : Integer.Sparse.eval row882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck882, Integer.Sparse.eval_collectBalanced, rawRowCheck882]

theorem rawRowCheck883 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form3 = rawRow883 := by decide +kernel

theorem rowCheck883 : row883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow883 := by decide +kernel

theorem rowEval883 (x : Key → ℝ) : Integer.Sparse.eval row883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck883, Integer.Sparse.eval_collectBalanced, rawRowCheck883]

theorem rawRowCheck884 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow884 := by decide +kernel

theorem rowCheck884 : row884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow884 := by decide +kernel

theorem rowEval884 (x : Key → ℝ) : Integer.Sparse.eval row884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck884, Integer.Sparse.eval_collectBalanced, rawRowCheck884]

theorem rawRowCheck885 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow885 := by decide +kernel

theorem rowCheck885 : row885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow885 := by decide +kernel

theorem rowEval885 (x : Key → ℝ) : Integer.Sparse.eval row885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck885, Integer.Sparse.eval_collectBalanced, rawRowCheck885]

theorem rawRowCheck886 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow886 := by decide +kernel

theorem rowCheck886 : row886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow886 := by decide +kernel

theorem rowEval886 (x : Key → ℝ) : Integer.Sparse.eval row886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck886, Integer.Sparse.eval_collectBalanced, rawRowCheck886]

theorem rawRowCheck887 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow887 := by decide +kernel

theorem rowCheck887 : row887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow887 := by decide +kernel

theorem rowEval887 (x : Key → ℝ) : Integer.Sparse.eval row887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck887, Integer.Sparse.eval_collectBalanced, rawRowCheck887]

theorem rawRowCheck888 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow888 := by decide +kernel

theorem rowCheck888 : row888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow888 := by decide +kernel

theorem rowEval888 (x : Key → ℝ) : Integer.Sparse.eval row888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck888, Integer.Sparse.eval_collectBalanced, rawRowCheck888]

theorem rawRowCheck889 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow889 := by decide +kernel

theorem rowCheck889 : row889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow889 := by decide +kernel

theorem rowEval889 (x : Key → ℝ) : Integer.Sparse.eval row889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck889, Integer.Sparse.eval_collectBalanced, rawRowCheck889]

theorem rawRowCheck890 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow890 := by decide +kernel

theorem rowCheck890 : row890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow890 := by decide +kernel

theorem rowEval890 (x : Key → ℝ) : Integer.Sparse.eval row890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck890, Integer.Sparse.eval_collectBalanced, rawRowCheck890]

theorem rawRowCheck891 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form4 = rawRow891 := by decide +kernel

theorem rowCheck891 : row891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow891 := by decide +kernel

theorem rowEval891 (x : Key → ℝ) : Integer.Sparse.eval row891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck891, Integer.Sparse.eval_collectBalanced, rawRowCheck891]

theorem rawRowCheck892 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form4 = rawRow892 := by decide +kernel

theorem rowCheck892 : row892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow892 := by decide +kernel

theorem rowEval892 (x : Key → ℝ) : Integer.Sparse.eval row892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck892, Integer.Sparse.eval_collectBalanced, rawRowCheck892]

theorem rawRowCheck893 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form4 = rawRow893 := by decide +kernel

theorem rowCheck893 : row893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow893 := by decide +kernel

theorem rowEval893 (x : Key → ℝ) : Integer.Sparse.eval row893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck893, Integer.Sparse.eval_collectBalanced, rawRowCheck893]

theorem rawRowCheck894 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow894 := by decide +kernel

theorem rowCheck894 : row894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow894 := by decide +kernel

theorem rowEval894 (x : Key → ℝ) : Integer.Sparse.eval row894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck894, Integer.Sparse.eval_collectBalanced, rawRowCheck894]

theorem rawRowCheck895 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form4 = rawRow895 := by decide +kernel

theorem rowCheck895 : row895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow895 := by decide +kernel

theorem rowEval895 (x : Key → ℝ) : Integer.Sparse.eval row895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck895, Integer.Sparse.eval_collectBalanced, rawRowCheck895]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck896 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form4 = rawRow896 := by decide +kernel

theorem rowCheck896 : row896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow896 := by decide +kernel

theorem rowEval896 (x : Key → ℝ) : Integer.Sparse.eval row896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck896, Integer.Sparse.eval_collectBalanced, rawRowCheck896]

theorem rawRowCheck897 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form4 = rawRow897 := by decide +kernel

theorem rowCheck897 : row897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow897 := by decide +kernel

theorem rowEval897 (x : Key → ℝ) : Integer.Sparse.eval row897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck897, Integer.Sparse.eval_collectBalanced, rawRowCheck897]

theorem rawRowCheck898 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow898 := by decide +kernel

theorem rowCheck898 : row898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow898 := by decide +kernel

theorem rowEval898 (x : Key → ℝ) : Integer.Sparse.eval row898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck898, Integer.Sparse.eval_collectBalanced, rawRowCheck898]

theorem rawRowCheck899 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow899 := by decide +kernel

theorem rowCheck899 : row899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow899 := by decide +kernel

theorem rowEval899 (x : Key → ℝ) : Integer.Sparse.eval row899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck899, Integer.Sparse.eval_collectBalanced, rawRowCheck899]

theorem rawRowCheck900 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow900 := by decide +kernel

theorem rowCheck900 : row900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow900 := by decide +kernel

theorem rowEval900 (x : Key → ℝ) : Integer.Sparse.eval row900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck900, Integer.Sparse.eval_collectBalanced, rawRowCheck900]

theorem rawRowCheck901 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow901 := by decide +kernel

theorem rowCheck901 : row901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow901 := by decide +kernel

theorem rowEval901 (x : Key → ℝ) : Integer.Sparse.eval row901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck901, Integer.Sparse.eval_collectBalanced, rawRowCheck901]

theorem rawRowCheck902 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow902 := by decide +kernel

theorem rowCheck902 : row902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow902 := by decide +kernel

theorem rowEval902 (x : Key → ℝ) : Integer.Sparse.eval row902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck902, Integer.Sparse.eval_collectBalanced, rawRowCheck902]

theorem rawRowCheck903 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow903 := by decide +kernel

theorem rowCheck903 : row903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow903 := by decide +kernel

theorem rowEval903 (x : Key → ℝ) : Integer.Sparse.eval row903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck903, Integer.Sparse.eval_collectBalanced, rawRowCheck903]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval834 x
  · exact rowEval835 x
  · exact rowEval836 x
  · exact rowEval837 x
  · exact rowEval838 x
  · exact rowEval839 x
  · exact rowEval840 x
  · exact rowEval841 x
  · exact rowEval842 x
  · exact rowEval843 x
  · exact rowEval844 x
  · exact rowEval845 x
  · exact rowEval846 x
  · exact rowEval847 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval848 x
  · exact rowEval849 x
  · exact rowEval850 x
  · exact rowEval851 x
  · exact rowEval852 x
  · exact rowEval853 x
  · exact rowEval854 x
  · exact rowEval855 x
  · exact rowEval856 x
  · exact rowEval857 x
  · exact rowEval858 x
  · exact rowEval859 x
  · exact rowEval860 x
  · exact rowEval861 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval862 x
  · exact rowEval863 x
  · exact rowEval864 x
  · exact rowEval865 x
  · exact rowEval866 x
  · exact rowEval867 x
  · exact rowEval868 x
  · exact rowEval869 x
  · exact rowEval870 x
  · exact rowEval871 x
  · exact rowEval872 x
  · exact rowEval873 x
  · exact rowEval874 x
  · exact rowEval875 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval876 x
  · exact rowEval877 x
  · exact rowEval878 x
  · exact rowEval879 x
  · exact rowEval880 x
  · exact rowEval881 x
  · exact rowEval882 x
  · exact rowEval883 x
  · exact rowEval884 x
  · exact rowEval885 x
  · exact rowEval886 x
  · exact rowEval887 x
  · exact rowEval888 x
  · exact rowEval889 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval890 x
  · exact rowEval891 x
  · exact rowEval892 x
  · exact rowEval893 x
  · exact rowEval894 x
  · exact rowEval895 x
  · exact rowEval896 x
  · exact rowEval897 x
  · exact rowEval898 x
  · exact rowEval899 x
  · exact rowEval900 x
  · exact rowEval901 x
  · exact rowEval902 x
  · exact rowEval903 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1030 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4 = rawRow1030 := by decide +kernel

theorem rowCheck1030 : row1030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1030 := by decide +kernel

theorem rowEval1030 (x : Key → ℝ) : Integer.Sparse.eval row1030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1030, Integer.Sparse.eval_collectBalanced, rawRowCheck1030]

theorem rawRowCheck1031 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4 = rawRow1031 := by decide +kernel

theorem rowCheck1031 : row1031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1031 := by decide +kernel

theorem rowEval1031 (x : Key → ℝ) : Integer.Sparse.eval row1031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1031, Integer.Sparse.eval_collectBalanced, rawRowCheck1031]

theorem rawRowCheck1032 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4 = rawRow1032 := by decide +kernel

theorem rowCheck1032 : row1032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1032 := by decide +kernel

theorem rowEval1032 (x : Key → ℝ) : Integer.Sparse.eval row1032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1032, Integer.Sparse.eval_collectBalanced, rawRowCheck1032]

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

theorem rawRowCheck1039 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4 = rawRow1039 := by decide +kernel

theorem rowCheck1039 : row1039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1039 := by decide +kernel

theorem rowEval1039 (x : Key → ℝ) : Integer.Sparse.eval row1039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1039, Integer.Sparse.eval_collectBalanced, rawRowCheck1039]

theorem rawRowCheck1040 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4 = rawRow1040 := by decide +kernel

theorem rowCheck1040 : row1040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1040 := by decide +kernel

theorem rowEval1040 (x : Key → ℝ) : Integer.Sparse.eval row1040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1040, Integer.Sparse.eval_collectBalanced, rawRowCheck1040]

theorem rawRowCheck1041 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4 = rawRow1041 := by decide +kernel

theorem rowCheck1041 : row1041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1041 := by decide +kernel

theorem rowEval1041 (x : Key → ℝ) : Integer.Sparse.eval row1041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1041, Integer.Sparse.eval_collectBalanced, rawRowCheck1041]

theorem rawRowCheck1042 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4 = rawRow1042 := by decide +kernel

theorem rowCheck1042 : row1042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1042 := by decide +kernel

theorem rowEval1042 (x : Key → ℝ) : Integer.Sparse.eval row1042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1042, Integer.Sparse.eval_collectBalanced, rawRowCheck1042]

theorem rawRowCheck1043 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4 = rawRow1043 := by decide +kernel

theorem rowCheck1043 : row1043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1043 := by decide +kernel

theorem rowEval1043 (x : Key → ℝ) : Integer.Sparse.eval row1043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1043, Integer.Sparse.eval_collectBalanced, rawRowCheck1043]

theorem rawRowCheck1044 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4 = rawRow1044 := by decide +kernel

theorem rowCheck1044 : row1044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1044 := by decide +kernel

theorem rowEval1044 (x : Key → ℝ) : Integer.Sparse.eval row1044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1044, Integer.Sparse.eval_collectBalanced, rawRowCheck1044]

theorem rawRowCheck1045 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow1045 := by decide +kernel

theorem rowCheck1045 : row1045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1045 := by decide +kernel

theorem rowEval1045 (x : Key → ℝ) : Integer.Sparse.eval row1045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1045, Integer.Sparse.eval_collectBalanced, rawRowCheck1045]

theorem rawRowCheck1046 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow1046 := by decide +kernel

theorem rowCheck1046 : row1046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1046 := by decide +kernel

theorem rowEval1046 (x : Key → ℝ) : Integer.Sparse.eval row1046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1046, Integer.Sparse.eval_collectBalanced, rawRowCheck1046]

theorem rawRowCheck1047 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow1047 := by decide +kernel

theorem rowCheck1047 : row1047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1047 := by decide +kernel

theorem rowEval1047 (x : Key → ℝ) : Integer.Sparse.eval row1047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1047, Integer.Sparse.eval_collectBalanced, rawRowCheck1047]

theorem rawRowCheck1048 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4 = rawRow1048 := by decide +kernel

theorem rowCheck1048 : row1048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1048 := by decide +kernel

theorem rowEval1048 (x : Key → ℝ) : Integer.Sparse.eval row1048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1048, Integer.Sparse.eval_collectBalanced, rawRowCheck1048]

theorem rawRowCheck1049 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4 = rawRow1049 := by decide +kernel

theorem rowCheck1049 : row1049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1049 := by decide +kernel

theorem rowEval1049 (x : Key → ℝ) : Integer.Sparse.eval row1049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1049, Integer.Sparse.eval_collectBalanced, rawRowCheck1049]

theorem rawRowCheck1050 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4 = rawRow1050 := by decide +kernel

theorem rowCheck1050 : row1050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1050 := by decide +kernel

theorem rowEval1050 (x : Key → ℝ) : Integer.Sparse.eval row1050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1050, Integer.Sparse.eval_collectBalanced, rawRowCheck1050]

theorem rawRowCheck1051 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4 = rawRow1051 := by decide +kernel

theorem rowCheck1051 : row1051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1051 := by decide +kernel

theorem rowEval1051 (x : Key → ℝ) : Integer.Sparse.eval row1051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1051, Integer.Sparse.eval_collectBalanced, rawRowCheck1051]

theorem rawRowCheck1052 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4 = rawRow1052 := by decide +kernel

theorem rowCheck1052 : row1052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1052 := by decide +kernel

theorem rowEval1052 (x : Key → ℝ) : Integer.Sparse.eval row1052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1052, Integer.Sparse.eval_collectBalanced, rawRowCheck1052]

theorem rawRowCheck1053 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4 = rawRow1053 := by decide +kernel

theorem rowCheck1053 : row1053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1053 := by decide +kernel

theorem rowEval1053 (x : Key → ℝ) : Integer.Sparse.eval row1053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1053, Integer.Sparse.eval_collectBalanced, rawRowCheck1053]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1024 x
  · exact rowEval1025 x
  · exact rowEval1026 x
  · exact rowEval1027 x
  · exact rowEval1028 x
  · exact rowEval1029 x
  · exact rowEval1030 x
  · exact rowEval1031 x
  · exact rowEval1032 x
  · exact rowEval1033 x
  · exact rowEval1034 x
  · exact rowEval1035 x
  · exact rowEval1036 x
  · exact rowEval1037 x
  · exact rowEval1038 x
  · exact rowEval1039 x
  · exact rowEval1040 x
  · exact rowEval1041 x
  · exact rowEval1042 x
  · exact rowEval1043 x
  · exact rowEval1044 x
  · exact rowEval1045 x
  · exact rowEval1046 x
  · exact rowEval1047 x
  · exact rowEval1048 x
  · exact rowEval1049 x
  · exact rowEval1050 x
  · exact rowEval1051 x
  · exact rowEval1052 x
  · exact rowEval1053 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1140 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form4 = rawRow1140 := by decide +kernel

theorem rowCheck1140 : row1140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1140 := by decide +kernel

theorem rowEval1140 (x : Key → ℝ) : Integer.Sparse.eval row1140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1140, Integer.Sparse.eval_collectBalanced, rawRowCheck1140]

theorem rawRowCheck1141 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form4 = rawRow1141 := by decide +kernel

theorem rowCheck1141 : row1141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1141 := by decide +kernel

theorem rowEval1141 (x : Key → ℝ) : Integer.Sparse.eval row1141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1141, Integer.Sparse.eval_collectBalanced, rawRowCheck1141]

theorem rawRowCheck1142 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form4 = rawRow1142 := by decide +kernel

theorem rowCheck1142 : row1142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1142 := by decide +kernel

theorem rowEval1142 (x : Key → ℝ) : Integer.Sparse.eval row1142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1142, Integer.Sparse.eval_collectBalanced, rawRowCheck1142]

theorem rawRowCheck1143 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form4 = rawRow1143 := by decide +kernel

theorem rowCheck1143 : row1143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1143 := by decide +kernel

theorem rowEval1143 (x : Key → ℝ) : Integer.Sparse.eval row1143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1143, Integer.Sparse.eval_collectBalanced, rawRowCheck1143]

theorem rawRowCheck1144 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form4 = rawRow1144 := by decide +kernel

theorem rowCheck1144 : row1144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1144 := by decide +kernel

theorem rowEval1144 (x : Key → ℝ) : Integer.Sparse.eval row1144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1144, Integer.Sparse.eval_collectBalanced, rawRowCheck1144]

theorem rawRowCheck1145 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form4 = rawRow1145 := by decide +kernel

theorem rowCheck1145 : row1145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1145 := by decide +kernel

theorem rowEval1145 (x : Key → ℝ) : Integer.Sparse.eval row1145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1145, Integer.Sparse.eval_collectBalanced, rawRowCheck1145]

theorem rawRowCheck1146 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form4 = rawRow1146 := by decide +kernel

theorem rowCheck1146 : row1146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1146 := by decide +kernel

theorem rowEval1146 (x : Key → ℝ) : Integer.Sparse.eval row1146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1146, Integer.Sparse.eval_collectBalanced, rawRowCheck1146]

theorem rawRowCheck1147 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form4 = rawRow1147 := by decide +kernel

theorem rowCheck1147 : row1147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1147 := by decide +kernel

theorem rowEval1147 (x : Key → ℝ) : Integer.Sparse.eval row1147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1147, Integer.Sparse.eval_collectBalanced, rawRowCheck1147]

theorem rawRowCheck1148 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form4 = rawRow1148 := by decide +kernel

theorem rowCheck1148 : row1148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1148 := by decide +kernel

theorem rowEval1148 (x : Key → ℝ) : Integer.Sparse.eval row1148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1148, Integer.Sparse.eval_collectBalanced, rawRowCheck1148]

theorem rawRowCheck1149 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form4 = rawRow1149 := by decide +kernel

theorem rowCheck1149 : row1149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1149 := by decide +kernel

theorem rowEval1149 (x : Key → ℝ) : Integer.Sparse.eval row1149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1149, Integer.Sparse.eval_collectBalanced, rawRowCheck1149]

theorem rawRowCheck1150 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form4 = rawRow1150 := by decide +kernel

theorem rowCheck1150 : row1150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1150 := by decide +kernel

theorem rowEval1150 (x : Key → ℝ) : Integer.Sparse.eval row1150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1150, Integer.Sparse.eval_collectBalanced, rawRowCheck1150]

theorem rawRowCheck1151 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form4 = rawRow1151 := by decide +kernel

theorem rowCheck1151 : row1151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1151 := by decide +kernel

theorem rowEval1151 (x : Key → ℝ) : Integer.Sparse.eval row1151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1151, Integer.Sparse.eval_collectBalanced, rawRowCheck1151]

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

theorem rawRowCheck1152 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form4 = rawRow1152 := by decide +kernel

theorem rowCheck1152 : row1152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1152 := by decide +kernel

theorem rowEval1152 (x : Key → ℝ) : Integer.Sparse.eval row1152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1152, Integer.Sparse.eval_collectBalanced, rawRowCheck1152]

theorem rawRowCheck1153 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form4 = rawRow1153 := by decide +kernel

theorem rowCheck1153 : row1153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1153 := by decide +kernel

theorem rowEval1153 (x : Key → ℝ) : Integer.Sparse.eval row1153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1153, Integer.Sparse.eval_collectBalanced, rawRowCheck1153]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1140 x
  · exact rowEval1141 x
  · exact rowEval1142 x
  · exact rowEval1143 x
  · exact rowEval1144 x
  · exact rowEval1145 x
  · exact rowEval1146 x
  · exact rowEval1147 x
  · exact rowEval1148 x
  · exact rowEval1149 x
  · exact rowEval1150 x
  · exact rowEval1151 x
  · exact rowEval1152 x
  · exact rowEval1153 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1406 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1406 := by decide +kernel

theorem rowCheck1406 : row1406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1406 := by decide +kernel

theorem rowEval1406 (x : Key → ℝ) : Integer.Sparse.eval row1406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1406, Integer.Sparse.eval_collectBalanced, rawRowCheck1406]

theorem rawRowCheck1407 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1407 := by decide +kernel

theorem rowCheck1407 : row1407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1407 := by decide +kernel

theorem rowEval1407 (x : Key → ℝ) : Integer.Sparse.eval row1407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1407, Integer.Sparse.eval_collectBalanced, rawRowCheck1407]

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

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1406 x
  · exact rowEval1407 x
  · exact rowEval1408 x
  · exact rowEval1409 x
  · exact rowEval1410 x
  · exact rowEval1411 x
  · exact rowEval1412 x
  · exact rowEval1413 x
  · exact rowEval1414 x
  · exact rowEval1415 x
  · exact rowEval1416 x
  · exact rowEval1417 x
  · exact rowEval1418 x
  · exact rowEval1419 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

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

theorem entryEvalRow4_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 4).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e_oai
