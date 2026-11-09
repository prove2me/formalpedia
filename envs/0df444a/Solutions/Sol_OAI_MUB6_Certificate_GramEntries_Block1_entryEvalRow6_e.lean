-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:30:31.62779+00:00
-- url     : https://prove2.me/submissions/72131b8c-33ce-4dd1-86a2-33b6dc054ec0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E020
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
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_6_e

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

theorem rawRowCheck1848 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1848 := by decide +kernel

theorem rowCheck1848 : row1848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1848 := by decide +kernel

theorem rowEval1848 (x : Key → ℝ) : Integer.Sparse.eval row1848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1848, Integer.Sparse.eval_collectBalanced, rawRowCheck1848]

theorem rawRowCheck1849 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1849 := by decide +kernel

theorem rowCheck1849 : row1849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1849 := by decide +kernel

theorem rowEval1849 (x : Key → ℝ) : Integer.Sparse.eval row1849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1849, Integer.Sparse.eval_collectBalanced, rawRowCheck1849]

theorem rawRowCheck1850 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1850 := by decide +kernel

theorem rowCheck1850 : row1850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1850 := by decide +kernel

theorem rowEval1850 (x : Key → ℝ) : Integer.Sparse.eval row1850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1850, Integer.Sparse.eval_collectBalanced, rawRowCheck1850]

theorem rawRowCheck1851 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1851 := by decide +kernel

theorem rowCheck1851 : row1851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1851 := by decide +kernel

theorem rowEval1851 (x : Key → ℝ) : Integer.Sparse.eval row1851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1851, Integer.Sparse.eval_collectBalanced, rawRowCheck1851]

theorem rawRowCheck1852 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1852 := by decide +kernel

theorem rowCheck1852 : row1852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1852 := by decide +kernel

theorem rowEval1852 (x : Key → ℝ) : Integer.Sparse.eval row1852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1852, Integer.Sparse.eval_collectBalanced, rawRowCheck1852]

theorem rawRowCheck1853 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1853 := by decide +kernel

theorem rowCheck1853 : row1853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1853 := by decide +kernel

theorem rowEval1853 (x : Key → ℝ) : Integer.Sparse.eval row1853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1853, Integer.Sparse.eval_collectBalanced, rawRowCheck1853]

theorem rawRowCheck1854 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1854 := by decide +kernel

theorem rowCheck1854 : row1854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1854 := by decide +kernel

theorem rowEval1854 (x : Key → ℝ) : Integer.Sparse.eval row1854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1854, Integer.Sparse.eval_collectBalanced, rawRowCheck1854]

theorem rawRowCheck1855 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1855 := by decide +kernel

theorem rowCheck1855 : row1855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1855 := by decide +kernel

theorem rowEval1855 (x : Key → ℝ) : Integer.Sparse.eval row1855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1855, Integer.Sparse.eval_collectBalanced, rawRowCheck1855]

theorem rawRowCheck1856 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1856 := by decide +kernel

theorem rowCheck1856 : row1856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1856 := by decide +kernel

theorem rowEval1856 (x : Key → ℝ) : Integer.Sparse.eval row1856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1856, Integer.Sparse.eval_collectBalanced, rawRowCheck1856]

theorem rawRowCheck1857 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1857 := by decide +kernel

theorem rowCheck1857 : row1857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1857 := by decide +kernel

theorem rowEval1857 (x : Key → ℝ) : Integer.Sparse.eval row1857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1857, Integer.Sparse.eval_collectBalanced, rawRowCheck1857]

theorem rawRowCheck1858 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1858 := by decide +kernel

theorem rowCheck1858 : row1858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1858 := by decide +kernel

theorem rowEval1858 (x : Key → ℝ) : Integer.Sparse.eval row1858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1858, Integer.Sparse.eval_collectBalanced, rawRowCheck1858]

theorem rawRowCheck1859 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1859 := by decide +kernel

theorem rowCheck1859 : row1859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1859 := by decide +kernel

theorem rowEval1859 (x : Key → ℝ) : Integer.Sparse.eval row1859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1859, Integer.Sparse.eval_collectBalanced, rawRowCheck1859]

theorem rawRowCheck1860 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1860 := by decide +kernel

theorem rowCheck1860 : row1860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1860 := by decide +kernel

theorem rowEval1860 (x : Key → ℝ) : Integer.Sparse.eval row1860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1860, Integer.Sparse.eval_collectBalanced, rawRowCheck1860]

theorem rawRowCheck1861 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1861 := by decide +kernel

theorem rowCheck1861 : row1861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1861 := by decide +kernel

theorem rowEval1861 (x : Key → ℝ) : Integer.Sparse.eval row1861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1861, Integer.Sparse.eval_collectBalanced, rawRowCheck1861]

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

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1848 x
  · exact rowEval1849 x
  · exact rowEval1850 x
  · exact rowEval1851 x
  · exact rowEval1852 x
  · exact rowEval1853 x
  · exact rowEval1854 x
  · exact rowEval1855 x
  · exact rowEval1856 x
  · exact rowEval1857 x
  · exact rowEval1858 x
  · exact rowEval1859 x
  · exact rowEval1860 x
  · exact rowEval1861 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

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

theorem rawRowCheck2002 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2002 := by decide +kernel

theorem rowCheck2002 : row2002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2002 := by decide +kernel

theorem rowEval2002 (x : Key → ℝ) : Integer.Sparse.eval row2002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2002, Integer.Sparse.eval_collectBalanced, rawRowCheck2002]

theorem rawRowCheck2003 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2003 := by decide +kernel

theorem rowCheck2003 : row2003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2003 := by decide +kernel

theorem rowEval2003 (x : Key → ℝ) : Integer.Sparse.eval row2003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2003, Integer.Sparse.eval_collectBalanced, rawRowCheck2003]

theorem rawRowCheck2004 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2004 := by decide +kernel

theorem rowCheck2004 : row2004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2004 := by decide +kernel

theorem rowEval2004 (x : Key → ℝ) : Integer.Sparse.eval row2004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2004, Integer.Sparse.eval_collectBalanced, rawRowCheck2004]

theorem rawRowCheck2005 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2005 := by decide +kernel

theorem rowCheck2005 : row2005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2005 := by decide +kernel

theorem rowEval2005 (x : Key → ℝ) : Integer.Sparse.eval row2005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2005, Integer.Sparse.eval_collectBalanced, rawRowCheck2005]

theorem rawRowCheck2006 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2006 := by decide +kernel

theorem rowCheck2006 : row2006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2006 := by decide +kernel

theorem rowEval2006 (x : Key → ℝ) : Integer.Sparse.eval row2006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2006, Integer.Sparse.eval_collectBalanced, rawRowCheck2006]

theorem rawRowCheck2007 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2007 := by decide +kernel

theorem rowCheck2007 : row2007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2007 := by decide +kernel

theorem rowEval2007 (x : Key → ℝ) : Integer.Sparse.eval row2007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2007, Integer.Sparse.eval_collectBalanced, rawRowCheck2007]

theorem rawRowCheck2008 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2008 := by decide +kernel

theorem rowCheck2008 : row2008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2008 := by decide +kernel

theorem rowEval2008 (x : Key → ℝ) : Integer.Sparse.eval row2008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2008, Integer.Sparse.eval_collectBalanced, rawRowCheck2008]

theorem rawRowCheck2009 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6 = rawRow2009 := by decide +kernel

theorem rowCheck2009 : row2009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2009 := by decide +kernel

theorem rowEval2009 (x : Key → ℝ) : Integer.Sparse.eval row2009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2009, Integer.Sparse.eval_collectBalanced, rawRowCheck2009]

theorem rawRowCheck2010 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6 = rawRow2010 := by decide +kernel

theorem rowCheck2010 : row2010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2010 := by decide +kernel

theorem rowEval2010 (x : Key → ℝ) : Integer.Sparse.eval row2010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2010, Integer.Sparse.eval_collectBalanced, rawRowCheck2010]

theorem rawRowCheck2011 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6 = rawRow2011 := by decide +kernel

theorem rowCheck2011 : row2011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2011 := by decide +kernel

theorem rowEval2011 (x : Key → ℝ) : Integer.Sparse.eval row2011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2011, Integer.Sparse.eval_collectBalanced, rawRowCheck2011]

theorem rawRowCheck2012 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2012 := by decide +kernel

theorem rowCheck2012 : row2012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2012 := by decide +kernel

theorem rowEval2012 (x : Key → ℝ) : Integer.Sparse.eval row2012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2012, Integer.Sparse.eval_collectBalanced, rawRowCheck2012]

theorem rawRowCheck2013 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow2013 := by decide +kernel

theorem rowCheck2013 : row2013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2013 := by decide +kernel

theorem rowEval2013 (x : Key → ℝ) : Integer.Sparse.eval row2013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2013, Integer.Sparse.eval_collectBalanced, rawRowCheck2013]

theorem rawRowCheck2014 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow2014 := by decide +kernel

theorem rowCheck2014 : row2014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2014 := by decide +kernel

theorem rowEval2014 (x : Key → ℝ) : Integer.Sparse.eval row2014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2014, Integer.Sparse.eval_collectBalanced, rawRowCheck2014]

theorem rawRowCheck2015 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow2015 := by decide +kernel

theorem rowCheck2015 : row2015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2015 := by decide +kernel

theorem rowEval2015 (x : Key → ℝ) : Integer.Sparse.eval row2015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2015, Integer.Sparse.eval_collectBalanced, rawRowCheck2015]

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

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2002 x
  · exact rowEval2003 x
  · exact rowEval2004 x
  · exact rowEval2005 x
  · exact rowEval2006 x
  · exact rowEval2007 x
  · exact rowEval2008 x
  · exact rowEval2009 x
  · exact rowEval2010 x
  · exact rowEval2011 x
  · exact rowEval2012 x
  · exact rowEval2013 x
  · exact rowEval2014 x
  · exact rowEval2015 x

theorem entryEval11_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

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

theorem rawRowCheck2266 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2266 := by decide +kernel

theorem rowCheck2266 : row2266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2266 := by decide +kernel

theorem rowEval2266 (x : Key → ℝ) : Integer.Sparse.eval row2266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2266, Integer.Sparse.eval_collectBalanced, rawRowCheck2266]

theorem rawRowCheck2267 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2267 := by decide +kernel

theorem rowCheck2267 : row2267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2267 := by decide +kernel

theorem rowEval2267 (x : Key → ℝ) : Integer.Sparse.eval row2267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2267, Integer.Sparse.eval_collectBalanced, rawRowCheck2267]

theorem rawRowCheck2268 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2268 := by decide +kernel

theorem rowCheck2268 : row2268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2268 := by decide +kernel

theorem rowEval2268 (x : Key → ℝ) : Integer.Sparse.eval row2268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2268, Integer.Sparse.eval_collectBalanced, rawRowCheck2268]

theorem rawRowCheck2269 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form6 = rawRow2269 := by decide +kernel

theorem rowCheck2269 : row2269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2269 := by decide +kernel

theorem rowEval2269 (x : Key → ℝ) : Integer.Sparse.eval row2269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2269, Integer.Sparse.eval_collectBalanced, rawRowCheck2269]

theorem rawRowCheck2270 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form6 = rawRow2270 := by decide +kernel

theorem rowCheck2270 : row2270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2270 := by decide +kernel

theorem rowEval2270 (x : Key → ℝ) : Integer.Sparse.eval row2270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2270, Integer.Sparse.eval_collectBalanced, rawRowCheck2270]

theorem rawRowCheck2271 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form6 = rawRow2271 := by decide +kernel

theorem rowCheck2271 : row2271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2271 := by decide +kernel

theorem rowEval2271 (x : Key → ℝ) : Integer.Sparse.eval row2271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2271, Integer.Sparse.eval_collectBalanced, rawRowCheck2271]

theorem rawRowCheck2272 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form6 = rawRow2272 := by decide +kernel

theorem rowCheck2272 : row2272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2272 := by decide +kernel

theorem rowEval2272 (x : Key → ℝ) : Integer.Sparse.eval row2272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2272, Integer.Sparse.eval_collectBalanced, rawRowCheck2272]

theorem rawRowCheck2273 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form6 = rawRow2273 := by decide +kernel

theorem rowCheck2273 : row2273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2273 := by decide +kernel

theorem rowEval2273 (x : Key → ℝ) : Integer.Sparse.eval row2273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2273, Integer.Sparse.eval_collectBalanced, rawRowCheck2273]

theorem rawRowCheck2274 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form6 = rawRow2274 := by decide +kernel

theorem rowCheck2274 : row2274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2274 := by decide +kernel

theorem rowEval2274 (x : Key → ℝ) : Integer.Sparse.eval row2274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2274, Integer.Sparse.eval_collectBalanced, rawRowCheck2274]

theorem rawRowCheck2275 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2275 := by decide +kernel

theorem rowCheck2275 : row2275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2275 := by decide +kernel

theorem rowEval2275 (x : Key → ℝ) : Integer.Sparse.eval row2275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2275, Integer.Sparse.eval_collectBalanced, rawRowCheck2275]

theorem rawRowCheck2276 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2276 := by decide +kernel

theorem rowCheck2276 : row2276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2276 := by decide +kernel

theorem rowEval2276 (x : Key → ℝ) : Integer.Sparse.eval row2276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2276, Integer.Sparse.eval_collectBalanced, rawRowCheck2276]

theorem rawRowCheck2277 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2277 := by decide +kernel

theorem rowCheck2277 : row2277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2277 := by decide +kernel

theorem rowEval2277 (x : Key → ℝ) : Integer.Sparse.eval row2277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2277, Integer.Sparse.eval_collectBalanced, rawRowCheck2277]

theorem rawRowCheck2278 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6 = rawRow2278 := by decide +kernel

theorem rowCheck2278 : row2278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2278 := by decide +kernel

theorem rowEval2278 (x : Key → ℝ) : Integer.Sparse.eval row2278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2278, Integer.Sparse.eval_collectBalanced, rawRowCheck2278]

theorem rawRowCheck2279 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6 = rawRow2279 := by decide +kernel

theorem rowCheck2279 : row2279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2279 := by decide +kernel

theorem rowEval2279 (x : Key → ℝ) : Integer.Sparse.eval row2279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2279, Integer.Sparse.eval_collectBalanced, rawRowCheck2279]

theorem rawRowCheck2280 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6 = rawRow2280 := by decide +kernel

theorem rowCheck2280 : row2280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2280 := by decide +kernel

theorem rowEval2280 (x : Key → ℝ) : Integer.Sparse.eval row2280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2280, Integer.Sparse.eval_collectBalanced, rawRowCheck2280]

theorem rawRowCheck2281 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6 = rawRow2281 := by decide +kernel

theorem rowCheck2281 : row2281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2281 := by decide +kernel

theorem rowEval2281 (x : Key → ℝ) : Integer.Sparse.eval row2281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2281, Integer.Sparse.eval_collectBalanced, rawRowCheck2281]

theorem rawRowCheck2282 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6 = rawRow2282 := by decide +kernel

theorem rowCheck2282 : row2282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2282 := by decide +kernel

theorem rowEval2282 (x : Key → ℝ) : Integer.Sparse.eval row2282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2282, Integer.Sparse.eval_collectBalanced, rawRowCheck2282]

theorem rawRowCheck2283 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6 = rawRow2283 := by decide +kernel

theorem rowCheck2283 : row2283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2283 := by decide +kernel

theorem rowEval2283 (x : Key → ℝ) : Integer.Sparse.eval row2283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2283, Integer.Sparse.eval_collectBalanced, rawRowCheck2283]

theorem rawRowCheck2284 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form6 = rawRow2284 := by decide +kernel

theorem rowCheck2284 : row2284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2284 := by decide +kernel

theorem rowEval2284 (x : Key → ℝ) : Integer.Sparse.eval row2284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2284, Integer.Sparse.eval_collectBalanced, rawRowCheck2284]

theorem rawRowCheck2285 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form6 = rawRow2285 := by decide +kernel

theorem rowCheck2285 : row2285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2285 := by decide +kernel

theorem rowEval2285 (x : Key → ℝ) : Integer.Sparse.eval row2285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2285, Integer.Sparse.eval_collectBalanced, rawRowCheck2285]

theorem rawRowCheck2286 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form6 = rawRow2286 := by decide +kernel

theorem rowCheck2286 : row2286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2286 := by decide +kernel

theorem rowEval2286 (x : Key → ℝ) : Integer.Sparse.eval row2286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2286, Integer.Sparse.eval_collectBalanced, rawRowCheck2286]

theorem rawRowCheck2287 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form6 = rawRow2287 := by decide +kernel

theorem rowCheck2287 : row2287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2287 := by decide +kernel

theorem rowEval2287 (x : Key → ℝ) : Integer.Sparse.eval row2287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2287, Integer.Sparse.eval_collectBalanced, rawRowCheck2287]

theorem rawRowCheck2288 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form6 = rawRow2288 := by decide +kernel

theorem rowCheck2288 : row2288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2288 := by decide +kernel

theorem rowEval2288 (x : Key → ℝ) : Integer.Sparse.eval row2288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2288, Integer.Sparse.eval_collectBalanced, rawRowCheck2288]

theorem rawRowCheck2289 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form6 = rawRow2289 := by decide +kernel

theorem rowCheck2289 : row2289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2289 := by decide +kernel

theorem rowEval2289 (x : Key → ℝ) : Integer.Sparse.eval row2289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2289, Integer.Sparse.eval_collectBalanced, rawRowCheck2289]

theorem rawRowCheck2290 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6 = rawRow2290 := by decide +kernel

theorem rowCheck2290 : row2290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2290 := by decide +kernel

theorem rowEval2290 (x : Key → ℝ) : Integer.Sparse.eval row2290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2290, Integer.Sparse.eval_collectBalanced, rawRowCheck2290]

theorem rawRowCheck2291 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6 = rawRow2291 := by decide +kernel

theorem rowCheck2291 : row2291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2291 := by decide +kernel

theorem rowEval2291 (x : Key → ℝ) : Integer.Sparse.eval row2291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2291, Integer.Sparse.eval_collectBalanced, rawRowCheck2291]

theorem rawRowCheck2292 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6 = rawRow2292 := by decide +kernel

theorem rowCheck2292 : row2292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2292 := by decide +kernel

theorem rowEval2292 (x : Key → ℝ) : Integer.Sparse.eval row2292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2292, Integer.Sparse.eval_collectBalanced, rawRowCheck2292]

theorem rawRowCheck2293 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6 = rawRow2293 := by decide +kernel

theorem rowCheck2293 : row2293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2293 := by decide +kernel

theorem rowEval2293 (x : Key → ℝ) : Integer.Sparse.eval row2293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2293, Integer.Sparse.eval_collectBalanced, rawRowCheck2293]

theorem rawRowCheck2294 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6 = rawRow2294 := by decide +kernel

theorem rowCheck2294 : row2294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2294 := by decide +kernel

theorem rowEval2294 (x : Key → ℝ) : Integer.Sparse.eval row2294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2294, Integer.Sparse.eval_collectBalanced, rawRowCheck2294]

theorem rawRowCheck2295 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6 = rawRow2295 := by decide +kernel

theorem rowCheck2295 : row2295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2295 := by decide +kernel

theorem rowEval2295 (x : Key → ℝ) : Integer.Sparse.eval row2295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2295, Integer.Sparse.eval_collectBalanced, rawRowCheck2295]

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

theorem entryCheck12_6 : entry12_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_6 k)) := by decide +kernel

theorem rowsSound12_6 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2266 x
  · exact rowEval2267 x
  · exact rowEval2268 x
  · exact rowEval2269 x
  · exact rowEval2270 x
  · exact rowEval2271 x
  · exact rowEval2272 x
  · exact rowEval2273 x
  · exact rowEval2274 x
  · exact rowEval2275 x
  · exact rowEval2276 x
  · exact rowEval2277 x
  · exact rowEval2278 x
  · exact rowEval2279 x
  · exact rowEval2280 x
  · exact rowEval2281 x
  · exact rowEval2282 x
  · exact rowEval2283 x
  · exact rowEval2284 x
  · exact rowEval2285 x
  · exact rowEval2286 x
  · exact rowEval2287 x
  · exact rowEval2288 x
  · exact rowEval2289 x
  · exact rowEval2290 x
  · exact rowEval2291 x
  · exact rowEval2292 x
  · exact rowEval2293 x
  · exact rowEval2294 x
  · exact rowEval2295 x

theorem entryEval12_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_6 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck12_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_6]

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

theorem rawRowCheck2560 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2560 := by decide +kernel

theorem rowCheck2560 : row2560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2560 := by decide +kernel

theorem rowEval2560 (x : Key → ℝ) : Integer.Sparse.eval row2560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2560, Integer.Sparse.eval_collectBalanced, rawRowCheck2560]

theorem rawRowCheck2561 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2561 := by decide +kernel

theorem rowCheck2561 : row2561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2561 := by decide +kernel

theorem rowEval2561 (x : Key → ℝ) : Integer.Sparse.eval row2561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2561, Integer.Sparse.eval_collectBalanced, rawRowCheck2561]

theorem rawRowCheck2562 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2562 := by decide +kernel

theorem rowCheck2562 : row2562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2562 := by decide +kernel

theorem rowEval2562 (x : Key → ℝ) : Integer.Sparse.eval row2562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2562, Integer.Sparse.eval_collectBalanced, rawRowCheck2562]

theorem rawRowCheck2563 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2563 := by decide +kernel

theorem rowCheck2563 : row2563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2563 := by decide +kernel

theorem rowEval2563 (x : Key → ℝ) : Integer.Sparse.eval row2563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2563, Integer.Sparse.eval_collectBalanced, rawRowCheck2563]

theorem rawRowCheck2564 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2564 := by decide +kernel

theorem rowCheck2564 : row2564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2564 := by decide +kernel

theorem rowEval2564 (x : Key → ℝ) : Integer.Sparse.eval row2564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2564, Integer.Sparse.eval_collectBalanced, rawRowCheck2564]

theorem rawRowCheck2565 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2565 := by decide +kernel

theorem rowCheck2565 : row2565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2565 := by decide +kernel

theorem rowEval2565 (x : Key → ℝ) : Integer.Sparse.eval row2565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2565, Integer.Sparse.eval_collectBalanced, rawRowCheck2565]

theorem rawRowCheck2566 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2566 := by decide +kernel

theorem rowCheck2566 : row2566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2566 := by decide +kernel

theorem rowEval2566 (x : Key → ℝ) : Integer.Sparse.eval row2566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2566, Integer.Sparse.eval_collectBalanced, rawRowCheck2566]

theorem rawRowCheck2567 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2567 := by decide +kernel

theorem rowCheck2567 : row2567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2567 := by decide +kernel

theorem rowEval2567 (x : Key → ℝ) : Integer.Sparse.eval row2567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2567, Integer.Sparse.eval_collectBalanced, rawRowCheck2567]

theorem rawRowCheck2568 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2568 := by decide +kernel

theorem rowCheck2568 : row2568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2568 := by decide +kernel

theorem rowEval2568 (x : Key → ℝ) : Integer.Sparse.eval row2568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2568, Integer.Sparse.eval_collectBalanced, rawRowCheck2568]

theorem rawRowCheck2569 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2569 := by decide +kernel

theorem rowCheck2569 : row2569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2569 := by decide +kernel

theorem rowEval2569 (x : Key → ℝ) : Integer.Sparse.eval row2569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2569, Integer.Sparse.eval_collectBalanced, rawRowCheck2569]

theorem rawRowCheck2570 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2570 := by decide +kernel

theorem rowCheck2570 : row2570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2570 := by decide +kernel

theorem rowEval2570 (x : Key → ℝ) : Integer.Sparse.eval row2570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2570, Integer.Sparse.eval_collectBalanced, rawRowCheck2570]

theorem rawRowCheck2571 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2571 := by decide +kernel

theorem rowCheck2571 : row2571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2571 := by decide +kernel

theorem rowEval2571 (x : Key → ℝ) : Integer.Sparse.eval row2571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2571, Integer.Sparse.eval_collectBalanced, rawRowCheck2571]

theorem rawRowCheck2572 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2572 := by decide +kernel

theorem rowCheck2572 : row2572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2572 := by decide +kernel

theorem rowEval2572 (x : Key → ℝ) : Integer.Sparse.eval row2572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2572, Integer.Sparse.eval_collectBalanced, rawRowCheck2572]

theorem rawRowCheck2573 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2573 := by decide +kernel

theorem rowCheck2573 : row2573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2573 := by decide +kernel

theorem rowEval2573 (x : Key → ℝ) : Integer.Sparse.eval row2573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2573, Integer.Sparse.eval_collectBalanced, rawRowCheck2573]

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

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2560 x
  · exact rowEval2561 x
  · exact rowEval2562 x
  · exact rowEval2563 x
  · exact rowEval2564 x
  · exact rowEval2565 x
  · exact rowEval2566 x
  · exact rowEval2567 x
  · exact rowEval2568 x
  · exact rowEval2569 x
  · exact rowEval2570 x
  · exact rowEval2571 x
  · exact rowEval2572 x
  · exact rowEval2573 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2816 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form6 = rawRow2816 := by decide +kernel

theorem rowCheck2816 : row2816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2816 := by decide +kernel

theorem rowEval2816 (x : Key → ℝ) : Integer.Sparse.eval row2816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2816, Integer.Sparse.eval_collectBalanced, rawRowCheck2816]

theorem rawRowCheck2817 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form6 = rawRow2817 := by decide +kernel

theorem rowCheck2817 : row2817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2817 := by decide +kernel

theorem rowEval2817 (x : Key → ℝ) : Integer.Sparse.eval row2817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2817, Integer.Sparse.eval_collectBalanced, rawRowCheck2817]

theorem rawRowCheck2818 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form6 = rawRow2818 := by decide +kernel

theorem rowCheck2818 : row2818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2818 := by decide +kernel

theorem rowEval2818 (x : Key → ℝ) : Integer.Sparse.eval row2818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2818, Integer.Sparse.eval_collectBalanced, rawRowCheck2818]

theorem rawRowCheck2819 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2819 := by decide +kernel

theorem rowCheck2819 : row2819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2819 := by decide +kernel

theorem rowEval2819 (x : Key → ℝ) : Integer.Sparse.eval row2819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2819, Integer.Sparse.eval_collectBalanced, rawRowCheck2819]

theorem rawRowCheck2820 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2820 := by decide +kernel

theorem rowCheck2820 : row2820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2820 := by decide +kernel

theorem rowEval2820 (x : Key → ℝ) : Integer.Sparse.eval row2820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2820, Integer.Sparse.eval_collectBalanced, rawRowCheck2820]

theorem rawRowCheck2821 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2821 := by decide +kernel

theorem rowCheck2821 : row2821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2821 := by decide +kernel

theorem rowEval2821 (x : Key → ℝ) : Integer.Sparse.eval row2821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2821, Integer.Sparse.eval_collectBalanced, rawRowCheck2821]

theorem rawRowCheck2822 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form6 = rawRow2822 := by decide +kernel

theorem rowCheck2822 : row2822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2822 := by decide +kernel

theorem rowEval2822 (x : Key → ℝ) : Integer.Sparse.eval row2822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2822, Integer.Sparse.eval_collectBalanced, rawRowCheck2822]

theorem rawRowCheck2823 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form6 = rawRow2823 := by decide +kernel

theorem rowCheck2823 : row2823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2823 := by decide +kernel

theorem rowEval2823 (x : Key → ℝ) : Integer.Sparse.eval row2823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2823, Integer.Sparse.eval_collectBalanced, rawRowCheck2823]

theorem rawRowCheck2824 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form6 = rawRow2824 := by decide +kernel

theorem rowCheck2824 : row2824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2824 := by decide +kernel

theorem rowEval2824 (x : Key → ℝ) : Integer.Sparse.eval row2824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2824, Integer.Sparse.eval_collectBalanced, rawRowCheck2824]

theorem rawRowCheck2825 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form6 = rawRow2825 := by decide +kernel

theorem rowCheck2825 : row2825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2825 := by decide +kernel

theorem rowEval2825 (x : Key → ℝ) : Integer.Sparse.eval row2825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2825, Integer.Sparse.eval_collectBalanced, rawRowCheck2825]

theorem rawRowCheck2826 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form6 = rawRow2826 := by decide +kernel

theorem rowCheck2826 : row2826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2826 := by decide +kernel

theorem rowEval2826 (x : Key → ℝ) : Integer.Sparse.eval row2826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2826, Integer.Sparse.eval_collectBalanced, rawRowCheck2826]

theorem rawRowCheck2827 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form6 = rawRow2827 := by decide +kernel

theorem rowCheck2827 : row2827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2827 := by decide +kernel

theorem rowEval2827 (x : Key → ℝ) : Integer.Sparse.eval row2827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2827, Integer.Sparse.eval_collectBalanced, rawRowCheck2827]

theorem rawRowCheck2828 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form6 = rawRow2828 := by decide +kernel

theorem rowCheck2828 : row2828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2828 := by decide +kernel

theorem rowEval2828 (x : Key → ℝ) : Integer.Sparse.eval row2828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2828, Integer.Sparse.eval_collectBalanced, rawRowCheck2828]

theorem rawRowCheck2829 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form6 = rawRow2829 := by decide +kernel

theorem rowCheck2829 : row2829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2829 := by decide +kernel

theorem rowEval2829 (x : Key → ℝ) : Integer.Sparse.eval row2829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2829, Integer.Sparse.eval_collectBalanced, rawRowCheck2829]

theorem rawRowCheck2830 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form6 = rawRow2830 := by decide +kernel

theorem rowCheck2830 : row2830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2830 := by decide +kernel

theorem rowEval2830 (x : Key → ℝ) : Integer.Sparse.eval row2830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2830, Integer.Sparse.eval_collectBalanced, rawRowCheck2830]

theorem rawRowCheck2831 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow2831 := by decide +kernel

theorem rowCheck2831 : row2831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2831 := by decide +kernel

theorem rowEval2831 (x : Key → ℝ) : Integer.Sparse.eval row2831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2831, Integer.Sparse.eval_collectBalanced, rawRowCheck2831]

theorem rawRowCheck2832 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow2832 := by decide +kernel

theorem rowCheck2832 : row2832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2832 := by decide +kernel

theorem rowEval2832 (x : Key → ℝ) : Integer.Sparse.eval row2832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2832, Integer.Sparse.eval_collectBalanced, rawRowCheck2832]

theorem rawRowCheck2833 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow2833 := by decide +kernel

theorem rowCheck2833 : row2833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2833 := by decide +kernel

theorem rowEval2833 (x : Key → ℝ) : Integer.Sparse.eval row2833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2833, Integer.Sparse.eval_collectBalanced, rawRowCheck2833]

theorem rawRowCheck2834 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form6 = rawRow2834 := by decide +kernel

theorem rowCheck2834 : row2834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2834 := by decide +kernel

theorem rowEval2834 (x : Key → ℝ) : Integer.Sparse.eval row2834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2834, Integer.Sparse.eval_collectBalanced, rawRowCheck2834]

theorem rawRowCheck2835 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form6 = rawRow2835 := by decide +kernel

theorem rowCheck2835 : row2835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2835 := by decide +kernel

theorem rowEval2835 (x : Key → ℝ) : Integer.Sparse.eval row2835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2835, Integer.Sparse.eval_collectBalanced, rawRowCheck2835]

theorem rawRowCheck2836 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form6 = rawRow2836 := by decide +kernel

theorem rowCheck2836 : row2836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2836 := by decide +kernel

theorem rowEval2836 (x : Key → ℝ) : Integer.Sparse.eval row2836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2836, Integer.Sparse.eval_collectBalanced, rawRowCheck2836]

theorem rawRowCheck2837 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form6 = rawRow2837 := by decide +kernel

theorem rowCheck2837 : row2837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2837 := by decide +kernel

theorem rowEval2837 (x : Key → ℝ) : Integer.Sparse.eval row2837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2837, Integer.Sparse.eval_collectBalanced, rawRowCheck2837]

theorem rawRowCheck2838 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form6 = rawRow2838 := by decide +kernel

theorem rowCheck2838 : row2838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2838 := by decide +kernel

theorem rowEval2838 (x : Key → ℝ) : Integer.Sparse.eval row2838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2838, Integer.Sparse.eval_collectBalanced, rawRowCheck2838]

theorem rawRowCheck2839 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form6 = rawRow2839 := by decide +kernel

theorem rowCheck2839 : row2839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2839 := by decide +kernel

theorem rowEval2839 (x : Key → ℝ) : Integer.Sparse.eval row2839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck2839, Integer.Sparse.eval_collectBalanced, rawRowCheck2839]

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

theorem entryCheck14_6 : entry14_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_6 k)) := by decide +kernel

theorem rowsSound14_6 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2816 x
  · exact rowEval2817 x
  · exact rowEval2818 x
  · exact rowEval2819 x
  · exact rowEval2820 x
  · exact rowEval2821 x
  · exact rowEval2822 x
  · exact rowEval2823 x
  · exact rowEval2824 x
  · exact rowEval2825 x
  · exact rowEval2826 x
  · exact rowEval2827 x
  · exact rowEval2828 x
  · exact rowEval2829 x
  · exact rowEval2830 x
  · exact rowEval2831 x
  · exact rowEval2832 x
  · exact rowEval2833 x
  · exact rowEval2834 x
  · exact rowEval2835 x
  · exact rowEval2836 x
  · exact rowEval2837 x
  · exact rowEval2838 x
  · exact rowEval2839 x

theorem entryEval14_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_6 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck14_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_6]

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

theorem rawRowCheck3548 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form6 = rawRow3548 := by decide +kernel

theorem rowCheck3548 : row3548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3548 := by decide +kernel

theorem rowEval3548 (x : Key → ℝ) : Integer.Sparse.eval row3548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3548, Integer.Sparse.eval_collectBalanced, rawRowCheck3548]

theorem rawRowCheck3549 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form6 = rawRow3549 := by decide +kernel

theorem rowCheck3549 : row3549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3549 := by decide +kernel

theorem rowEval3549 (x : Key → ℝ) : Integer.Sparse.eval row3549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3549, Integer.Sparse.eval_collectBalanced, rawRowCheck3549]

theorem rawRowCheck3550 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form6 = rawRow3550 := by decide +kernel

theorem rowCheck3550 : row3550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3550 := by decide +kernel

theorem rowEval3550 (x : Key → ℝ) : Integer.Sparse.eval row3550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3550, Integer.Sparse.eval_collectBalanced, rawRowCheck3550]

theorem rawRowCheck3551 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3551 := by decide +kernel

theorem rowCheck3551 : row3551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3551 := by decide +kernel

theorem rowEval3551 (x : Key → ℝ) : Integer.Sparse.eval row3551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3551, Integer.Sparse.eval_collectBalanced, rawRowCheck3551]

theorem rawRowCheck3552 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3552 := by decide +kernel

theorem rowCheck3552 : row3552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3552 := by decide +kernel

theorem rowEval3552 (x : Key → ℝ) : Integer.Sparse.eval row3552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3552, Integer.Sparse.eval_collectBalanced, rawRowCheck3552]

theorem rawRowCheck3553 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3553 := by decide +kernel

theorem rowCheck3553 : row3553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3553 := by decide +kernel

theorem rowEval3553 (x : Key → ℝ) : Integer.Sparse.eval row3553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3553, Integer.Sparse.eval_collectBalanced, rawRowCheck3553]

theorem rawRowCheck3554 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form6 = rawRow3554 := by decide +kernel

theorem rowCheck3554 : row3554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3554 := by decide +kernel

theorem rowEval3554 (x : Key → ℝ) : Integer.Sparse.eval row3554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3554, Integer.Sparse.eval_collectBalanced, rawRowCheck3554]

theorem rawRowCheck3555 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form6 = rawRow3555 := by decide +kernel

theorem rowCheck3555 : row3555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3555 := by decide +kernel

theorem rowEval3555 (x : Key → ℝ) : Integer.Sparse.eval row3555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3555, Integer.Sparse.eval_collectBalanced, rawRowCheck3555]

theorem rawRowCheck3556 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form6 = rawRow3556 := by decide +kernel

theorem rowCheck3556 : row3556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3556 := by decide +kernel

theorem rowEval3556 (x : Key → ℝ) : Integer.Sparse.eval row3556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3556, Integer.Sparse.eval_collectBalanced, rawRowCheck3556]

theorem rawRowCheck3557 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow3557 := by decide +kernel

theorem rowCheck3557 : row3557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3557 := by decide +kernel

theorem rowEval3557 (x : Key → ℝ) : Integer.Sparse.eval row3557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3557, Integer.Sparse.eval_collectBalanced, rawRowCheck3557]

theorem rawRowCheck3558 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow3558 := by decide +kernel

theorem rowCheck3558 : row3558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3558 := by decide +kernel

theorem rowEval3558 (x : Key → ℝ) : Integer.Sparse.eval row3558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3558, Integer.Sparse.eval_collectBalanced, rawRowCheck3558]

theorem rawRowCheck3559 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow3559 := by decide +kernel

theorem rowCheck3559 : row3559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3559 := by decide +kernel

theorem rowEval3559 (x : Key → ℝ) : Integer.Sparse.eval row3559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3559, Integer.Sparse.eval_collectBalanced, rawRowCheck3559]

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

theorem entryCheck16_6 : entry16_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_6 k)) := by decide +kernel

theorem rowsSound16_6 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2266 x
  · exact rowEval2267 x
  · exact rowEval2268 x
  · exact rowEval3548 x
  · exact rowEval3549 x
  · exact rowEval3550 x
  · exact rowEval2275 x
  · exact rowEval2276 x
  · exact rowEval2277 x
  · exact rowEval3551 x
  · exact rowEval3552 x
  · exact rowEval3553 x
  · exact rowEval3554 x
  · exact rowEval3555 x
  · exact rowEval3556 x
  · exact rowEval3557 x
  · exact rowEval3558 x
  · exact rowEval3559 x

theorem entryEval16_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_6 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck16_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_6]

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

theorem rawRowCheck4640 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4640 := by decide +kernel

theorem rowCheck4640 : row4640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4640 := by decide +kernel

theorem rowEval4640 (x : Key → ℝ) : Integer.Sparse.eval row4640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4640, Integer.Sparse.eval_collectBalanced, rawRowCheck4640]

theorem rawRowCheck4641 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4641 := by decide +kernel

theorem rowCheck4641 : row4641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4641 := by decide +kernel

theorem rowEval4641 (x : Key → ℝ) : Integer.Sparse.eval row4641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4641, Integer.Sparse.eval_collectBalanced, rawRowCheck4641]

theorem rawRowCheck4642 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4642 := by decide +kernel

theorem rowCheck4642 : row4642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4642 := by decide +kernel

theorem rowEval4642 (x : Key → ℝ) : Integer.Sparse.eval row4642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4642, Integer.Sparse.eval_collectBalanced, rawRowCheck4642]

theorem rawRowCheck4643 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4643 := by decide +kernel

theorem rowCheck4643 : row4643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4643 := by decide +kernel

theorem rowEval4643 (x : Key → ℝ) : Integer.Sparse.eval row4643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4643, Integer.Sparse.eval_collectBalanced, rawRowCheck4643]

theorem rawRowCheck4644 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4644 := by decide +kernel

theorem rowCheck4644 : row4644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4644 := by decide +kernel

theorem rowEval4644 (x : Key → ℝ) : Integer.Sparse.eval row4644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4644, Integer.Sparse.eval_collectBalanced, rawRowCheck4644]

theorem rawRowCheck4645 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4645 := by decide +kernel

theorem rowCheck4645 : row4645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4645 := by decide +kernel

theorem rowEval4645 (x : Key → ℝ) : Integer.Sparse.eval row4645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4645, Integer.Sparse.eval_collectBalanced, rawRowCheck4645]

theorem rawRowCheck4646 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4646 := by decide +kernel

theorem rowCheck4646 : row4646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4646 := by decide +kernel

theorem rowEval4646 (x : Key → ℝ) : Integer.Sparse.eval row4646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4646, Integer.Sparse.eval_collectBalanced, rawRowCheck4646]

theorem rawRowCheck4647 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4647 := by decide +kernel

theorem rowCheck4647 : row4647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4647 := by decide +kernel

theorem rowEval4647 (x : Key → ℝ) : Integer.Sparse.eval row4647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4647, Integer.Sparse.eval_collectBalanced, rawRowCheck4647]

theorem rawRowCheck4648 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4648 := by decide +kernel

theorem rowCheck4648 : row4648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4648 := by decide +kernel

theorem rowEval4648 (x : Key → ℝ) : Integer.Sparse.eval row4648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4648, Integer.Sparse.eval_collectBalanced, rawRowCheck4648]

theorem rawRowCheck4649 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4649 := by decide +kernel

theorem rowCheck4649 : row4649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4649 := by decide +kernel

theorem rowEval4649 (x : Key → ℝ) : Integer.Sparse.eval row4649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4649, Integer.Sparse.eval_collectBalanced, rawRowCheck4649]

theorem rawRowCheck4650 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4650 := by decide +kernel

theorem rowCheck4650 : row4650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4650 := by decide +kernel

theorem rowEval4650 (x : Key → ℝ) : Integer.Sparse.eval row4650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4650, Integer.Sparse.eval_collectBalanced, rawRowCheck4650]

theorem rawRowCheck4651 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4651 := by decide +kernel

theorem rowCheck4651 : row4651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4651 := by decide +kernel

theorem rowEval4651 (x : Key → ℝ) : Integer.Sparse.eval row4651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4651, Integer.Sparse.eval_collectBalanced, rawRowCheck4651]

theorem rawRowCheck4652 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4652 := by decide +kernel

theorem rowCheck4652 : row4652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4652 := by decide +kernel

theorem rowEval4652 (x : Key → ℝ) : Integer.Sparse.eval row4652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4652, Integer.Sparse.eval_collectBalanced, rawRowCheck4652]

theorem rawRowCheck4653 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4653 := by decide +kernel

theorem rowCheck4653 : row4653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4653 := by decide +kernel

theorem rowEval4653 (x : Key → ℝ) : Integer.Sparse.eval row4653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4653, Integer.Sparse.eval_collectBalanced, rawRowCheck4653]

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

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4640 x
  · exact rowEval4641 x
  · exact rowEval4642 x
  · exact rowEval4643 x
  · exact rowEval4644 x
  · exact rowEval4645 x
  · exact rowEval4646 x
  · exact rowEval4647 x
  · exact rowEval4648 x
  · exact rowEval4649 x
  · exact rowEval4650 x
  · exact rowEval4651 x
  · exact rowEval4652 x
  · exact rowEval4653 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

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

theorem rawRowCheck1434 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow1434 := by decide +kernel

theorem rowCheck1434 : row1434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1434 := by decide +kernel

theorem rowEval1434 (x : Key → ℝ) : Integer.Sparse.eval row1434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1434, Integer.Sparse.eval_collectBalanced, rawRowCheck1434]

theorem rawRowCheck1435 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow1435 := by decide +kernel

theorem rowCheck1435 : row1435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1435 := by decide +kernel

theorem rowEval1435 (x : Key → ℝ) : Integer.Sparse.eval row1435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1435, Integer.Sparse.eval_collectBalanced, rawRowCheck1435]

theorem rawRowCheck1436 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow1436 := by decide +kernel

theorem rowCheck1436 : row1436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1436 := by decide +kernel

theorem rowEval1436 (x : Key → ℝ) : Integer.Sparse.eval row1436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1436, Integer.Sparse.eval_collectBalanced, rawRowCheck1436]

theorem rawRowCheck1437 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1437 := by decide +kernel

theorem rowCheck1437 : row1437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1437 := by decide +kernel

theorem rowEval1437 (x : Key → ℝ) : Integer.Sparse.eval row1437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1437, Integer.Sparse.eval_collectBalanced, rawRowCheck1437]

theorem rawRowCheck1438 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6 = rawRow1438 := by decide +kernel

theorem rowCheck1438 : row1438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1438 := by decide +kernel

theorem rowEval1438 (x : Key → ℝ) : Integer.Sparse.eval row1438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1438, Integer.Sparse.eval_collectBalanced, rawRowCheck1438]

theorem rawRowCheck1439 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6 = rawRow1439 := by decide +kernel

theorem rowCheck1439 : row1439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1439 := by decide +kernel

theorem rowEval1439 (x : Key → ℝ) : Integer.Sparse.eval row1439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1439, Integer.Sparse.eval_collectBalanced, rawRowCheck1439]

theorem rawRowCheck1440 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6 = rawRow1440 := by decide +kernel

theorem rowCheck1440 : row1440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1440 := by decide +kernel

theorem rowEval1440 (x : Key → ℝ) : Integer.Sparse.eval row1440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1440, Integer.Sparse.eval_collectBalanced, rawRowCheck1440]

theorem rawRowCheck1441 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1441 := by decide +kernel

theorem rowCheck1441 : row1441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1441 := by decide +kernel

theorem rowEval1441 (x : Key → ℝ) : Integer.Sparse.eval row1441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1441, Integer.Sparse.eval_collectBalanced, rawRowCheck1441]

theorem rawRowCheck1442 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1442 := by decide +kernel

theorem rowCheck1442 : row1442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1442 := by decide +kernel

theorem rowEval1442 (x : Key → ℝ) : Integer.Sparse.eval row1442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1442, Integer.Sparse.eval_collectBalanced, rawRowCheck1442]

theorem rawRowCheck1443 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1443 := by decide +kernel

theorem rowCheck1443 : row1443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1443 := by decide +kernel

theorem rowEval1443 (x : Key → ℝ) : Integer.Sparse.eval row1443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1443, Integer.Sparse.eval_collectBalanced, rawRowCheck1443]

theorem rawRowCheck1444 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6 = rawRow1444 := by decide +kernel

theorem rowCheck1444 : row1444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1444 := by decide +kernel

theorem rowEval1444 (x : Key → ℝ) : Integer.Sparse.eval row1444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1444, Integer.Sparse.eval_collectBalanced, rawRowCheck1444]

theorem rawRowCheck1445 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6 = rawRow1445 := by decide +kernel

theorem rowCheck1445 : row1445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1445 := by decide +kernel

theorem rowEval1445 (x : Key → ℝ) : Integer.Sparse.eval row1445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1445, Integer.Sparse.eval_collectBalanced, rawRowCheck1445]

theorem rawRowCheck1446 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6 = rawRow1446 := by decide +kernel

theorem rowCheck1446 : row1446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1446 := by decide +kernel

theorem rowEval1446 (x : Key → ℝ) : Integer.Sparse.eval row1446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1446, Integer.Sparse.eval_collectBalanced, rawRowCheck1446]

theorem rawRowCheck1447 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6 = rawRow1447 := by decide +kernel

theorem rowCheck1447 : row1447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1447 := by decide +kernel

theorem rowEval1447 (x : Key → ℝ) : Integer.Sparse.eval row1447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form6) x := by
  rw [rowCheck1447, Integer.Sparse.eval_collectBalanced, rawRowCheck1447]

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

theorem rawRowCheck1644 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1644 := by decide +kernel

theorem rowCheck1644 : row1644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1644 := by decide +kernel

theorem rowEval1644 (x : Key → ℝ) : Integer.Sparse.eval row1644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1644, Integer.Sparse.eval_collectBalanced, rawRowCheck1644]

theorem rawRowCheck1645 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1645 := by decide +kernel

theorem rowCheck1645 : row1645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1645 := by decide +kernel

theorem rowEval1645 (x : Key → ℝ) : Integer.Sparse.eval row1645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1645, Integer.Sparse.eval_collectBalanced, rawRowCheck1645]

theorem rawRowCheck1646 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1646 := by decide +kernel

theorem rowCheck1646 : row1646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1646 := by decide +kernel

theorem rowEval1646 (x : Key → ℝ) : Integer.Sparse.eval row1646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1646, Integer.Sparse.eval_collectBalanced, rawRowCheck1646]

theorem rawRowCheck1653 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1653 := by decide +kernel

theorem rowCheck1653 : row1653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1653 := by decide +kernel

theorem rowEval1653 (x : Key → ℝ) : Integer.Sparse.eval row1653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1653, Integer.Sparse.eval_collectBalanced, rawRowCheck1653]

theorem rawRowCheck1654 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1654 := by decide +kernel

theorem rowCheck1654 : row1654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1654 := by decide +kernel

theorem rowEval1654 (x : Key → ℝ) : Integer.Sparse.eval row1654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1654, Integer.Sparse.eval_collectBalanced, rawRowCheck1654]

theorem rawRowCheck1655 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1655 := by decide +kernel

theorem rowCheck1655 : row1655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1655 := by decide +kernel

theorem rowEval1655 (x : Key → ℝ) : Integer.Sparse.eval row1655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1655, Integer.Sparse.eval_collectBalanced, rawRowCheck1655]

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

theorem rawRowCheck4902 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4902 := by decide +kernel

theorem rowCheck4902 : row4902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4902 := by decide +kernel

theorem rowEval4902 (x : Key → ℝ) : Integer.Sparse.eval row4902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4902, Integer.Sparse.eval_collectBalanced, rawRowCheck4902]

theorem rawRowCheck4903 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4903 := by decide +kernel

theorem rowCheck4903 : row4903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4903 := by decide +kernel

theorem rowEval4903 (x : Key → ℝ) : Integer.Sparse.eval row4903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4903, Integer.Sparse.eval_collectBalanced, rawRowCheck4903]

theorem rawRowCheck4904 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4904 := by decide +kernel

theorem rowCheck4904 : row4904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4904 := by decide +kernel

theorem rowEval4904 (x : Key → ℝ) : Integer.Sparse.eval row4904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4904, Integer.Sparse.eval_collectBalanced, rawRowCheck4904]

theorem rawRowCheck4905 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6 = rawRow4905 := by decide +kernel

theorem rowCheck4905 : row4905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4905 := by decide +kernel

theorem rowEval4905 (x : Key → ℝ) : Integer.Sparse.eval row4905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4905, Integer.Sparse.eval_collectBalanced, rawRowCheck4905]

theorem rawRowCheck4906 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6 = rawRow4906 := by decide +kernel

theorem rowCheck4906 : row4906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4906 := by decide +kernel

theorem rowEval4906 (x : Key → ℝ) : Integer.Sparse.eval row4906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4906, Integer.Sparse.eval_collectBalanced, rawRowCheck4906]

theorem rawRowCheck4907 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6 = rawRow4907 := by decide +kernel

theorem rowCheck4907 : row4907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4907 := by decide +kernel

theorem rowEval4907 (x : Key → ℝ) : Integer.Sparse.eval row4907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4907, Integer.Sparse.eval_collectBalanced, rawRowCheck4907]

theorem rawRowCheck4908 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4908 := by decide +kernel

theorem rowCheck4908 : row4908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4908 := by decide +kernel

theorem rowEval4908 (x : Key → ℝ) : Integer.Sparse.eval row4908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4908, Integer.Sparse.eval_collectBalanced, rawRowCheck4908]

theorem rawRowCheck4909 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4909 := by decide +kernel

theorem rowCheck4909 : row4909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4909 := by decide +kernel

theorem rowEval4909 (x : Key → ℝ) : Integer.Sparse.eval row4909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4909, Integer.Sparse.eval_collectBalanced, rawRowCheck4909]

theorem rawRowCheck4910 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4910 := by decide +kernel

theorem rowCheck4910 : row4910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4910 := by decide +kernel

theorem rowEval4910 (x : Key → ℝ) : Integer.Sparse.eval row4910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4910, Integer.Sparse.eval_collectBalanced, rawRowCheck4910]

theorem rawRowCheck4911 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6 = rawRow4911 := by decide +kernel

theorem rowCheck4911 : row4911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4911 := by decide +kernel

theorem rowEval4911 (x : Key → ℝ) : Integer.Sparse.eval row4911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4911, Integer.Sparse.eval_collectBalanced, rawRowCheck4911]

theorem rawRowCheck4912 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6 = rawRow4912 := by decide +kernel

theorem rowCheck4912 : row4912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4912 := by decide +kernel

theorem rowEval4912 (x : Key → ℝ) : Integer.Sparse.eval row4912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4912, Integer.Sparse.eval_collectBalanced, rawRowCheck4912]

theorem rawRowCheck4913 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6 = rawRow4913 := by decide +kernel

theorem rowCheck4913 : row4913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4913 := by decide +kernel

theorem rowEval4913 (x : Key → ℝ) : Integer.Sparse.eval row4913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4913, Integer.Sparse.eval_collectBalanced, rawRowCheck4913]

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

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4902 x
  · exact rowEval4903 x
  · exact rowEval4904 x
  · exact rowEval1644 x
  · exact rowEval1645 x
  · exact rowEval1646 x
  · exact rowEval4905 x
  · exact rowEval4906 x
  · exact rowEval4907 x
  · exact rowEval4908 x
  · exact rowEval4909 x
  · exact rowEval4910 x
  · exact rowEval1653 x
  · exact rowEval1654 x
  · exact rowEval1655 x
  · exact rowEval4911 x
  · exact rowEval4912 x
  · exact rowEval4913 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1084 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1084 := by decide +kernel

theorem rowCheck1084 : row1084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1084 := by decide +kernel

theorem rowEval1084 (x : Key → ℝ) : Integer.Sparse.eval row1084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1084, Integer.Sparse.eval_collectBalanced, rawRowCheck1084]

theorem rawRowCheck1085 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1085 := by decide +kernel

theorem rowCheck1085 : row1085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1085 := by decide +kernel

theorem rowEval1085 (x : Key → ℝ) : Integer.Sparse.eval row1085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1085, Integer.Sparse.eval_collectBalanced, rawRowCheck1085]

theorem rawRowCheck1086 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1086 := by decide +kernel

theorem rowCheck1086 : row1086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1086 := by decide +kernel

theorem rowEval1086 (x : Key → ℝ) : Integer.Sparse.eval row1086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1086, Integer.Sparse.eval_collectBalanced, rawRowCheck1086]

theorem rawRowCheck1087 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1087 := by decide +kernel

theorem rowCheck1087 : row1087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1087 := by decide +kernel

theorem rowEval1087 (x : Key → ℝ) : Integer.Sparse.eval row1087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1087, Integer.Sparse.eval_collectBalanced, rawRowCheck1087]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1088 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1088 := by decide +kernel

theorem rowCheck1088 : row1088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1088 := by decide +kernel

theorem rowEval1088 (x : Key → ℝ) : Integer.Sparse.eval row1088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1088, Integer.Sparse.eval_collectBalanced, rawRowCheck1088]

theorem rawRowCheck1089 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1089 := by decide +kernel

theorem rowCheck1089 : row1089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1089 := by decide +kernel

theorem rowEval1089 (x : Key → ℝ) : Integer.Sparse.eval row1089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1089, Integer.Sparse.eval_collectBalanced, rawRowCheck1089]

theorem rawRowCheck1090 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1090 := by decide +kernel

theorem rowCheck1090 : row1090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1090 := by decide +kernel

theorem rowEval1090 (x : Key → ℝ) : Integer.Sparse.eval row1090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1090, Integer.Sparse.eval_collectBalanced, rawRowCheck1090]

theorem rawRowCheck1091 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1091 := by decide +kernel

theorem rowCheck1091 : row1091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1091 := by decide +kernel

theorem rowEval1091 (x : Key → ℝ) : Integer.Sparse.eval row1091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1091, Integer.Sparse.eval_collectBalanced, rawRowCheck1091]

theorem rawRowCheck1092 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1092 := by decide +kernel

theorem rowCheck1092 : row1092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1092 := by decide +kernel

theorem rowEval1092 (x : Key → ℝ) : Integer.Sparse.eval row1092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1092, Integer.Sparse.eval_collectBalanced, rawRowCheck1092]

theorem rawRowCheck1093 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1093 := by decide +kernel

theorem rowCheck1093 : row1093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1093 := by decide +kernel

theorem rowEval1093 (x : Key → ℝ) : Integer.Sparse.eval row1093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1093, Integer.Sparse.eval_collectBalanced, rawRowCheck1093]

theorem rawRowCheck1094 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1094 := by decide +kernel

theorem rowCheck1094 : row1094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1094 := by decide +kernel

theorem rowEval1094 (x : Key → ℝ) : Integer.Sparse.eval row1094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1094, Integer.Sparse.eval_collectBalanced, rawRowCheck1094]

theorem rawRowCheck1095 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1095 := by decide +kernel

theorem rowCheck1095 : row1095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1095 := by decide +kernel

theorem rowEval1095 (x : Key → ℝ) : Integer.Sparse.eval row1095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1095, Integer.Sparse.eval_collectBalanced, rawRowCheck1095]

theorem rawRowCheck1096 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1096 := by decide +kernel

theorem rowCheck1096 : row1096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1096 := by decide +kernel

theorem rowEval1096 (x : Key → ℝ) : Integer.Sparse.eval row1096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1096, Integer.Sparse.eval_collectBalanced, rawRowCheck1096]

theorem rawRowCheck1097 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1097 := by decide +kernel

theorem rowCheck1097 : row1097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1097 := by decide +kernel

theorem rowEval1097 (x : Key → ℝ) : Integer.Sparse.eval row1097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1097, Integer.Sparse.eval_collectBalanced, rawRowCheck1097]

theorem rawRowCheck1098 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form1 = rawRow1098 := by decide +kernel

theorem rowCheck1098 : row1098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1098 := by decide +kernel

theorem rowEval1098 (x : Key → ℝ) : Integer.Sparse.eval row1098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1098, Integer.Sparse.eval_collectBalanced, rawRowCheck1098]

theorem rawRowCheck1099 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form1 = rawRow1099 := by decide +kernel

theorem rowCheck1099 : row1099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1099 := by decide +kernel

theorem rowEval1099 (x : Key → ℝ) : Integer.Sparse.eval row1099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1099, Integer.Sparse.eval_collectBalanced, rawRowCheck1099]

theorem rawRowCheck1100 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form1 = rawRow1100 := by decide +kernel

theorem rowCheck1100 : row1100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1100 := by decide +kernel

theorem rowEval1100 (x : Key → ℝ) : Integer.Sparse.eval row1100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1100, Integer.Sparse.eval_collectBalanced, rawRowCheck1100]

theorem rawRowCheck1101 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form1 = rawRow1101 := by decide +kernel

theorem rowCheck1101 : row1101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1101 := by decide +kernel

theorem rowEval1101 (x : Key → ℝ) : Integer.Sparse.eval row1101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1101, Integer.Sparse.eval_collectBalanced, rawRowCheck1101]

theorem rawRowCheck1102 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form1 = rawRow1102 := by decide +kernel

theorem rowCheck1102 : row1102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1102 := by decide +kernel

theorem rowEval1102 (x : Key → ℝ) : Integer.Sparse.eval row1102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1102, Integer.Sparse.eval_collectBalanced, rawRowCheck1102]

theorem rawRowCheck1103 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form1 = rawRow1103 := by decide +kernel

theorem rowCheck1103 : row1103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1103 := by decide +kernel

theorem rowEval1103 (x : Key → ℝ) : Integer.Sparse.eval row1103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1103, Integer.Sparse.eval_collectBalanced, rawRowCheck1103]

theorem rawRowCheck1104 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form1 = rawRow1104 := by decide +kernel

theorem rowCheck1104 : row1104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1104 := by decide +kernel

theorem rowEval1104 (x : Key → ℝ) : Integer.Sparse.eval row1104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1104, Integer.Sparse.eval_collectBalanced, rawRowCheck1104]

theorem rawRowCheck1105 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form1 = rawRow1105 := by decide +kernel

theorem rowCheck1105 : row1105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1105 := by decide +kernel

theorem rowEval1105 (x : Key → ℝ) : Integer.Sparse.eval row1105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1105, Integer.Sparse.eval_collectBalanced, rawRowCheck1105]

theorem rawRowCheck1106 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form1 = rawRow1106 := by decide +kernel

theorem rowCheck1106 : row1106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1106 := by decide +kernel

theorem rowEval1106 (x : Key → ℝ) : Integer.Sparse.eval row1106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1106, Integer.Sparse.eval_collectBalanced, rawRowCheck1106]

theorem rawRowCheck1107 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form1 = rawRow1107 := by decide +kernel

theorem rowCheck1107 : row1107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1107 := by decide +kernel

theorem rowEval1107 (x : Key → ℝ) : Integer.Sparse.eval row1107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1107, Integer.Sparse.eval_collectBalanced, rawRowCheck1107]

theorem rawRowCheck1108 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form1 = rawRow1108 := by decide +kernel

theorem rowCheck1108 : row1108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1108 := by decide +kernel

theorem rowEval1108 (x : Key → ℝ) : Integer.Sparse.eval row1108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1108, Integer.Sparse.eval_collectBalanced, rawRowCheck1108]

theorem rawRowCheck1109 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form1 = rawRow1109 := by decide +kernel

theorem rowCheck1109 : row1109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1109 := by decide +kernel

theorem rowEval1109 (x : Key → ℝ) : Integer.Sparse.eval row1109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1109, Integer.Sparse.eval_collectBalanced, rawRowCheck1109]

theorem rawRowCheck1110 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form1 = rawRow1110 := by decide +kernel

theorem rowCheck1110 : row1110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1110 := by decide +kernel

theorem rowEval1110 (x : Key → ℝ) : Integer.Sparse.eval row1110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1110, Integer.Sparse.eval_collectBalanced, rawRowCheck1110]

theorem rawRowCheck1111 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form1 = rawRow1111 := by decide +kernel

theorem rowCheck1111 : row1111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1111 := by decide +kernel

theorem rowEval1111 (x : Key → ℝ) : Integer.Sparse.eval row1111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1111, Integer.Sparse.eval_collectBalanced, rawRowCheck1111]

theorem rawRowCheck1112 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form2 = rawRow1112 := by decide +kernel

theorem rowCheck1112 : row1112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1112 := by decide +kernel

theorem rowEval1112 (x : Key → ℝ) : Integer.Sparse.eval row1112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1112, Integer.Sparse.eval_collectBalanced, rawRowCheck1112]

theorem rawRowCheck1113 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form2 = rawRow1113 := by decide +kernel

theorem rowCheck1113 : row1113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1113 := by decide +kernel

theorem rowEval1113 (x : Key → ℝ) : Integer.Sparse.eval row1113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1113, Integer.Sparse.eval_collectBalanced, rawRowCheck1113]

theorem rawRowCheck1114 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form2 = rawRow1114 := by decide +kernel

theorem rowCheck1114 : row1114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1114 := by decide +kernel

theorem rowEval1114 (x : Key → ℝ) : Integer.Sparse.eval row1114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1114, Integer.Sparse.eval_collectBalanced, rawRowCheck1114]

theorem rawRowCheck1115 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form2 = rawRow1115 := by decide +kernel

theorem rowCheck1115 : row1115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1115 := by decide +kernel

theorem rowEval1115 (x : Key → ℝ) : Integer.Sparse.eval row1115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1115, Integer.Sparse.eval_collectBalanced, rawRowCheck1115]

theorem rawRowCheck1116 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form2 = rawRow1116 := by decide +kernel

theorem rowCheck1116 : row1116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1116 := by decide +kernel

theorem rowEval1116 (x : Key → ℝ) : Integer.Sparse.eval row1116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1116, Integer.Sparse.eval_collectBalanced, rawRowCheck1116]

theorem rawRowCheck1117 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form2 = rawRow1117 := by decide +kernel

theorem rowCheck1117 : row1117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1117 := by decide +kernel

theorem rowEval1117 (x : Key → ℝ) : Integer.Sparse.eval row1117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1117, Integer.Sparse.eval_collectBalanced, rawRowCheck1117]

theorem rawRowCheck1118 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form2 = rawRow1118 := by decide +kernel

theorem rowCheck1118 : row1118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1118 := by decide +kernel

theorem rowEval1118 (x : Key → ℝ) : Integer.Sparse.eval row1118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1118, Integer.Sparse.eval_collectBalanced, rawRowCheck1118]

theorem rawRowCheck1119 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form2 = rawRow1119 := by decide +kernel

theorem rowCheck1119 : row1119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1119 := by decide +kernel

theorem rowEval1119 (x : Key → ℝ) : Integer.Sparse.eval row1119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1119, Integer.Sparse.eval_collectBalanced, rawRowCheck1119]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck1120 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form2 = rawRow1120 := by decide +kernel

theorem rowCheck1120 : row1120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1120 := by decide +kernel

theorem rowEval1120 (x : Key → ℝ) : Integer.Sparse.eval row1120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1120, Integer.Sparse.eval_collectBalanced, rawRowCheck1120]

theorem rawRowCheck1121 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form2 = rawRow1121 := by decide +kernel

theorem rowCheck1121 : row1121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1121 := by decide +kernel

theorem rowEval1121 (x : Key → ℝ) : Integer.Sparse.eval row1121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1121, Integer.Sparse.eval_collectBalanced, rawRowCheck1121]

theorem rawRowCheck1122 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form2 = rawRow1122 := by decide +kernel

theorem rowCheck1122 : row1122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1122 := by decide +kernel

theorem rowEval1122 (x : Key → ℝ) : Integer.Sparse.eval row1122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1122, Integer.Sparse.eval_collectBalanced, rawRowCheck1122]

theorem rawRowCheck1123 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form2 = rawRow1123 := by decide +kernel

theorem rowCheck1123 : row1123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1123 := by decide +kernel

theorem rowEval1123 (x : Key → ℝ) : Integer.Sparse.eval row1123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1123, Integer.Sparse.eval_collectBalanced, rawRowCheck1123]

theorem rawRowCheck1124 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form2 = rawRow1124 := by decide +kernel

theorem rowCheck1124 : row1124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1124 := by decide +kernel

theorem rowEval1124 (x : Key → ℝ) : Integer.Sparse.eval row1124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1124, Integer.Sparse.eval_collectBalanced, rawRowCheck1124]

theorem rawRowCheck1125 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form2 = rawRow1125 := by decide +kernel

theorem rowCheck1125 : row1125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1125 := by decide +kernel

theorem rowEval1125 (x : Key → ℝ) : Integer.Sparse.eval row1125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1125, Integer.Sparse.eval_collectBalanced, rawRowCheck1125]

theorem rawRowCheck1126 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form3 = rawRow1126 := by decide +kernel

theorem rowCheck1126 : row1126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1126 := by decide +kernel

theorem rowEval1126 (x : Key → ℝ) : Integer.Sparse.eval row1126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1126, Integer.Sparse.eval_collectBalanced, rawRowCheck1126]

theorem rawRowCheck1127 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form3 = rawRow1127 := by decide +kernel

theorem rowCheck1127 : row1127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1127 := by decide +kernel

theorem rowEval1127 (x : Key → ℝ) : Integer.Sparse.eval row1127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1127, Integer.Sparse.eval_collectBalanced, rawRowCheck1127]

theorem rawRowCheck1128 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form3 = rawRow1128 := by decide +kernel

theorem rowCheck1128 : row1128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1128 := by decide +kernel

theorem rowEval1128 (x : Key → ℝ) : Integer.Sparse.eval row1128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1128, Integer.Sparse.eval_collectBalanced, rawRowCheck1128]

theorem rawRowCheck1129 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form3 = rawRow1129 := by decide +kernel

theorem rowCheck1129 : row1129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1129 := by decide +kernel

theorem rowEval1129 (x : Key → ℝ) : Integer.Sparse.eval row1129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1129, Integer.Sparse.eval_collectBalanced, rawRowCheck1129]

theorem rawRowCheck1130 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form3 = rawRow1130 := by decide +kernel

theorem rowCheck1130 : row1130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1130 := by decide +kernel

theorem rowEval1130 (x : Key → ℝ) : Integer.Sparse.eval row1130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1130, Integer.Sparse.eval_collectBalanced, rawRowCheck1130]

theorem rawRowCheck1131 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form3 = rawRow1131 := by decide +kernel

theorem rowCheck1131 : row1131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1131 := by decide +kernel

theorem rowEval1131 (x : Key → ℝ) : Integer.Sparse.eval row1131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1131, Integer.Sparse.eval_collectBalanced, rawRowCheck1131]

theorem rawRowCheck1132 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form3 = rawRow1132 := by decide +kernel

theorem rowCheck1132 : row1132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1132 := by decide +kernel

theorem rowEval1132 (x : Key → ℝ) : Integer.Sparse.eval row1132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1132, Integer.Sparse.eval_collectBalanced, rawRowCheck1132]

theorem rawRowCheck1133 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form3 = rawRow1133 := by decide +kernel

theorem rowCheck1133 : row1133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1133 := by decide +kernel

theorem rowEval1133 (x : Key → ℝ) : Integer.Sparse.eval row1133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1133, Integer.Sparse.eval_collectBalanced, rawRowCheck1133]

theorem rawRowCheck1134 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form3 = rawRow1134 := by decide +kernel

theorem rowCheck1134 : row1134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1134 := by decide +kernel

theorem rowEval1134 (x : Key → ℝ) : Integer.Sparse.eval row1134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1134, Integer.Sparse.eval_collectBalanced, rawRowCheck1134]

theorem rawRowCheck1135 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form3 = rawRow1135 := by decide +kernel

theorem rowCheck1135 : row1135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1135 := by decide +kernel

theorem rowEval1135 (x : Key → ℝ) : Integer.Sparse.eval row1135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1135, Integer.Sparse.eval_collectBalanced, rawRowCheck1135]

theorem rawRowCheck1136 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form3 = rawRow1136 := by decide +kernel

theorem rowCheck1136 : row1136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1136 := by decide +kernel

theorem rowEval1136 (x : Key → ℝ) : Integer.Sparse.eval row1136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1136, Integer.Sparse.eval_collectBalanced, rawRowCheck1136]

theorem rawRowCheck1137 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form3 = rawRow1137 := by decide +kernel

theorem rowCheck1137 : row1137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1137 := by decide +kernel

theorem rowEval1137 (x : Key → ℝ) : Integer.Sparse.eval row1137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1137, Integer.Sparse.eval_collectBalanced, rawRowCheck1137]

theorem rawRowCheck1138 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form3 = rawRow1138 := by decide +kernel

theorem rowCheck1138 : row1138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1138 := by decide +kernel

theorem rowEval1138 (x : Key → ℝ) : Integer.Sparse.eval row1138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1138, Integer.Sparse.eval_collectBalanced, rawRowCheck1138]

theorem rawRowCheck1139 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form3 = rawRow1139 := by decide +kernel

theorem rowCheck1139 : row1139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1139 := by decide +kernel

theorem rowEval1139 (x : Key → ℝ) : Integer.Sparse.eval row1139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1139, Integer.Sparse.eval_collectBalanced, rawRowCheck1139]

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

theorem rawRowCheck1154 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form5 = rawRow1154 := by decide +kernel

theorem rowCheck1154 : row1154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1154 := by decide +kernel

theorem rowEval1154 (x : Key → ℝ) : Integer.Sparse.eval row1154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1154, Integer.Sparse.eval_collectBalanced, rawRowCheck1154]

theorem rawRowCheck1155 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form5 = rawRow1155 := by decide +kernel

theorem rowCheck1155 : row1155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1155 := by decide +kernel

theorem rowEval1155 (x : Key → ℝ) : Integer.Sparse.eval row1155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1155, Integer.Sparse.eval_collectBalanced, rawRowCheck1155]

theorem rawRowCheck1156 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form5 = rawRow1156 := by decide +kernel

theorem rowCheck1156 : row1156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1156 := by decide +kernel

theorem rowEval1156 (x : Key → ℝ) : Integer.Sparse.eval row1156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1156, Integer.Sparse.eval_collectBalanced, rawRowCheck1156]

theorem rawRowCheck1157 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form5 = rawRow1157 := by decide +kernel

theorem rowCheck1157 : row1157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1157 := by decide +kernel

theorem rowEval1157 (x : Key → ℝ) : Integer.Sparse.eval row1157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1157, Integer.Sparse.eval_collectBalanced, rawRowCheck1157]

theorem rawRowCheck1158 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form5 = rawRow1158 := by decide +kernel

theorem rowCheck1158 : row1158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1158 := by decide +kernel

theorem rowEval1158 (x : Key → ℝ) : Integer.Sparse.eval row1158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1158, Integer.Sparse.eval_collectBalanced, rawRowCheck1158]

theorem rawRowCheck1159 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form5 = rawRow1159 := by decide +kernel

theorem rowCheck1159 : row1159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1159 := by decide +kernel

theorem rowEval1159 (x : Key → ℝ) : Integer.Sparse.eval row1159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1159, Integer.Sparse.eval_collectBalanced, rawRowCheck1159]

theorem rawRowCheck1160 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form5 = rawRow1160 := by decide +kernel

theorem rowCheck1160 : row1160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1160 := by decide +kernel

theorem rowEval1160 (x : Key → ℝ) : Integer.Sparse.eval row1160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1160, Integer.Sparse.eval_collectBalanced, rawRowCheck1160]

theorem rawRowCheck1161 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form5 = rawRow1161 := by decide +kernel

theorem rowCheck1161 : row1161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1161 := by decide +kernel

theorem rowEval1161 (x : Key → ℝ) : Integer.Sparse.eval row1161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1161, Integer.Sparse.eval_collectBalanced, rawRowCheck1161]

theorem rawRowCheck1162 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form5 = rawRow1162 := by decide +kernel

theorem rowCheck1162 : row1162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1162 := by decide +kernel

theorem rowEval1162 (x : Key → ℝ) : Integer.Sparse.eval row1162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1162, Integer.Sparse.eval_collectBalanced, rawRowCheck1162]

theorem rawRowCheck1163 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form5 = rawRow1163 := by decide +kernel

theorem rowCheck1163 : row1163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1163 := by decide +kernel

theorem rowEval1163 (x : Key → ℝ) : Integer.Sparse.eval row1163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1163, Integer.Sparse.eval_collectBalanced, rawRowCheck1163]

theorem rawRowCheck1164 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form5 = rawRow1164 := by decide +kernel

theorem rowCheck1164 : row1164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1164 := by decide +kernel

theorem rowEval1164 (x : Key → ℝ) : Integer.Sparse.eval row1164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1164, Integer.Sparse.eval_collectBalanced, rawRowCheck1164]

theorem rawRowCheck1165 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form5 = rawRow1165 := by decide +kernel

theorem rowCheck1165 : row1165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1165 := by decide +kernel

theorem rowEval1165 (x : Key → ℝ) : Integer.Sparse.eval row1165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1165, Integer.Sparse.eval_collectBalanced, rawRowCheck1165]

theorem rawRowCheck1166 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form5 = rawRow1166 := by decide +kernel

theorem rowCheck1166 : row1166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1166 := by decide +kernel

theorem rowEval1166 (x : Key → ℝ) : Integer.Sparse.eval row1166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1166, Integer.Sparse.eval_collectBalanced, rawRowCheck1166]

theorem rawRowCheck1167 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form5 = rawRow1167 := by decide +kernel

theorem rowCheck1167 : row1167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1167 := by decide +kernel

theorem rowEval1167 (x : Key → ℝ) : Integer.Sparse.eval row1167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1167, Integer.Sparse.eval_collectBalanced, rawRowCheck1167]

theorem rawRowCheck1168 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form6 = rawRow1168 := by decide +kernel

theorem rowCheck1168 : row1168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1168 := by decide +kernel

theorem rowEval1168 (x : Key → ℝ) : Integer.Sparse.eval row1168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1168, Integer.Sparse.eval_collectBalanced, rawRowCheck1168]

theorem rawRowCheck1169 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form6 = rawRow1169 := by decide +kernel

theorem rowCheck1169 : row1169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1169 := by decide +kernel

theorem rowEval1169 (x : Key → ℝ) : Integer.Sparse.eval row1169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1169, Integer.Sparse.eval_collectBalanced, rawRowCheck1169]

theorem rawRowCheck1170 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form6 = rawRow1170 := by decide +kernel

theorem rowCheck1170 : row1170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1170 := by decide +kernel

theorem rowEval1170 (x : Key → ℝ) : Integer.Sparse.eval row1170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1170, Integer.Sparse.eval_collectBalanced, rawRowCheck1170]

theorem rawRowCheck1171 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form6 = rawRow1171 := by decide +kernel

theorem rowCheck1171 : row1171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1171 := by decide +kernel

theorem rowEval1171 (x : Key → ℝ) : Integer.Sparse.eval row1171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1171, Integer.Sparse.eval_collectBalanced, rawRowCheck1171]

theorem rawRowCheck1172 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form6 = rawRow1172 := by decide +kernel

theorem rowCheck1172 : row1172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1172 := by decide +kernel

theorem rowEval1172 (x : Key → ℝ) : Integer.Sparse.eval row1172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1172, Integer.Sparse.eval_collectBalanced, rawRowCheck1172]

theorem rawRowCheck1173 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form6 = rawRow1173 := by decide +kernel

theorem rowCheck1173 : row1173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1173 := by decide +kernel

theorem rowEval1173 (x : Key → ℝ) : Integer.Sparse.eval row1173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1173, Integer.Sparse.eval_collectBalanced, rawRowCheck1173]

theorem rawRowCheck1174 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form6 = rawRow1174 := by decide +kernel

theorem rowCheck1174 : row1174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1174 := by decide +kernel

theorem rowEval1174 (x : Key → ℝ) : Integer.Sparse.eval row1174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1174, Integer.Sparse.eval_collectBalanced, rawRowCheck1174]

theorem rawRowCheck1175 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form6 = rawRow1175 := by decide +kernel

theorem rowCheck1175 : row1175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1175 := by decide +kernel

theorem rowEval1175 (x : Key → ℝ) : Integer.Sparse.eval row1175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1175, Integer.Sparse.eval_collectBalanced, rawRowCheck1175]

theorem rawRowCheck1176 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form6 = rawRow1176 := by decide +kernel

theorem rowCheck1176 : row1176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1176 := by decide +kernel

theorem rowEval1176 (x : Key → ℝ) : Integer.Sparse.eval row1176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1176, Integer.Sparse.eval_collectBalanced, rawRowCheck1176]

theorem rawRowCheck1177 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form6 = rawRow1177 := by decide +kernel

theorem rowCheck1177 : row1177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1177 := by decide +kernel

theorem rowEval1177 (x : Key → ℝ) : Integer.Sparse.eval row1177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1177, Integer.Sparse.eval_collectBalanced, rawRowCheck1177]

theorem rawRowCheck1178 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form6 = rawRow1178 := by decide +kernel

theorem rowCheck1178 : row1178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1178 := by decide +kernel

theorem rowEval1178 (x : Key → ℝ) : Integer.Sparse.eval row1178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1178, Integer.Sparse.eval_collectBalanced, rawRowCheck1178]

theorem rawRowCheck1179 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form6 = rawRow1179 := by decide +kernel

theorem rowCheck1179 : row1179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1179 := by decide +kernel

theorem rowEval1179 (x : Key → ℝ) : Integer.Sparse.eval row1179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1179, Integer.Sparse.eval_collectBalanced, rawRowCheck1179]

theorem rawRowCheck1180 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form6 = rawRow1180 := by decide +kernel

theorem rowCheck1180 : row1180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1180 := by decide +kernel

theorem rowEval1180 (x : Key → ℝ) : Integer.Sparse.eval row1180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1180, Integer.Sparse.eval_collectBalanced, rawRowCheck1180]

theorem rawRowCheck1181 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form6 = rawRow1181 := by decide +kernel

theorem rowCheck1181 : row1181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1181 := by decide +kernel

theorem rowEval1181 (x : Key → ℝ) : Integer.Sparse.eval row1181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1181, Integer.Sparse.eval_collectBalanced, rawRowCheck1181]

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

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1084 x
  · exact rowEval1085 x
  · exact rowEval1086 x
  · exact rowEval1087 x
  · exact rowEval1088 x
  · exact rowEval1089 x
  · exact rowEval1090 x
  · exact rowEval1091 x
  · exact rowEval1092 x
  · exact rowEval1093 x
  · exact rowEval1094 x
  · exact rowEval1095 x
  · exact rowEval1096 x
  · exact rowEval1097 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1098 x
  · exact rowEval1099 x
  · exact rowEval1100 x
  · exact rowEval1101 x
  · exact rowEval1102 x
  · exact rowEval1103 x
  · exact rowEval1104 x
  · exact rowEval1105 x
  · exact rowEval1106 x
  · exact rowEval1107 x
  · exact rowEval1108 x
  · exact rowEval1109 x
  · exact rowEval1110 x
  · exact rowEval1111 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1112 x
  · exact rowEval1113 x
  · exact rowEval1114 x
  · exact rowEval1115 x
  · exact rowEval1116 x
  · exact rowEval1117 x
  · exact rowEval1118 x
  · exact rowEval1119 x
  · exact rowEval1120 x
  · exact rowEval1121 x
  · exact rowEval1122 x
  · exact rowEval1123 x
  · exact rowEval1124 x
  · exact rowEval1125 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1126 x
  · exact rowEval1127 x
  · exact rowEval1128 x
  · exact rowEval1129 x
  · exact rowEval1130 x
  · exact rowEval1131 x
  · exact rowEval1132 x
  · exact rowEval1133 x
  · exact rowEval1134 x
  · exact rowEval1135 x
  · exact rowEval1136 x
  · exact rowEval1137 x
  · exact rowEval1138 x
  · exact rowEval1139 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

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

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1154 x
  · exact rowEval1155 x
  · exact rowEval1156 x
  · exact rowEval1157 x
  · exact rowEval1158 x
  · exact rowEval1159 x
  · exact rowEval1160 x
  · exact rowEval1161 x
  · exact rowEval1162 x
  · exact rowEval1163 x
  · exact rowEval1164 x
  · exact rowEval1165 x
  · exact rowEval1166 x
  · exact rowEval1167 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1168 x
  · exact rowEval1169 x
  · exact rowEval1170 x
  · exact rowEval1171 x
  · exact rowEval1172 x
  · exact rowEval1173 x
  · exact rowEval1174 x
  · exact rowEval1175 x
  · exact rowEval1176 x
  · exact rowEval1177 x
  · exact rowEval1178 x
  · exact rowEval1179 x
  · exact rowEval1180 x
  · exact rowEval1181 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

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

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1434 x
  · exact rowEval1435 x
  · exact rowEval1436 x
  · exact rowEval1437 x
  · exact rowEval1438 x
  · exact rowEval1439 x
  · exact rowEval1440 x
  · exact rowEval1441 x
  · exact rowEval1442 x
  · exact rowEval1443 x
  · exact rowEval1444 x
  · exact rowEval1445 x
  · exact rowEval1446 x
  · exact rowEval1447 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

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

theorem entryEvalRow6_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 6).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval6_0 B hB
  · exact entryEval6_1 B hB
  · exact entryEval6_2 B hB
  · exact entryEval6_3 B hB
  · exact entryEval6_4 B hB
  · exact entryEval6_5 B hB
  · exact entryEval6_6 B hB
  · exact (entryEval7_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e_oai
