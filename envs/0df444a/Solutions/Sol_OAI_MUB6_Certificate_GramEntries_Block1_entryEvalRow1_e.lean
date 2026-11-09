-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:34:56.23713+00:00
-- url     : https://prove2.me/submissions/13e212b6-cc08-43b5-b54b-26424e43c8d1

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
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval2_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_1_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck660 : GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow660 := by decide +kernel

theorem rowCheck660 : row660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow660 := by decide +kernel

theorem rowEval660 (x : Key → ℝ) : Integer.Sparse.eval row660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck660, Integer.Sparse.eval_collectBalanced, rawRowCheck660]

theorem rawRowCheck661 : GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow661 := by decide +kernel

theorem rowCheck661 : row661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow661 := by decide +kernel

theorem rowEval661 (x : Key → ℝ) : Integer.Sparse.eval row661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck661, Integer.Sparse.eval_collectBalanced, rawRowCheck661]

theorem rawRowCheck662 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow662 := by decide +kernel

theorem rowCheck662 : row662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow662 := by decide +kernel

theorem rowEval662 (x : Key → ℝ) : Integer.Sparse.eval row662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck662, Integer.Sparse.eval_collectBalanced, rawRowCheck662]

theorem rawRowCheck663 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow663 := by decide +kernel

theorem rowCheck663 : row663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow663 := by decide +kernel

theorem rowEval663 (x : Key → ℝ) : Integer.Sparse.eval row663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck663, Integer.Sparse.eval_collectBalanced, rawRowCheck663]

theorem rawRowCheck664 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow664 := by decide +kernel

theorem rowCheck664 : row664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow664 := by decide +kernel

theorem rowEval664 (x : Key → ℝ) : Integer.Sparse.eval row664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck664, Integer.Sparse.eval_collectBalanced, rawRowCheck664]

theorem rawRowCheck665 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow665 := by decide +kernel

theorem rowCheck665 : row665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow665 := by decide +kernel

theorem rowEval665 (x : Key → ℝ) : Integer.Sparse.eval row665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck665, Integer.Sparse.eval_collectBalanced, rawRowCheck665]

theorem rawRowCheck666 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow666 := by decide +kernel

theorem rowCheck666 : row666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow666 := by decide +kernel

theorem rowEval666 (x : Key → ℝ) : Integer.Sparse.eval row666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck666, Integer.Sparse.eval_collectBalanced, rawRowCheck666]

theorem rawRowCheck667 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow667 := by decide +kernel

theorem rowCheck667 : row667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow667 := by decide +kernel

theorem rowEval667 (x : Key → ℝ) : Integer.Sparse.eval row667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck667, Integer.Sparse.eval_collectBalanced, rawRowCheck667]

theorem rawRowCheck668 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow668 := by decide +kernel

theorem rowCheck668 : row668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow668 := by decide +kernel

theorem rowEval668 (x : Key → ℝ) : Integer.Sparse.eval row668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck668, Integer.Sparse.eval_collectBalanced, rawRowCheck668]

theorem rawRowCheck669 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow669 := by decide +kernel

theorem rowCheck669 : row669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow669 := by decide +kernel

theorem rowEval669 (x : Key → ℝ) : Integer.Sparse.eval row669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck669, Integer.Sparse.eval_collectBalanced, rawRowCheck669]

theorem rawRowCheck670 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow670 := by decide +kernel

theorem rowCheck670 : row670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow670 := by decide +kernel

theorem rowEval670 (x : Key → ℝ) : Integer.Sparse.eval row670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck670, Integer.Sparse.eval_collectBalanced, rawRowCheck670]

theorem rawRowCheck671 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow671 := by decide +kernel

theorem rowCheck671 : row671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow671 := by decide +kernel

theorem rowEval671 (x : Key → ℝ) : Integer.Sparse.eval row671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck671, Integer.Sparse.eval_collectBalanced, rawRowCheck671]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck672 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow672 := by decide +kernel

theorem rowCheck672 : row672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow672 := by decide +kernel

theorem rowEval672 (x : Key → ℝ) : Integer.Sparse.eval row672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck672, Integer.Sparse.eval_collectBalanced, rawRowCheck672]

theorem rawRowCheck673 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow673 := by decide +kernel

theorem rowCheck673 : row673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow673 := by decide +kernel

theorem rowEval673 (x : Key → ℝ) : Integer.Sparse.eval row673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck673, Integer.Sparse.eval_collectBalanced, rawRowCheck673]

theorem rawRowCheck674 : GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow674 := by decide +kernel

theorem rowCheck674 : row674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow674 := by decide +kernel

theorem rowEval674 (x : Key → ℝ) : Integer.Sparse.eval row674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck674, Integer.Sparse.eval_collectBalanced, rawRowCheck674]

theorem rawRowCheck675 : GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow675 := by decide +kernel

theorem rowCheck675 : row675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow675 := by decide +kernel

theorem rowEval675 (x : Key → ℝ) : Integer.Sparse.eval row675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck675, Integer.Sparse.eval_collectBalanced, rawRowCheck675]

theorem rawRowCheck676 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow676 := by decide +kernel

theorem rowCheck676 : row676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow676 := by decide +kernel

theorem rowEval676 (x : Key → ℝ) : Integer.Sparse.eval row676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck676, Integer.Sparse.eval_collectBalanced, rawRowCheck676]

theorem rawRowCheck677 : GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow677 := by decide +kernel

theorem rowCheck677 : row677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow677 := by decide +kernel

theorem rowEval677 (x : Key → ℝ) : Integer.Sparse.eval row677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck677, Integer.Sparse.eval_collectBalanced, rawRowCheck677]

theorem rawRowCheck678 : GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow678 := by decide +kernel

theorem rowCheck678 : row678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow678 := by decide +kernel

theorem rowEval678 (x : Key → ℝ) : Integer.Sparse.eval row678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck678, Integer.Sparse.eval_collectBalanced, rawRowCheck678]

theorem rawRowCheck679 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow679 := by decide +kernel

theorem rowCheck679 : row679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow679 := by decide +kernel

theorem rowEval679 (x : Key → ℝ) : Integer.Sparse.eval row679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck679, Integer.Sparse.eval_collectBalanced, rawRowCheck679]

theorem rawRowCheck680 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow680 := by decide +kernel

theorem rowCheck680 : row680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow680 := by decide +kernel

theorem rowEval680 (x : Key → ℝ) : Integer.Sparse.eval row680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck680, Integer.Sparse.eval_collectBalanced, rawRowCheck680]

theorem rawRowCheck681 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow681 := by decide +kernel

theorem rowCheck681 : row681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow681 := by decide +kernel

theorem rowEval681 (x : Key → ℝ) : Integer.Sparse.eval row681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck681, Integer.Sparse.eval_collectBalanced, rawRowCheck681]

theorem rawRowCheck682 : GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow682 := by decide +kernel

theorem rowCheck682 : row682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow682 := by decide +kernel

theorem rowEval682 (x : Key → ℝ) : Integer.Sparse.eval row682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck682, Integer.Sparse.eval_collectBalanced, rawRowCheck682]

theorem rawRowCheck683 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow683 := by decide +kernel

theorem rowCheck683 : row683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow683 := by decide +kernel

theorem rowEval683 (x : Key → ℝ) : Integer.Sparse.eval row683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck683, Integer.Sparse.eval_collectBalanced, rawRowCheck683]

theorem rawRowCheck684 : GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow684 := by decide +kernel

theorem rowCheck684 : row684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow684 := by decide +kernel

theorem rowEval684 (x : Key → ℝ) : Integer.Sparse.eval row684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck684, Integer.Sparse.eval_collectBalanced, rawRowCheck684]

theorem rawRowCheck685 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow685 := by decide +kernel

theorem rowCheck685 : row685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow685 := by decide +kernel

theorem rowEval685 (x : Key → ℝ) : Integer.Sparse.eval row685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck685, Integer.Sparse.eval_collectBalanced, rawRowCheck685]

theorem rawRowCheck686 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow686 := by decide +kernel

theorem rowCheck686 : row686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow686 := by decide +kernel

theorem rowEval686 (x : Key → ℝ) : Integer.Sparse.eval row686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck686, Integer.Sparse.eval_collectBalanced, rawRowCheck686]

theorem rawRowCheck687 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow687 := by decide +kernel

theorem rowCheck687 : row687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow687 := by decide +kernel

theorem rowEval687 (x : Key → ℝ) : Integer.Sparse.eval row687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck687, Integer.Sparse.eval_collectBalanced, rawRowCheck687]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block1.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form1.terms k).tag (GramFunctions.Block1.form1.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval660 x
  · exact rowEval661 x
  · exact rowEval662 x
  · exact rowEval663 x
  · exact rowEval664 x
  · exact rowEval665 x
  · exact rowEval666 x
  · exact rowEval667 x
  · exact rowEval668 x
  · exact rowEval669 x
  · exact rowEval670 x
  · exact rowEval671 x
  · exact rowEval672 x
  · exact rowEval673 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block1.form1.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form1 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

theorem entryCheck1_1 : entry1_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form1.terms k).coefficient) (rows1_1 k)) := by decide +kernel

theorem rowsSound1_1 (k : Fin GramFunctions.Block1.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form1.terms k).tag (GramFunctions.Block1.form1.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval674 x
  · exact rowEval675 x
  · exact rowEval676 x
  · exact rowEval677 x
  · exact rowEval678 x
  · exact rowEval679 x
  · exact rowEval680 x
  · exact rowEval681 x
  · exact rowEval682 x
  · exact rowEval683 x
  · exact rowEval684 x
  · exact rowEval685 x
  · exact rowEval686 x
  · exact rowEval687 x

theorem entryEval1_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_1 (GramNormalization.eval B) = GramFunctions.Block1.form1.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck1_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form1 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_1]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1778 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1778 := by decide +kernel

theorem rowCheck1778 : row1778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1778 := by decide +kernel

theorem rowEval1778 (x : Key → ℝ) : Integer.Sparse.eval row1778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1778, Integer.Sparse.eval_collectBalanced, rawRowCheck1778]

theorem rawRowCheck1779 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1779 := by decide +kernel

theorem rowCheck1779 : row1779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1779 := by decide +kernel

theorem rowEval1779 (x : Key → ℝ) : Integer.Sparse.eval row1779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1779, Integer.Sparse.eval_collectBalanced, rawRowCheck1779]

theorem rawRowCheck1780 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1780 := by decide +kernel

theorem rowCheck1780 : row1780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1780 := by decide +kernel

theorem rowEval1780 (x : Key → ℝ) : Integer.Sparse.eval row1780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1780, Integer.Sparse.eval_collectBalanced, rawRowCheck1780]

theorem rawRowCheck1781 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1781 := by decide +kernel

theorem rowCheck1781 : row1781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1781 := by decide +kernel

theorem rowEval1781 (x : Key → ℝ) : Integer.Sparse.eval row1781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1781, Integer.Sparse.eval_collectBalanced, rawRowCheck1781]

theorem rawRowCheck1782 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1 = rawRow1782 := by decide +kernel

theorem rowCheck1782 : row1782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1782 := by decide +kernel

theorem rowEval1782 (x : Key → ℝ) : Integer.Sparse.eval row1782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck1782, Integer.Sparse.eval_collectBalanced, rawRowCheck1782]

theorem rawRowCheck1783 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1 = rawRow1783 := by decide +kernel

theorem rowCheck1783 : row1783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1783 := by decide +kernel

theorem rowEval1783 (x : Key → ℝ) : Integer.Sparse.eval row1783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1783, Integer.Sparse.eval_collectBalanced, rawRowCheck1783]

theorem rawRowCheck1784 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1 = rawRow1784 := by decide +kernel

theorem rowCheck1784 : row1784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1784 := by decide +kernel

theorem rowEval1784 (x : Key → ℝ) : Integer.Sparse.eval row1784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1784, Integer.Sparse.eval_collectBalanced, rawRowCheck1784]

theorem rawRowCheck1785 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1785 := by decide +kernel

theorem rowCheck1785 : row1785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1785 := by decide +kernel

theorem rowEval1785 (x : Key → ℝ) : Integer.Sparse.eval row1785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1785, Integer.Sparse.eval_collectBalanced, rawRowCheck1785]

theorem rawRowCheck1786 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1786 := by decide +kernel

theorem rowCheck1786 : row1786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1786 := by decide +kernel

theorem rowEval1786 (x : Key → ℝ) : Integer.Sparse.eval row1786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1786, Integer.Sparse.eval_collectBalanced, rawRowCheck1786]

theorem rawRowCheck1787 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1787 := by decide +kernel

theorem rowCheck1787 : row1787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1787 := by decide +kernel

theorem rowEval1787 (x : Key → ℝ) : Integer.Sparse.eval row1787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1787, Integer.Sparse.eval_collectBalanced, rawRowCheck1787]

theorem rawRowCheck1788 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1788 := by decide +kernel

theorem rowCheck1788 : row1788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1788 := by decide +kernel

theorem rowEval1788 (x : Key → ℝ) : Integer.Sparse.eval row1788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1788, Integer.Sparse.eval_collectBalanced, rawRowCheck1788]

theorem rawRowCheck1789 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1789 := by decide +kernel

theorem rowCheck1789 : row1789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1789 := by decide +kernel

theorem rowEval1789 (x : Key → ℝ) : Integer.Sparse.eval row1789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1789, Integer.Sparse.eval_collectBalanced, rawRowCheck1789]

theorem rawRowCheck1790 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1790 := by decide +kernel

theorem rowCheck1790 : row1790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1790 := by decide +kernel

theorem rowEval1790 (x : Key → ℝ) : Integer.Sparse.eval row1790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1790, Integer.Sparse.eval_collectBalanced, rawRowCheck1790]

theorem rawRowCheck1791 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1791 := by decide +kernel

theorem rowCheck1791 : row1791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1791 := by decide +kernel

theorem rowEval1791 (x : Key → ℝ) : Integer.Sparse.eval row1791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1791, Integer.Sparse.eval_collectBalanced, rawRowCheck1791]

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

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1778 x
  · exact rowEval1779 x
  · exact rowEval1780 x
  · exact rowEval1781 x
  · exact rowEval1782 x
  · exact rowEval1783 x
  · exact rowEval1784 x
  · exact rowEval1785 x
  · exact rowEval1786 x
  · exact rowEval1787 x
  · exact rowEval1788 x
  · exact rowEval1789 x
  · exact rowEval1790 x
  · exact rowEval1791 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

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

theorem rawRowCheck1932 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1932 := by decide +kernel

theorem rowCheck1932 : row1932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1932 := by decide +kernel

theorem rowEval1932 (x : Key → ℝ) : Integer.Sparse.eval row1932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1932, Integer.Sparse.eval_collectBalanced, rawRowCheck1932]

theorem rawRowCheck1933 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1933 := by decide +kernel

theorem rowCheck1933 : row1933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1933 := by decide +kernel

theorem rowEval1933 (x : Key → ℝ) : Integer.Sparse.eval row1933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1933, Integer.Sparse.eval_collectBalanced, rawRowCheck1933]

theorem rawRowCheck1934 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1934 := by decide +kernel

theorem rowCheck1934 : row1934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1934 := by decide +kernel

theorem rowEval1934 (x : Key → ℝ) : Integer.Sparse.eval row1934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1934, Integer.Sparse.eval_collectBalanced, rawRowCheck1934]

theorem rawRowCheck1935 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1935 := by decide +kernel

theorem rowCheck1935 : row1935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1935 := by decide +kernel

theorem rowEval1935 (x : Key → ℝ) : Integer.Sparse.eval row1935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1935, Integer.Sparse.eval_collectBalanced, rawRowCheck1935]

theorem rawRowCheck1936 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1936 := by decide +kernel

theorem rowCheck1936 : row1936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1936 := by decide +kernel

theorem rowEval1936 (x : Key → ℝ) : Integer.Sparse.eval row1936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1936, Integer.Sparse.eval_collectBalanced, rawRowCheck1936]

theorem rawRowCheck1937 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1937 := by decide +kernel

theorem rowCheck1937 : row1937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1937 := by decide +kernel

theorem rowEval1937 (x : Key → ℝ) : Integer.Sparse.eval row1937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1937, Integer.Sparse.eval_collectBalanced, rawRowCheck1937]

theorem rawRowCheck1938 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1938 := by decide +kernel

theorem rowCheck1938 : row1938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1938 := by decide +kernel

theorem rowEval1938 (x : Key → ℝ) : Integer.Sparse.eval row1938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1938, Integer.Sparse.eval_collectBalanced, rawRowCheck1938]

theorem rawRowCheck1939 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1939 := by decide +kernel

theorem rowCheck1939 : row1939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1939 := by decide +kernel

theorem rowEval1939 (x : Key → ℝ) : Integer.Sparse.eval row1939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1939, Integer.Sparse.eval_collectBalanced, rawRowCheck1939]

theorem rawRowCheck1940 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1940 := by decide +kernel

theorem rowCheck1940 : row1940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1940 := by decide +kernel

theorem rowEval1940 (x : Key → ℝ) : Integer.Sparse.eval row1940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1940, Integer.Sparse.eval_collectBalanced, rawRowCheck1940]

theorem rawRowCheck1941 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1941 := by decide +kernel

theorem rowCheck1941 : row1941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1941 := by decide +kernel

theorem rowEval1941 (x : Key → ℝ) : Integer.Sparse.eval row1941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1941, Integer.Sparse.eval_collectBalanced, rawRowCheck1941]

theorem rawRowCheck1942 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1942 := by decide +kernel

theorem rowCheck1942 : row1942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1942 := by decide +kernel

theorem rowEval1942 (x : Key → ℝ) : Integer.Sparse.eval row1942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1942, Integer.Sparse.eval_collectBalanced, rawRowCheck1942]

theorem rawRowCheck1943 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1943 := by decide +kernel

theorem rowCheck1943 : row1943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1943 := by decide +kernel

theorem rowEval1943 (x : Key → ℝ) : Integer.Sparse.eval row1943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1943, Integer.Sparse.eval_collectBalanced, rawRowCheck1943]

theorem rawRowCheck1944 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1944 := by decide +kernel

theorem rowCheck1944 : row1944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1944 := by decide +kernel

theorem rowEval1944 (x : Key → ℝ) : Integer.Sparse.eval row1944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1944, Integer.Sparse.eval_collectBalanced, rawRowCheck1944]

theorem rawRowCheck1945 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1945 := by decide +kernel

theorem rowCheck1945 : row1945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1945 := by decide +kernel

theorem rowEval1945 (x : Key → ℝ) : Integer.Sparse.eval row1945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1945, Integer.Sparse.eval_collectBalanced, rawRowCheck1945]

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

theorem rawRowCheck2116 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2116 := by decide +kernel

theorem rowCheck2116 : row2116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2116 := by decide +kernel

theorem rowEval2116 (x : Key → ℝ) : Integer.Sparse.eval row2116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2116, Integer.Sparse.eval_collectBalanced, rawRowCheck2116]

theorem rawRowCheck2117 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2117 := by decide +kernel

theorem rowCheck2117 : row2117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2117 := by decide +kernel

theorem rowEval2117 (x : Key → ℝ) : Integer.Sparse.eval row2117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2117, Integer.Sparse.eval_collectBalanced, rawRowCheck2117]

theorem rawRowCheck2118 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2118 := by decide +kernel

theorem rowCheck2118 : row2118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2118 := by decide +kernel

theorem rowEval2118 (x : Key → ℝ) : Integer.Sparse.eval row2118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2118, Integer.Sparse.eval_collectBalanced, rawRowCheck2118]

theorem rawRowCheck2125 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2125 := by decide +kernel

theorem rowCheck2125 : row2125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2125 := by decide +kernel

theorem rowEval2125 (x : Key → ℝ) : Integer.Sparse.eval row2125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2125, Integer.Sparse.eval_collectBalanced, rawRowCheck2125]

theorem rawRowCheck2126 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2126 := by decide +kernel

theorem rowCheck2126 : row2126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2126 := by decide +kernel

theorem rowEval2126 (x : Key → ℝ) : Integer.Sparse.eval row2126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2126, Integer.Sparse.eval_collectBalanced, rawRowCheck2126]

theorem rawRowCheck2127 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2127 := by decide +kernel

theorem rowCheck2127 : row2127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2127 := by decide +kernel

theorem rowEval2127 (x : Key → ℝ) : Integer.Sparse.eval row2127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2127, Integer.Sparse.eval_collectBalanced, rawRowCheck2127]

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

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1932 x
  · exact rowEval1933 x
  · exact rowEval1934 x
  · exact rowEval1935 x
  · exact rowEval1936 x
  · exact rowEval1937 x
  · exact rowEval1938 x
  · exact rowEval1939 x
  · exact rowEval1940 x
  · exact rowEval1941 x
  · exact rowEval1942 x
  · exact rowEval1943 x
  · exact rowEval1944 x
  · exact rowEval1945 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck2490 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2490 := by decide +kernel

theorem rowCheck2490 : row2490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2490 := by decide +kernel

theorem rowEval2490 (x : Key → ℝ) : Integer.Sparse.eval row2490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2490, Integer.Sparse.eval_collectBalanced, rawRowCheck2490]

theorem rawRowCheck2491 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2491 := by decide +kernel

theorem rowCheck2491 : row2491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2491 := by decide +kernel

theorem rowEval2491 (x : Key → ℝ) : Integer.Sparse.eval row2491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2491, Integer.Sparse.eval_collectBalanced, rawRowCheck2491]

theorem rawRowCheck2492 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2492 := by decide +kernel

theorem rowCheck2492 : row2492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2492 := by decide +kernel

theorem rowEval2492 (x : Key → ℝ) : Integer.Sparse.eval row2492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2492, Integer.Sparse.eval_collectBalanced, rawRowCheck2492]

theorem rawRowCheck2493 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2493 := by decide +kernel

theorem rowCheck2493 : row2493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2493 := by decide +kernel

theorem rowEval2493 (x : Key → ℝ) : Integer.Sparse.eval row2493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2493, Integer.Sparse.eval_collectBalanced, rawRowCheck2493]

theorem rawRowCheck2494 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2494 := by decide +kernel

theorem rowCheck2494 : row2494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2494 := by decide +kernel

theorem rowEval2494 (x : Key → ℝ) : Integer.Sparse.eval row2494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2494, Integer.Sparse.eval_collectBalanced, rawRowCheck2494]

theorem rawRowCheck2495 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2495 := by decide +kernel

theorem rowCheck2495 : row2495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2495 := by decide +kernel

theorem rowEval2495 (x : Key → ℝ) : Integer.Sparse.eval row2495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2495, Integer.Sparse.eval_collectBalanced, rawRowCheck2495]

theorem rawRowCheck2496 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2496 := by decide +kernel

theorem rowCheck2496 : row2496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2496 := by decide +kernel

theorem rowEval2496 (x : Key → ℝ) : Integer.Sparse.eval row2496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2496, Integer.Sparse.eval_collectBalanced, rawRowCheck2496]

theorem rawRowCheck2497 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2497 := by decide +kernel

theorem rowCheck2497 : row2497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2497 := by decide +kernel

theorem rowEval2497 (x : Key → ℝ) : Integer.Sparse.eval row2497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2497, Integer.Sparse.eval_collectBalanced, rawRowCheck2497]

theorem rawRowCheck2498 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2498 := by decide +kernel

theorem rowCheck2498 : row2498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2498 := by decide +kernel

theorem rowEval2498 (x : Key → ℝ) : Integer.Sparse.eval row2498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2498, Integer.Sparse.eval_collectBalanced, rawRowCheck2498]

theorem rawRowCheck2499 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2499 := by decide +kernel

theorem rowCheck2499 : row2499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2499 := by decide +kernel

theorem rowEval2499 (x : Key → ℝ) : Integer.Sparse.eval row2499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2499, Integer.Sparse.eval_collectBalanced, rawRowCheck2499]

theorem rawRowCheck2500 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2500 := by decide +kernel

theorem rowCheck2500 : row2500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2500 := by decide +kernel

theorem rowEval2500 (x : Key → ℝ) : Integer.Sparse.eval row2500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2500, Integer.Sparse.eval_collectBalanced, rawRowCheck2500]

theorem rawRowCheck2501 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2501 := by decide +kernel

theorem rowCheck2501 : row2501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2501 := by decide +kernel

theorem rowEval2501 (x : Key → ℝ) : Integer.Sparse.eval row2501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2501, Integer.Sparse.eval_collectBalanced, rawRowCheck2501]

theorem rawRowCheck2502 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2502 := by decide +kernel

theorem rowCheck2502 : row2502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2502 := by decide +kernel

theorem rowEval2502 (x : Key → ℝ) : Integer.Sparse.eval row2502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2502, Integer.Sparse.eval_collectBalanced, rawRowCheck2502]

theorem rawRowCheck2503 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2503 := by decide +kernel

theorem rowCheck2503 : row2503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2503 := by decide +kernel

theorem rowEval2503 (x : Key → ℝ) : Integer.Sparse.eval row2503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2503, Integer.Sparse.eval_collectBalanced, rawRowCheck2503]

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

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2490 x
  · exact rowEval2491 x
  · exact rowEval2492 x
  · exact rowEval2493 x
  · exact rowEval2494 x
  · exact rowEval2495 x
  · exact rowEval2496 x
  · exact rowEval2497 x
  · exact rowEval2498 x
  · exact rowEval2499 x
  · exact rowEval2500 x
  · exact rowEval2501 x
  · exact rowEval2502 x
  · exact rowEval2503 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

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

theorem rawRowCheck2696 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form1 = rawRow2696 := by decide +kernel

theorem rowCheck2696 : row2696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2696 := by decide +kernel

theorem rowEval2696 (x : Key → ℝ) : Integer.Sparse.eval row2696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2696, Integer.Sparse.eval_collectBalanced, rawRowCheck2696]

theorem rawRowCheck2697 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form1 = rawRow2697 := by decide +kernel

theorem rowCheck2697 : row2697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2697 := by decide +kernel

theorem rowEval2697 (x : Key → ℝ) : Integer.Sparse.eval row2697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2697, Integer.Sparse.eval_collectBalanced, rawRowCheck2697]

theorem rawRowCheck2698 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form1 = rawRow2698 := by decide +kernel

theorem rowCheck2698 : row2698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2698 := by decide +kernel

theorem rowEval2698 (x : Key → ℝ) : Integer.Sparse.eval row2698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2698, Integer.Sparse.eval_collectBalanced, rawRowCheck2698]

theorem rawRowCheck2699 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2699 := by decide +kernel

theorem rowCheck2699 : row2699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2699 := by decide +kernel

theorem rowEval2699 (x : Key → ℝ) : Integer.Sparse.eval row2699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2699, Integer.Sparse.eval_collectBalanced, rawRowCheck2699]

theorem rawRowCheck2700 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2700 := by decide +kernel

theorem rowCheck2700 : row2700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2700 := by decide +kernel

theorem rowEval2700 (x : Key → ℝ) : Integer.Sparse.eval row2700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2700, Integer.Sparse.eval_collectBalanced, rawRowCheck2700]

theorem rawRowCheck2701 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2701 := by decide +kernel

theorem rowCheck2701 : row2701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2701 := by decide +kernel

theorem rowEval2701 (x : Key → ℝ) : Integer.Sparse.eval row2701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2701, Integer.Sparse.eval_collectBalanced, rawRowCheck2701]

theorem rawRowCheck2702 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form1 = rawRow2702 := by decide +kernel

theorem rowCheck2702 : row2702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2702 := by decide +kernel

theorem rowEval2702 (x : Key → ℝ) : Integer.Sparse.eval row2702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2702, Integer.Sparse.eval_collectBalanced, rawRowCheck2702]

theorem rawRowCheck2703 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form1 = rawRow2703 := by decide +kernel

theorem rowCheck2703 : row2703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2703 := by decide +kernel

theorem rowEval2703 (x : Key → ℝ) : Integer.Sparse.eval row2703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2703, Integer.Sparse.eval_collectBalanced, rawRowCheck2703]

theorem rawRowCheck2704 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form1 = rawRow2704 := by decide +kernel

theorem rowCheck2704 : row2704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2704 := by decide +kernel

theorem rowEval2704 (x : Key → ℝ) : Integer.Sparse.eval row2704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2704, Integer.Sparse.eval_collectBalanced, rawRowCheck2704]

theorem rawRowCheck2705 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form1 = rawRow2705 := by decide +kernel

theorem rowCheck2705 : row2705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2705 := by decide +kernel

theorem rowEval2705 (x : Key → ℝ) : Integer.Sparse.eval row2705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2705, Integer.Sparse.eval_collectBalanced, rawRowCheck2705]

theorem rawRowCheck2706 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form1 = rawRow2706 := by decide +kernel

theorem rowCheck2706 : row2706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2706 := by decide +kernel

theorem rowEval2706 (x : Key → ℝ) : Integer.Sparse.eval row2706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2706, Integer.Sparse.eval_collectBalanced, rawRowCheck2706]

theorem rawRowCheck2707 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form1 = rawRow2707 := by decide +kernel

theorem rowCheck2707 : row2707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2707 := by decide +kernel

theorem rowEval2707 (x : Key → ℝ) : Integer.Sparse.eval row2707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2707, Integer.Sparse.eval_collectBalanced, rawRowCheck2707]

theorem rawRowCheck2708 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form1 = rawRow2708 := by decide +kernel

theorem rowCheck2708 : row2708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2708 := by decide +kernel

theorem rowEval2708 (x : Key → ℝ) : Integer.Sparse.eval row2708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2708, Integer.Sparse.eval_collectBalanced, rawRowCheck2708]

theorem rawRowCheck2709 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form1 = rawRow2709 := by decide +kernel

theorem rowCheck2709 : row2709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2709 := by decide +kernel

theorem rowEval2709 (x : Key → ℝ) : Integer.Sparse.eval row2709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2709, Integer.Sparse.eval_collectBalanced, rawRowCheck2709]

theorem rawRowCheck2710 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form1 = rawRow2710 := by decide +kernel

theorem rowCheck2710 : row2710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2710 := by decide +kernel

theorem rowEval2710 (x : Key → ℝ) : Integer.Sparse.eval row2710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2710, Integer.Sparse.eval_collectBalanced, rawRowCheck2710]

theorem rawRowCheck2711 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2711 := by decide +kernel

theorem rowCheck2711 : row2711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2711 := by decide +kernel

theorem rowEval2711 (x : Key → ℝ) : Integer.Sparse.eval row2711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2711, Integer.Sparse.eval_collectBalanced, rawRowCheck2711]

theorem rawRowCheck2712 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2712 := by decide +kernel

theorem rowCheck2712 : row2712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2712 := by decide +kernel

theorem rowEval2712 (x : Key → ℝ) : Integer.Sparse.eval row2712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2712, Integer.Sparse.eval_collectBalanced, rawRowCheck2712]

theorem rawRowCheck2713 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2713 := by decide +kernel

theorem rowCheck2713 : row2713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2713 := by decide +kernel

theorem rowEval2713 (x : Key → ℝ) : Integer.Sparse.eval row2713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2713, Integer.Sparse.eval_collectBalanced, rawRowCheck2713]

theorem rawRowCheck2714 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form1 = rawRow2714 := by decide +kernel

theorem rowCheck2714 : row2714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2714 := by decide +kernel

theorem rowEval2714 (x : Key → ℝ) : Integer.Sparse.eval row2714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2714, Integer.Sparse.eval_collectBalanced, rawRowCheck2714]

theorem rawRowCheck2715 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form1 = rawRow2715 := by decide +kernel

theorem rowCheck2715 : row2715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2715 := by decide +kernel

theorem rowEval2715 (x : Key → ℝ) : Integer.Sparse.eval row2715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2715, Integer.Sparse.eval_collectBalanced, rawRowCheck2715]

theorem rawRowCheck2716 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form1 = rawRow2716 := by decide +kernel

theorem rowCheck2716 : row2716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2716 := by decide +kernel

theorem rowEval2716 (x : Key → ℝ) : Integer.Sparse.eval row2716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2716, Integer.Sparse.eval_collectBalanced, rawRowCheck2716]

theorem rawRowCheck2717 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form1 = rawRow2717 := by decide +kernel

theorem rowCheck2717 : row2717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2717 := by decide +kernel

theorem rowEval2717 (x : Key → ℝ) : Integer.Sparse.eval row2717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2717, Integer.Sparse.eval_collectBalanced, rawRowCheck2717]

theorem rawRowCheck2718 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form1 = rawRow2718 := by decide +kernel

theorem rowCheck2718 : row2718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2718 := by decide +kernel

theorem rowEval2718 (x : Key → ℝ) : Integer.Sparse.eval row2718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2718, Integer.Sparse.eval_collectBalanced, rawRowCheck2718]

theorem rawRowCheck2719 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form1 = rawRow2719 := by decide +kernel

theorem rowCheck2719 : row2719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2719 := by decide +kernel

theorem rowEval2719 (x : Key → ℝ) : Integer.Sparse.eval row2719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck2719, Integer.Sparse.eval_collectBalanced, rawRowCheck2719]

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

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2696 x
  · exact rowEval2697 x
  · exact rowEval2698 x
  · exact rowEval2699 x
  · exact rowEval2700 x
  · exact rowEval2701 x
  · exact rowEval2702 x
  · exact rowEval2703 x
  · exact rowEval2704 x
  · exact rowEval2705 x
  · exact rowEval2706 x
  · exact rowEval2707 x
  · exact rowEval2708 x
  · exact rowEval2709 x
  · exact rowEval2710 x
  · exact rowEval2711 x
  · exact rowEval2712 x
  · exact rowEval2713 x
  · exact rowEval2714 x
  · exact rowEval2715 x
  · exact rowEval2716 x
  · exact rowEval2717 x
  · exact rowEval2718 x
  · exact rowEval2719 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck792 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow792 := by decide +kernel

theorem rowCheck792 : row792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow792 := by decide +kernel

theorem rowEval792 (x : Key → ℝ) : Integer.Sparse.eval row792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck792, Integer.Sparse.eval_collectBalanced, rawRowCheck792]

theorem rawRowCheck793 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow793 := by decide +kernel

theorem rowCheck793 : row793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow793 := by decide +kernel

theorem rowEval793 (x : Key → ℝ) : Integer.Sparse.eval row793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck793, Integer.Sparse.eval_collectBalanced, rawRowCheck793]

theorem rawRowCheck794 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow794 := by decide +kernel

theorem rowCheck794 : row794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow794 := by decide +kernel

theorem rowEval794 (x : Key → ℝ) : Integer.Sparse.eval row794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck794, Integer.Sparse.eval_collectBalanced, rawRowCheck794]

theorem rawRowCheck795 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow795 := by decide +kernel

theorem rowCheck795 : row795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow795 := by decide +kernel

theorem rowEval795 (x : Key → ℝ) : Integer.Sparse.eval row795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck795, Integer.Sparse.eval_collectBalanced, rawRowCheck795]

theorem rawRowCheck796 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1 = rawRow796 := by decide +kernel

theorem rowCheck796 : row796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow796 := by decide +kernel

theorem rowEval796 (x : Key → ℝ) : Integer.Sparse.eval row796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck796, Integer.Sparse.eval_collectBalanced, rawRowCheck796]

theorem rawRowCheck797 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1 = rawRow797 := by decide +kernel

theorem rowCheck797 : row797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow797 := by decide +kernel

theorem rowEval797 (x : Key → ℝ) : Integer.Sparse.eval row797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck797, Integer.Sparse.eval_collectBalanced, rawRowCheck797]

theorem rawRowCheck798 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1 = rawRow798 := by decide +kernel

theorem rowCheck798 : row798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow798 := by decide +kernel

theorem rowEval798 (x : Key → ℝ) : Integer.Sparse.eval row798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck798, Integer.Sparse.eval_collectBalanced, rawRowCheck798]

theorem rawRowCheck799 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1 = rawRow799 := by decide +kernel

theorem rowCheck799 : row799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow799 := by decide +kernel

theorem rowEval799 (x : Key → ℝ) : Integer.Sparse.eval row799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck799, Integer.Sparse.eval_collectBalanced, rawRowCheck799]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck3488 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form1 = rawRow3488 := by decide +kernel

theorem rowCheck3488 : row3488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3488 := by decide +kernel

theorem rowEval3488 (x : Key → ℝ) : Integer.Sparse.eval row3488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3488, Integer.Sparse.eval_collectBalanced, rawRowCheck3488]

theorem rawRowCheck3489 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form1 = rawRow3489 := by decide +kernel

theorem rowCheck3489 : row3489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3489 := by decide +kernel

theorem rowEval3489 (x : Key → ℝ) : Integer.Sparse.eval row3489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3489, Integer.Sparse.eval_collectBalanced, rawRowCheck3489]

theorem rawRowCheck3490 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form1 = rawRow3490 := by decide +kernel

theorem rowCheck3490 : row3490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3490 := by decide +kernel

theorem rowEval3490 (x : Key → ℝ) : Integer.Sparse.eval row3490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3490, Integer.Sparse.eval_collectBalanced, rawRowCheck3490]

theorem rawRowCheck3491 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3491 := by decide +kernel

theorem rowCheck3491 : row3491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3491 := by decide +kernel

theorem rowEval3491 (x : Key → ℝ) : Integer.Sparse.eval row3491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3491, Integer.Sparse.eval_collectBalanced, rawRowCheck3491]

theorem rawRowCheck3492 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3492 := by decide +kernel

theorem rowCheck3492 : row3492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3492 := by decide +kernel

theorem rowEval3492 (x : Key → ℝ) : Integer.Sparse.eval row3492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3492, Integer.Sparse.eval_collectBalanced, rawRowCheck3492]

theorem rawRowCheck3493 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3493 := by decide +kernel

theorem rowCheck3493 : row3493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3493 := by decide +kernel

theorem rowEval3493 (x : Key → ℝ) : Integer.Sparse.eval row3493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3493, Integer.Sparse.eval_collectBalanced, rawRowCheck3493]

theorem rawRowCheck3494 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow3494 := by decide +kernel

theorem rowCheck3494 : row3494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3494 := by decide +kernel

theorem rowEval3494 (x : Key → ℝ) : Integer.Sparse.eval row3494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3494, Integer.Sparse.eval_collectBalanced, rawRowCheck3494]

theorem rawRowCheck3495 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow3495 := by decide +kernel

theorem rowCheck3495 : row3495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3495 := by decide +kernel

theorem rowEval3495 (x : Key → ℝ) : Integer.Sparse.eval row3495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3495, Integer.Sparse.eval_collectBalanced, rawRowCheck3495]

theorem rawRowCheck3496 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow3496 := by decide +kernel

theorem rowCheck3496 : row3496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3496 := by decide +kernel

theorem rowEval3496 (x : Key → ℝ) : Integer.Sparse.eval row3496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3496, Integer.Sparse.eval_collectBalanced, rawRowCheck3496]

theorem rawRowCheck3497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3497 := by decide +kernel

theorem rowCheck3497 : row3497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3497 := by decide +kernel

theorem rowEval3497 (x : Key → ℝ) : Integer.Sparse.eval row3497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3497, Integer.Sparse.eval_collectBalanced, rawRowCheck3497]

theorem rawRowCheck3498 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3498 := by decide +kernel

theorem rowCheck3498 : row3498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3498 := by decide +kernel

theorem rowEval3498 (x : Key → ℝ) : Integer.Sparse.eval row3498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3498, Integer.Sparse.eval_collectBalanced, rawRowCheck3498]

theorem rawRowCheck3499 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3499 := by decide +kernel

theorem rowCheck3499 : row3499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3499 := by decide +kernel

theorem rowEval3499 (x : Key → ℝ) : Integer.Sparse.eval row3499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3499, Integer.Sparse.eval_collectBalanced, rawRowCheck3499]

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

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2116 x
  · exact rowEval2117 x
  · exact rowEval2118 x
  · exact rowEval3488 x
  · exact rowEval3489 x
  · exact rowEval3490 x
  · exact rowEval2125 x
  · exact rowEval2126 x
  · exact rowEval2127 x
  · exact rowEval3491 x
  · exact rowEval3492 x
  · exact rowEval3493 x
  · exact rowEval3494 x
  · exact rowEval3495 x
  · exact rowEval3496 x
  · exact rowEval3497 x
  · exact rowEval3498 x
  · exact rowEval3499 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck3734 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3734 := by decide +kernel

theorem rowCheck3734 : row3734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3734 := by decide +kernel

theorem rowEval3734 (x : Key → ℝ) : Integer.Sparse.eval row3734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3734, Integer.Sparse.eval_collectBalanced, rawRowCheck3734]

theorem rawRowCheck3735 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3735 := by decide +kernel

theorem rowCheck3735 : row3735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3735 := by decide +kernel

theorem rowEval3735 (x : Key → ℝ) : Integer.Sparse.eval row3735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3735, Integer.Sparse.eval_collectBalanced, rawRowCheck3735]

theorem rawRowCheck3736 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3736 := by decide +kernel

theorem rowCheck3736 : row3736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3736 := by decide +kernel

theorem rowEval3736 (x : Key → ℝ) : Integer.Sparse.eval row3736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3736, Integer.Sparse.eval_collectBalanced, rawRowCheck3736]

theorem rawRowCheck3737 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3737 := by decide +kernel

theorem rowCheck3737 : row3737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3737 := by decide +kernel

theorem rowEval3737 (x : Key → ℝ) : Integer.Sparse.eval row3737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3737, Integer.Sparse.eval_collectBalanced, rawRowCheck3737]

theorem rawRowCheck3738 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3738 := by decide +kernel

theorem rowCheck3738 : row3738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3738 := by decide +kernel

theorem rowEval3738 (x : Key → ℝ) : Integer.Sparse.eval row3738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3738, Integer.Sparse.eval_collectBalanced, rawRowCheck3738]

theorem rawRowCheck3739 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3739 := by decide +kernel

theorem rowCheck3739 : row3739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3739 := by decide +kernel

theorem rowEval3739 (x : Key → ℝ) : Integer.Sparse.eval row3739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3739, Integer.Sparse.eval_collectBalanced, rawRowCheck3739]

theorem rawRowCheck3740 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3740 := by decide +kernel

theorem rowCheck3740 : row3740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3740 := by decide +kernel

theorem rowEval3740 (x : Key → ℝ) : Integer.Sparse.eval row3740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3740, Integer.Sparse.eval_collectBalanced, rawRowCheck3740]

theorem rawRowCheck3741 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3741 := by decide +kernel

theorem rowCheck3741 : row3741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3741 := by decide +kernel

theorem rowEval3741 (x : Key → ℝ) : Integer.Sparse.eval row3741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3741, Integer.Sparse.eval_collectBalanced, rawRowCheck3741]

theorem rawRowCheck3742 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3742 := by decide +kernel

theorem rowCheck3742 : row3742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3742 := by decide +kernel

theorem rowEval3742 (x : Key → ℝ) : Integer.Sparse.eval row3742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3742, Integer.Sparse.eval_collectBalanced, rawRowCheck3742]

theorem rawRowCheck3743 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3743 := by decide +kernel

theorem rowCheck3743 : row3743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3743 := by decide +kernel

theorem rowEval3743 (x : Key → ℝ) : Integer.Sparse.eval row3743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3743, Integer.Sparse.eval_collectBalanced, rawRowCheck3743]

theorem rawRowCheck3744 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3744 := by decide +kernel

theorem rowCheck3744 : row3744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3744 := by decide +kernel

theorem rowEval3744 (x : Key → ℝ) : Integer.Sparse.eval row3744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3744, Integer.Sparse.eval_collectBalanced, rawRowCheck3744]

theorem rawRowCheck3745 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3745 := by decide +kernel

theorem rowCheck3745 : row3745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3745 := by decide +kernel

theorem rowEval3745 (x : Key → ℝ) : Integer.Sparse.eval row3745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3745, Integer.Sparse.eval_collectBalanced, rawRowCheck3745]

theorem rawRowCheck3746 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3746 := by decide +kernel

theorem rowCheck3746 : row3746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3746 := by decide +kernel

theorem rowEval3746 (x : Key → ℝ) : Integer.Sparse.eval row3746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3746, Integer.Sparse.eval_collectBalanced, rawRowCheck3746]

theorem rawRowCheck3747 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3747 := by decide +kernel

theorem rowCheck3747 : row3747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3747 := by decide +kernel

theorem rowEval3747 (x : Key → ℝ) : Integer.Sparse.eval row3747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3747, Integer.Sparse.eval_collectBalanced, rawRowCheck3747]

theorem rawRowCheck3748 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3748 := by decide +kernel

theorem rowCheck3748 : row3748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3748 := by decide +kernel

theorem rowEval3748 (x : Key → ℝ) : Integer.Sparse.eval row3748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3748, Integer.Sparse.eval_collectBalanced, rawRowCheck3748]

theorem rawRowCheck3749 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3749 := by decide +kernel

theorem rowCheck3749 : row3749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3749 := by decide +kernel

theorem rowEval3749 (x : Key → ℝ) : Integer.Sparse.eval row3749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3749, Integer.Sparse.eval_collectBalanced, rawRowCheck3749]

theorem rawRowCheck3750 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3750 := by decide +kernel

theorem rowCheck3750 : row3750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3750 := by decide +kernel

theorem rowEval3750 (x : Key → ℝ) : Integer.Sparse.eval row3750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3750, Integer.Sparse.eval_collectBalanced, rawRowCheck3750]

theorem rawRowCheck3751 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3751 := by decide +kernel

theorem rowCheck3751 : row3751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3751 := by decide +kernel

theorem rowEval3751 (x : Key → ℝ) : Integer.Sparse.eval row3751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3751, Integer.Sparse.eval_collectBalanced, rawRowCheck3751]

theorem rawRowCheck3752 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3752 := by decide +kernel

theorem rowCheck3752 : row3752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3752 := by decide +kernel

theorem rowEval3752 (x : Key → ℝ) : Integer.Sparse.eval row3752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3752, Integer.Sparse.eval_collectBalanced, rawRowCheck3752]

theorem rawRowCheck3753 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3753 := by decide +kernel

theorem rowCheck3753 : row3753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3753 := by decide +kernel

theorem rowEval3753 (x : Key → ℝ) : Integer.Sparse.eval row3753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3753, Integer.Sparse.eval_collectBalanced, rawRowCheck3753]

theorem rawRowCheck3754 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3754 := by decide +kernel

theorem rowCheck3754 : row3754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3754 := by decide +kernel

theorem rowEval3754 (x : Key → ℝ) : Integer.Sparse.eval row3754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3754, Integer.Sparse.eval_collectBalanced, rawRowCheck3754]

theorem rawRowCheck3755 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3755 := by decide +kernel

theorem rowCheck3755 : row3755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3755 := by decide +kernel

theorem rowEval3755 (x : Key → ℝ) : Integer.Sparse.eval row3755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3755, Integer.Sparse.eval_collectBalanced, rawRowCheck3755]

theorem rawRowCheck3756 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3756 := by decide +kernel

theorem rowCheck3756 : row3756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3756 := by decide +kernel

theorem rowEval3756 (x : Key → ℝ) : Integer.Sparse.eval row3756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3756, Integer.Sparse.eval_collectBalanced, rawRowCheck3756]

theorem rawRowCheck3757 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3757 := by decide +kernel

theorem rowCheck3757 : row3757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3757 := by decide +kernel

theorem rowEval3757 (x : Key → ℝ) : Integer.Sparse.eval row3757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3757, Integer.Sparse.eval_collectBalanced, rawRowCheck3757]

theorem rawRowCheck3758 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3758 := by decide +kernel

theorem rowCheck3758 : row3758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3758 := by decide +kernel

theorem rowEval3758 (x : Key → ℝ) : Integer.Sparse.eval row3758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3758, Integer.Sparse.eval_collectBalanced, rawRowCheck3758]

theorem rawRowCheck3759 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3759 := by decide +kernel

theorem rowCheck3759 : row3759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3759 := by decide +kernel

theorem rowEval3759 (x : Key → ℝ) : Integer.Sparse.eval row3759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3759, Integer.Sparse.eval_collectBalanced, rawRowCheck3759]

theorem rawRowCheck3760 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3760 := by decide +kernel

theorem rowCheck3760 : row3760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3760 := by decide +kernel

theorem rowEval3760 (x : Key → ℝ) : Integer.Sparse.eval row3760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3760, Integer.Sparse.eval_collectBalanced, rawRowCheck3760]

theorem rawRowCheck3761 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3761 := by decide +kernel

theorem rowCheck3761 : row3761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3761 := by decide +kernel

theorem rowEval3761 (x : Key → ℝ) : Integer.Sparse.eval row3761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3761, Integer.Sparse.eval_collectBalanced, rawRowCheck3761]

theorem rawRowCheck3762 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3762 := by decide +kernel

theorem rowCheck3762 : row3762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3762 := by decide +kernel

theorem rowEval3762 (x : Key → ℝ) : Integer.Sparse.eval row3762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3762, Integer.Sparse.eval_collectBalanced, rawRowCheck3762]

theorem rawRowCheck3763 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3763 := by decide +kernel

theorem rowCheck3763 : row3763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3763 := by decide +kernel

theorem rowEval3763 (x : Key → ℝ) : Integer.Sparse.eval row3763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3763, Integer.Sparse.eval_collectBalanced, rawRowCheck3763]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval3734 x
  · exact rowEval3735 x
  · exact rowEval3736 x
  · exact rowEval3737 x
  · exact rowEval3738 x
  · exact rowEval3739 x
  · exact rowEval3740 x
  · exact rowEval3741 x
  · exact rowEval3742 x
  · exact rowEval3743 x
  · exact rowEval3744 x
  · exact rowEval3745 x
  · exact rowEval3746 x
  · exact rowEval3747 x
  · exact rowEval3748 x
  · exact rowEval3749 x
  · exact rowEval3750 x
  · exact rowEval3751 x
  · exact rowEval3752 x
  · exact rowEval3753 x
  · exact rowEval3754 x
  · exact rowEval3755 x
  · exact rowEval3756 x
  · exact rowEval3757 x
  · exact rowEval3758 x
  · exact rowEval3759 x
  · exact rowEval3760 x
  · exact rowEval3761 x
  · exact rowEval3762 x
  · exact rowEval3763 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4570 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4570 := by decide +kernel

theorem rowCheck4570 : row4570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4570 := by decide +kernel

theorem rowEval4570 (x : Key → ℝ) : Integer.Sparse.eval row4570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4570, Integer.Sparse.eval_collectBalanced, rawRowCheck4570]

theorem rawRowCheck4571 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4571 := by decide +kernel

theorem rowCheck4571 : row4571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4571 := by decide +kernel

theorem rowEval4571 (x : Key → ℝ) : Integer.Sparse.eval row4571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4571, Integer.Sparse.eval_collectBalanced, rawRowCheck4571]

theorem rawRowCheck4572 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4572 := by decide +kernel

theorem rowCheck4572 : row4572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4572 := by decide +kernel

theorem rowEval4572 (x : Key → ℝ) : Integer.Sparse.eval row4572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4572, Integer.Sparse.eval_collectBalanced, rawRowCheck4572]

theorem rawRowCheck4573 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4573 := by decide +kernel

theorem rowCheck4573 : row4573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4573 := by decide +kernel

theorem rowEval4573 (x : Key → ℝ) : Integer.Sparse.eval row4573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4573, Integer.Sparse.eval_collectBalanced, rawRowCheck4573]

theorem rawRowCheck4574 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4574 := by decide +kernel

theorem rowCheck4574 : row4574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4574 := by decide +kernel

theorem rowEval4574 (x : Key → ℝ) : Integer.Sparse.eval row4574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4574, Integer.Sparse.eval_collectBalanced, rawRowCheck4574]

theorem rawRowCheck4575 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4575 := by decide +kernel

theorem rowCheck4575 : row4575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4575 := by decide +kernel

theorem rowEval4575 (x : Key → ℝ) : Integer.Sparse.eval row4575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4575, Integer.Sparse.eval_collectBalanced, rawRowCheck4575]

theorem rawRowCheck4576 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4576 := by decide +kernel

theorem rowCheck4576 : row4576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4576 := by decide +kernel

theorem rowEval4576 (x : Key → ℝ) : Integer.Sparse.eval row4576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4576, Integer.Sparse.eval_collectBalanced, rawRowCheck4576]

theorem rawRowCheck4577 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4577 := by decide +kernel

theorem rowCheck4577 : row4577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4577 := by decide +kernel

theorem rowEval4577 (x : Key → ℝ) : Integer.Sparse.eval row4577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4577, Integer.Sparse.eval_collectBalanced, rawRowCheck4577]

theorem rawRowCheck4578 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4578 := by decide +kernel

theorem rowCheck4578 : row4578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4578 := by decide +kernel

theorem rowEval4578 (x : Key → ℝ) : Integer.Sparse.eval row4578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4578, Integer.Sparse.eval_collectBalanced, rawRowCheck4578]

theorem rawRowCheck4579 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4579 := by decide +kernel

theorem rowCheck4579 : row4579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4579 := by decide +kernel

theorem rowEval4579 (x : Key → ℝ) : Integer.Sparse.eval row4579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4579, Integer.Sparse.eval_collectBalanced, rawRowCheck4579]

theorem rawRowCheck4580 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4580 := by decide +kernel

theorem rowCheck4580 : row4580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4580 := by decide +kernel

theorem rowEval4580 (x : Key → ℝ) : Integer.Sparse.eval row4580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4580, Integer.Sparse.eval_collectBalanced, rawRowCheck4580]

theorem rawRowCheck4581 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4581 := by decide +kernel

theorem rowCheck4581 : row4581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4581 := by decide +kernel

theorem rowEval4581 (x : Key → ℝ) : Integer.Sparse.eval row4581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4581, Integer.Sparse.eval_collectBalanced, rawRowCheck4581]

theorem rawRowCheck4582 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4582 := by decide +kernel

theorem rowCheck4582 : row4582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4582 := by decide +kernel

theorem rowEval4582 (x : Key → ℝ) : Integer.Sparse.eval row4582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4582, Integer.Sparse.eval_collectBalanced, rawRowCheck4582]

theorem rawRowCheck4583 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4583 := by decide +kernel

theorem rowCheck4583 : row4583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4583 := by decide +kernel

theorem rowEval4583 (x : Key → ℝ) : Integer.Sparse.eval row4583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4583, Integer.Sparse.eval_collectBalanced, rawRowCheck4583]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4842 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4842 := by decide +kernel

theorem rowCheck4842 : row4842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4842 := by decide +kernel

theorem rowEval4842 (x : Key → ℝ) : Integer.Sparse.eval row4842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4842, Integer.Sparse.eval_collectBalanced, rawRowCheck4842]

theorem rawRowCheck4843 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4843 := by decide +kernel

theorem rowCheck4843 : row4843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4843 := by decide +kernel

theorem rowEval4843 (x : Key → ℝ) : Integer.Sparse.eval row4843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4843, Integer.Sparse.eval_collectBalanced, rawRowCheck4843]

theorem rawRowCheck4844 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4844 := by decide +kernel

theorem rowCheck4844 : row4844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4844 := by decide +kernel

theorem rowEval4844 (x : Key → ℝ) : Integer.Sparse.eval row4844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4844, Integer.Sparse.eval_collectBalanced, rawRowCheck4844]

theorem rawRowCheck4845 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4845 := by decide +kernel

theorem rowCheck4845 : row4845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4845 := by decide +kernel

theorem rowEval4845 (x : Key → ℝ) : Integer.Sparse.eval row4845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4845, Integer.Sparse.eval_collectBalanced, rawRowCheck4845]

theorem rawRowCheck4846 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4846 := by decide +kernel

theorem rowCheck4846 : row4846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4846 := by decide +kernel

theorem rowEval4846 (x : Key → ℝ) : Integer.Sparse.eval row4846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4846, Integer.Sparse.eval_collectBalanced, rawRowCheck4846]

theorem rawRowCheck4847 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4847 := by decide +kernel

theorem rowCheck4847 : row4847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4847 := by decide +kernel

theorem rowEval4847 (x : Key → ℝ) : Integer.Sparse.eval row4847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4847, Integer.Sparse.eval_collectBalanced, rawRowCheck4847]

theorem rawRowCheck4848 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4848 := by decide +kernel

theorem rowCheck4848 : row4848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4848 := by decide +kernel

theorem rowEval4848 (x : Key → ℝ) : Integer.Sparse.eval row4848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4848, Integer.Sparse.eval_collectBalanced, rawRowCheck4848]

theorem rawRowCheck4849 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4849 := by decide +kernel

theorem rowCheck4849 : row4849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4849 := by decide +kernel

theorem rowEval4849 (x : Key → ℝ) : Integer.Sparse.eval row4849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4849, Integer.Sparse.eval_collectBalanced, rawRowCheck4849]

theorem rawRowCheck4850 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4850 := by decide +kernel

theorem rowCheck4850 : row4850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4850 := by decide +kernel

theorem rowEval4850 (x : Key → ℝ) : Integer.Sparse.eval row4850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4850, Integer.Sparse.eval_collectBalanced, rawRowCheck4850]

theorem rawRowCheck4851 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4851 := by decide +kernel

theorem rowCheck4851 : row4851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4851 := by decide +kernel

theorem rowEval4851 (x : Key → ℝ) : Integer.Sparse.eval row4851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4851, Integer.Sparse.eval_collectBalanced, rawRowCheck4851]

theorem rawRowCheck4852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4852 := by decide +kernel

theorem rowCheck4852 : row4852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4852 := by decide +kernel

theorem rowEval4852 (x : Key → ℝ) : Integer.Sparse.eval row4852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4852, Integer.Sparse.eval_collectBalanced, rawRowCheck4852]

theorem rawRowCheck4853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4853 := by decide +kernel

theorem rowCheck4853 : row4853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4853 := by decide +kernel

theorem rowEval4853 (x : Key → ℝ) : Integer.Sparse.eval row4853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4853, Integer.Sparse.eval_collectBalanced, rawRowCheck4853]

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

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4570 x
  · exact rowEval4571 x
  · exact rowEval4572 x
  · exact rowEval4573 x
  · exact rowEval4574 x
  · exact rowEval4575 x
  · exact rowEval4576 x
  · exact rowEval4577 x
  · exact rowEval4578 x
  · exact rowEval4579 x
  · exact rowEval4580 x
  · exact rowEval4581 x
  · exact rowEval4582 x
  · exact rowEval4583 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

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

theorem rawRowCheck1494 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1494 := by decide +kernel

theorem rowCheck1494 : row1494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1494 := by decide +kernel

theorem rowEval1494 (x : Key → ℝ) : Integer.Sparse.eval row1494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1494, Integer.Sparse.eval_collectBalanced, rawRowCheck1494]

theorem rawRowCheck1495 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1495 := by decide +kernel

theorem rowCheck1495 : row1495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1495 := by decide +kernel

theorem rowEval1495 (x : Key → ℝ) : Integer.Sparse.eval row1495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1495, Integer.Sparse.eval_collectBalanced, rawRowCheck1495]

theorem rawRowCheck1496 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1496 := by decide +kernel

theorem rowCheck1496 : row1496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1496 := by decide +kernel

theorem rowEval1496 (x : Key → ℝ) : Integer.Sparse.eval row1496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1496, Integer.Sparse.eval_collectBalanced, rawRowCheck1496]

theorem rawRowCheck1503 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1 = rawRow1503 := by decide +kernel

theorem rowCheck1503 : row1503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1503 := by decide +kernel

theorem rowEval1503 (x : Key → ℝ) : Integer.Sparse.eval row1503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1503, Integer.Sparse.eval_collectBalanced, rawRowCheck1503]

theorem rawRowCheck1504 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1 = rawRow1504 := by decide +kernel

theorem rowCheck1504 : row1504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1504 := by decide +kernel

theorem rowEval1504 (x : Key → ℝ) : Integer.Sparse.eval row1504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1504, Integer.Sparse.eval_collectBalanced, rawRowCheck1504]

theorem rawRowCheck1505 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1 = rawRow1505 := by decide +kernel

theorem rowCheck1505 : row1505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1505 := by decide +kernel

theorem rowEval1505 (x : Key → ℝ) : Integer.Sparse.eval row1505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1505, Integer.Sparse.eval_collectBalanced, rawRowCheck1505]

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

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4842 x
  · exact rowEval4843 x
  · exact rowEval4844 x
  · exact rowEval1494 x
  · exact rowEval1495 x
  · exact rowEval1496 x
  · exact rowEval4845 x
  · exact rowEval4846 x
  · exact rowEval4847 x
  · exact rowEval4848 x
  · exact rowEval4849 x
  · exact rowEval4850 x
  · exact rowEval1503 x
  · exact rowEval1504 x
  · exact rowEval1505 x
  · exact rowEval4851 x
  · exact rowEval4852 x
  · exact rowEval4853 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck800 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1 = rawRow800 := by decide +kernel

theorem rowCheck800 : row800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow800 := by decide +kernel

theorem rowEval800 (x : Key → ℝ) : Integer.Sparse.eval row800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck800, Integer.Sparse.eval_collectBalanced, rawRowCheck800]

theorem rawRowCheck801 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1 = rawRow801 := by decide +kernel

theorem rowCheck801 : row801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow801 := by decide +kernel

theorem rowEval801 (x : Key → ℝ) : Integer.Sparse.eval row801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck801, Integer.Sparse.eval_collectBalanced, rawRowCheck801]

theorem rawRowCheck802 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow802 := by decide +kernel

theorem rowCheck802 : row802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow802 := by decide +kernel

theorem rowEval802 (x : Key → ℝ) : Integer.Sparse.eval row802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck802, Integer.Sparse.eval_collectBalanced, rawRowCheck802]

theorem rawRowCheck803 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow803 := by decide +kernel

theorem rowCheck803 : row803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow803 := by decide +kernel

theorem rowEval803 (x : Key → ℝ) : Integer.Sparse.eval row803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck803, Integer.Sparse.eval_collectBalanced, rawRowCheck803]

theorem rawRowCheck804 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow804 := by decide +kernel

theorem rowCheck804 : row804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow804 := by decide +kernel

theorem rowEval804 (x : Key → ℝ) : Integer.Sparse.eval row804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck804, Integer.Sparse.eval_collectBalanced, rawRowCheck804]

theorem rawRowCheck805 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow805 := by decide +kernel

theorem rowCheck805 : row805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow805 := by decide +kernel

theorem rowEval805 (x : Key → ℝ) : Integer.Sparse.eval row805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck805, Integer.Sparse.eval_collectBalanced, rawRowCheck805]

end MUB6.Certificate.GramRows

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval792 x
  · exact rowEval793 x
  · exact rowEval794 x
  · exact rowEval795 x
  · exact rowEval796 x
  · exact rowEval797 x
  · exact rowEval798 x
  · exact rowEval799 x
  · exact rowEval800 x
  · exact rowEval801 x
  · exact rowEval802 x
  · exact rowEval803 x
  · exact rowEval804 x
  · exact rowEval805 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck940 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1 = rawRow940 := by decide +kernel

theorem rowCheck940 : row940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow940 := by decide +kernel

theorem rowEval940 (x : Key → ℝ) : Integer.Sparse.eval row940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck940, Integer.Sparse.eval_collectBalanced, rawRowCheck940]

theorem rawRowCheck941 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1 = rawRow941 := by decide +kernel

theorem rowCheck941 : row941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow941 := by decide +kernel

theorem rowEval941 (x : Key → ℝ) : Integer.Sparse.eval row941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck941, Integer.Sparse.eval_collectBalanced, rawRowCheck941]

theorem rawRowCheck942 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1 = rawRow942 := by decide +kernel

theorem rowCheck942 : row942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow942 := by decide +kernel

theorem rowEval942 (x : Key → ℝ) : Integer.Sparse.eval row942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck942, Integer.Sparse.eval_collectBalanced, rawRowCheck942]

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

theorem rawRowCheck949 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1 = rawRow949 := by decide +kernel

theorem rowCheck949 : row949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow949 := by decide +kernel

theorem rowEval949 (x : Key → ℝ) : Integer.Sparse.eval row949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck949, Integer.Sparse.eval_collectBalanced, rawRowCheck949]

theorem rawRowCheck950 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1 = rawRow950 := by decide +kernel

theorem rowCheck950 : row950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow950 := by decide +kernel

theorem rowEval950 (x : Key → ℝ) : Integer.Sparse.eval row950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck950, Integer.Sparse.eval_collectBalanced, rawRowCheck950]

theorem rawRowCheck951 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1 = rawRow951 := by decide +kernel

theorem rowCheck951 : row951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow951 := by decide +kernel

theorem rowEval951 (x : Key → ℝ) : Integer.Sparse.eval row951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck951, Integer.Sparse.eval_collectBalanced, rawRowCheck951]

theorem rawRowCheck952 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1 = rawRow952 := by decide +kernel

theorem rowCheck952 : row952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow952 := by decide +kernel

theorem rowEval952 (x : Key → ℝ) : Integer.Sparse.eval row952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck952, Integer.Sparse.eval_collectBalanced, rawRowCheck952]

theorem rawRowCheck953 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1 = rawRow953 := by decide +kernel

theorem rowCheck953 : row953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow953 := by decide +kernel

theorem rowEval953 (x : Key → ℝ) : Integer.Sparse.eval row953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck953, Integer.Sparse.eval_collectBalanced, rawRowCheck953]

theorem rawRowCheck954 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1 = rawRow954 := by decide +kernel

theorem rowCheck954 : row954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow954 := by decide +kernel

theorem rowEval954 (x : Key → ℝ) : Integer.Sparse.eval row954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck954, Integer.Sparse.eval_collectBalanced, rawRowCheck954]

theorem rawRowCheck955 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow955 := by decide +kernel

theorem rowCheck955 : row955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow955 := by decide +kernel

theorem rowEval955 (x : Key → ℝ) : Integer.Sparse.eval row955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck955, Integer.Sparse.eval_collectBalanced, rawRowCheck955]

theorem rawRowCheck956 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow956 := by decide +kernel

theorem rowCheck956 : row956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow956 := by decide +kernel

theorem rowEval956 (x : Key → ℝ) : Integer.Sparse.eval row956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck956, Integer.Sparse.eval_collectBalanced, rawRowCheck956]

theorem rawRowCheck957 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow957 := by decide +kernel

theorem rowCheck957 : row957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow957 := by decide +kernel

theorem rowEval957 (x : Key → ℝ) : Integer.Sparse.eval row957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck957, Integer.Sparse.eval_collectBalanced, rawRowCheck957]

theorem rawRowCheck958 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow958 := by decide +kernel

theorem rowCheck958 : row958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow958 := by decide +kernel

theorem rowEval958 (x : Key → ℝ) : Integer.Sparse.eval row958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck958, Integer.Sparse.eval_collectBalanced, rawRowCheck958]

theorem rawRowCheck959 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow959 := by decide +kernel

theorem rowCheck959 : row959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow959 := by decide +kernel

theorem rowEval959 (x : Key → ℝ) : Integer.Sparse.eval row959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck959, Integer.Sparse.eval_collectBalanced, rawRowCheck959]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck960 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow960 := by decide +kernel

theorem rowCheck960 : row960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow960 := by decide +kernel

theorem rowEval960 (x : Key → ℝ) : Integer.Sparse.eval row960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck960, Integer.Sparse.eval_collectBalanced, rawRowCheck960]

theorem rawRowCheck961 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow961 := by decide +kernel

theorem rowCheck961 : row961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow961 := by decide +kernel

theorem rowEval961 (x : Key → ℝ) : Integer.Sparse.eval row961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck961, Integer.Sparse.eval_collectBalanced, rawRowCheck961]

theorem rawRowCheck962 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow962 := by decide +kernel

theorem rowCheck962 : row962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow962 := by decide +kernel

theorem rowEval962 (x : Key → ℝ) : Integer.Sparse.eval row962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck962, Integer.Sparse.eval_collectBalanced, rawRowCheck962]

theorem rawRowCheck963 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow963 := by decide +kernel

theorem rowCheck963 : row963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow963 := by decide +kernel

theorem rowEval963 (x : Key → ℝ) : Integer.Sparse.eval row963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck963, Integer.Sparse.eval_collectBalanced, rawRowCheck963]

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

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval934 x
  · exact rowEval935 x
  · exact rowEval936 x
  · exact rowEval937 x
  · exact rowEval938 x
  · exact rowEval939 x
  · exact rowEval940 x
  · exact rowEval941 x
  · exact rowEval942 x
  · exact rowEval943 x
  · exact rowEval944 x
  · exact rowEval945 x
  · exact rowEval946 x
  · exact rowEval947 x
  · exact rowEval948 x
  · exact rowEval949 x
  · exact rowEval950 x
  · exact rowEval951 x
  · exact rowEval952 x
  · exact rowEval953 x
  · exact rowEval954 x
  · exact rowEval955 x
  · exact rowEval956 x
  · exact rowEval957 x
  · exact rowEval958 x
  · exact rowEval959 x
  · exact rowEval960 x
  · exact rowEval961 x
  · exact rowEval962 x
  · exact rowEval963 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1364 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1364 := by decide +kernel

theorem rowCheck1364 : row1364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1364 := by decide +kernel

theorem rowEval1364 (x : Key → ℝ) : Integer.Sparse.eval row1364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1364, Integer.Sparse.eval_collectBalanced, rawRowCheck1364]

theorem rawRowCheck1365 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1365 := by decide +kernel

theorem rowCheck1365 : row1365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1365 := by decide +kernel

theorem rowEval1365 (x : Key → ℝ) : Integer.Sparse.eval row1365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1365, Integer.Sparse.eval_collectBalanced, rawRowCheck1365]

theorem rawRowCheck1366 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1366 := by decide +kernel

theorem rowCheck1366 : row1366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1366 := by decide +kernel

theorem rowEval1366 (x : Key → ℝ) : Integer.Sparse.eval row1366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1366, Integer.Sparse.eval_collectBalanced, rawRowCheck1366]

theorem rawRowCheck1367 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1367 := by decide +kernel

theorem rowCheck1367 : row1367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1367 := by decide +kernel

theorem rowEval1367 (x : Key → ℝ) : Integer.Sparse.eval row1367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1367, Integer.Sparse.eval_collectBalanced, rawRowCheck1367]

theorem rawRowCheck1368 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1368 := by decide +kernel

theorem rowCheck1368 : row1368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1368 := by decide +kernel

theorem rowEval1368 (x : Key → ℝ) : Integer.Sparse.eval row1368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1368, Integer.Sparse.eval_collectBalanced, rawRowCheck1368]

theorem rawRowCheck1369 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1369 := by decide +kernel

theorem rowCheck1369 : row1369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1369 := by decide +kernel

theorem rowEval1369 (x : Key → ℝ) : Integer.Sparse.eval row1369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1369, Integer.Sparse.eval_collectBalanced, rawRowCheck1369]

theorem rawRowCheck1370 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1370 := by decide +kernel

theorem rowCheck1370 : row1370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1370 := by decide +kernel

theorem rowEval1370 (x : Key → ℝ) : Integer.Sparse.eval row1370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1370, Integer.Sparse.eval_collectBalanced, rawRowCheck1370]

theorem rawRowCheck1371 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1371 := by decide +kernel

theorem rowCheck1371 : row1371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1371 := by decide +kernel

theorem rowEval1371 (x : Key → ℝ) : Integer.Sparse.eval row1371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1371, Integer.Sparse.eval_collectBalanced, rawRowCheck1371]

theorem rawRowCheck1372 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1372 := by decide +kernel

theorem rowCheck1372 : row1372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1372 := by decide +kernel

theorem rowEval1372 (x : Key → ℝ) : Integer.Sparse.eval row1372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1372, Integer.Sparse.eval_collectBalanced, rawRowCheck1372]

theorem rawRowCheck1373 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1373 := by decide +kernel

theorem rowCheck1373 : row1373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1373 := by decide +kernel

theorem rowEval1373 (x : Key → ℝ) : Integer.Sparse.eval row1373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1373, Integer.Sparse.eval_collectBalanced, rawRowCheck1373]

theorem rawRowCheck1374 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1374 := by decide +kernel

theorem rowCheck1374 : row1374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1374 := by decide +kernel

theorem rowEval1374 (x : Key → ℝ) : Integer.Sparse.eval row1374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1374, Integer.Sparse.eval_collectBalanced, rawRowCheck1374]

theorem rawRowCheck1375 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1375 := by decide +kernel

theorem rowCheck1375 : row1375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1375 := by decide +kernel

theorem rowEval1375 (x : Key → ℝ) : Integer.Sparse.eval row1375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1375, Integer.Sparse.eval_collectBalanced, rawRowCheck1375]

theorem rawRowCheck1376 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1376 := by decide +kernel

theorem rowCheck1376 : row1376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1376 := by decide +kernel

theorem rowEval1376 (x : Key → ℝ) : Integer.Sparse.eval row1376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1376, Integer.Sparse.eval_collectBalanced, rawRowCheck1376]

theorem rawRowCheck1377 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1377 := by decide +kernel

theorem rowCheck1377 : row1377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1377 := by decide +kernel

theorem rowEval1377 (x : Key → ℝ) : Integer.Sparse.eval row1377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1377, Integer.Sparse.eval_collectBalanced, rawRowCheck1377]

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

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1364 x
  · exact rowEval1365 x
  · exact rowEval1366 x
  · exact rowEval1367 x
  · exact rowEval1368 x
  · exact rowEval1369 x
  · exact rowEval1370 x
  · exact rowEval1371 x
  · exact rowEval1372 x
  · exact rowEval1373 x
  · exact rowEval1374 x
  · exact rowEval1375 x
  · exact rowEval1376 x
  · exact rowEval1377 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

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

theorem entryEvalRow1_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 1).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval1_0 B hB
  · exact entryEval1_1 B hB
  · exact (entryEval2_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e_oai
