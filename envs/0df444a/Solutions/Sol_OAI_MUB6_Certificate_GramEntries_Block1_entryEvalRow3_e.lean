-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:49:00.934831+00:00
-- url     : https://prove2.me/submissions/2f945e02-6a3f-42c8-9646-2d22b0455120

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_3_e

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

theorem rawRowCheck1806 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1806 := by decide +kernel

theorem rowCheck1806 : row1806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1806 := by decide +kernel

theorem rowEval1806 (x : Key → ℝ) : Integer.Sparse.eval row1806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1806, Integer.Sparse.eval_collectBalanced, rawRowCheck1806]

theorem rawRowCheck1807 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1807 := by decide +kernel

theorem rowCheck1807 : row1807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1807 := by decide +kernel

theorem rowEval1807 (x : Key → ℝ) : Integer.Sparse.eval row1807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1807, Integer.Sparse.eval_collectBalanced, rawRowCheck1807]

theorem rawRowCheck1808 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1808 := by decide +kernel

theorem rowCheck1808 : row1808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1808 := by decide +kernel

theorem rowEval1808 (x : Key → ℝ) : Integer.Sparse.eval row1808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1808, Integer.Sparse.eval_collectBalanced, rawRowCheck1808]

theorem rawRowCheck1809 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1809 := by decide +kernel

theorem rowCheck1809 : row1809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1809 := by decide +kernel

theorem rowEval1809 (x : Key → ℝ) : Integer.Sparse.eval row1809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1809, Integer.Sparse.eval_collectBalanced, rawRowCheck1809]

theorem rawRowCheck1810 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3 = rawRow1810 := by decide +kernel

theorem rowCheck1810 : row1810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1810 := by decide +kernel

theorem rowEval1810 (x : Key → ℝ) : Integer.Sparse.eval row1810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1810, Integer.Sparse.eval_collectBalanced, rawRowCheck1810]

theorem rawRowCheck1811 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3 = rawRow1811 := by decide +kernel

theorem rowCheck1811 : row1811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1811 := by decide +kernel

theorem rowEval1811 (x : Key → ℝ) : Integer.Sparse.eval row1811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1811, Integer.Sparse.eval_collectBalanced, rawRowCheck1811]

theorem rawRowCheck1812 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3 = rawRow1812 := by decide +kernel

theorem rowCheck1812 : row1812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1812 := by decide +kernel

theorem rowEval1812 (x : Key → ℝ) : Integer.Sparse.eval row1812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1812, Integer.Sparse.eval_collectBalanced, rawRowCheck1812]

theorem rawRowCheck1813 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1813 := by decide +kernel

theorem rowCheck1813 : row1813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1813 := by decide +kernel

theorem rowEval1813 (x : Key → ℝ) : Integer.Sparse.eval row1813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1813, Integer.Sparse.eval_collectBalanced, rawRowCheck1813]

theorem rawRowCheck1814 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1814 := by decide +kernel

theorem rowCheck1814 : row1814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1814 := by decide +kernel

theorem rowEval1814 (x : Key → ℝ) : Integer.Sparse.eval row1814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1814, Integer.Sparse.eval_collectBalanced, rawRowCheck1814]

theorem rawRowCheck1815 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1815 := by decide +kernel

theorem rowCheck1815 : row1815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1815 := by decide +kernel

theorem rowEval1815 (x : Key → ℝ) : Integer.Sparse.eval row1815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1815, Integer.Sparse.eval_collectBalanced, rawRowCheck1815]

theorem rawRowCheck1816 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1816 := by decide +kernel

theorem rowCheck1816 : row1816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1816 := by decide +kernel

theorem rowEval1816 (x : Key → ℝ) : Integer.Sparse.eval row1816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1816, Integer.Sparse.eval_collectBalanced, rawRowCheck1816]

theorem rawRowCheck1817 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1817 := by decide +kernel

theorem rowCheck1817 : row1817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1817 := by decide +kernel

theorem rowEval1817 (x : Key → ℝ) : Integer.Sparse.eval row1817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1817, Integer.Sparse.eval_collectBalanced, rawRowCheck1817]

theorem rawRowCheck1818 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1818 := by decide +kernel

theorem rowCheck1818 : row1818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1818 := by decide +kernel

theorem rowEval1818 (x : Key → ℝ) : Integer.Sparse.eval row1818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1818, Integer.Sparse.eval_collectBalanced, rawRowCheck1818]

theorem rawRowCheck1819 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1819 := by decide +kernel

theorem rowCheck1819 : row1819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1819 := by decide +kernel

theorem rowEval1819 (x : Key → ℝ) : Integer.Sparse.eval row1819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1819, Integer.Sparse.eval_collectBalanced, rawRowCheck1819]

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

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1806 x
  · exact rowEval1807 x
  · exact rowEval1808 x
  · exact rowEval1809 x
  · exact rowEval1810 x
  · exact rowEval1811 x
  · exact rowEval1812 x
  · exact rowEval1813 x
  · exact rowEval1814 x
  · exact rowEval1815 x
  · exact rowEval1816 x
  · exact rowEval1817 x
  · exact rowEval1818 x
  · exact rowEval1819 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

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

theorem rawRowCheck1960 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1960 := by decide +kernel

theorem rowCheck1960 : row1960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1960 := by decide +kernel

theorem rowEval1960 (x : Key → ℝ) : Integer.Sparse.eval row1960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1960, Integer.Sparse.eval_collectBalanced, rawRowCheck1960]

theorem rawRowCheck1961 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1961 := by decide +kernel

theorem rowCheck1961 : row1961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1961 := by decide +kernel

theorem rowEval1961 (x : Key → ℝ) : Integer.Sparse.eval row1961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1961, Integer.Sparse.eval_collectBalanced, rawRowCheck1961]

theorem rawRowCheck1962 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1962 := by decide +kernel

theorem rowCheck1962 : row1962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1962 := by decide +kernel

theorem rowEval1962 (x : Key → ℝ) : Integer.Sparse.eval row1962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1962, Integer.Sparse.eval_collectBalanced, rawRowCheck1962]

theorem rawRowCheck1963 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1963 := by decide +kernel

theorem rowCheck1963 : row1963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1963 := by decide +kernel

theorem rowEval1963 (x : Key → ℝ) : Integer.Sparse.eval row1963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1963, Integer.Sparse.eval_collectBalanced, rawRowCheck1963]

theorem rawRowCheck1964 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1964 := by decide +kernel

theorem rowCheck1964 : row1964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1964 := by decide +kernel

theorem rowEval1964 (x : Key → ℝ) : Integer.Sparse.eval row1964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1964, Integer.Sparse.eval_collectBalanced, rawRowCheck1964]

theorem rawRowCheck1965 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1965 := by decide +kernel

theorem rowCheck1965 : row1965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1965 := by decide +kernel

theorem rowEval1965 (x : Key → ℝ) : Integer.Sparse.eval row1965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1965, Integer.Sparse.eval_collectBalanced, rawRowCheck1965]

theorem rawRowCheck1966 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1966 := by decide +kernel

theorem rowCheck1966 : row1966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1966 := by decide +kernel

theorem rowEval1966 (x : Key → ℝ) : Integer.Sparse.eval row1966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1966, Integer.Sparse.eval_collectBalanced, rawRowCheck1966]

theorem rawRowCheck1967 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1967 := by decide +kernel

theorem rowCheck1967 : row1967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1967 := by decide +kernel

theorem rowEval1967 (x : Key → ℝ) : Integer.Sparse.eval row1967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1967, Integer.Sparse.eval_collectBalanced, rawRowCheck1967]

theorem rawRowCheck1968 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1968 := by decide +kernel

theorem rowCheck1968 : row1968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1968 := by decide +kernel

theorem rowEval1968 (x : Key → ℝ) : Integer.Sparse.eval row1968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1968, Integer.Sparse.eval_collectBalanced, rawRowCheck1968]

theorem rawRowCheck1969 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1969 := by decide +kernel

theorem rowCheck1969 : row1969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1969 := by decide +kernel

theorem rowEval1969 (x : Key → ℝ) : Integer.Sparse.eval row1969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1969, Integer.Sparse.eval_collectBalanced, rawRowCheck1969]

theorem rawRowCheck1970 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1970 := by decide +kernel

theorem rowCheck1970 : row1970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1970 := by decide +kernel

theorem rowEval1970 (x : Key → ℝ) : Integer.Sparse.eval row1970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1970, Integer.Sparse.eval_collectBalanced, rawRowCheck1970]

theorem rawRowCheck1971 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1971 := by decide +kernel

theorem rowCheck1971 : row1971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1971 := by decide +kernel

theorem rowEval1971 (x : Key → ℝ) : Integer.Sparse.eval row1971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1971, Integer.Sparse.eval_collectBalanced, rawRowCheck1971]

theorem rawRowCheck1972 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1972 := by decide +kernel

theorem rowCheck1972 : row1972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1972 := by decide +kernel

theorem rowEval1972 (x : Key → ℝ) : Integer.Sparse.eval row1972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1972, Integer.Sparse.eval_collectBalanced, rawRowCheck1972]

theorem rawRowCheck1973 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1973 := by decide +kernel

theorem rowCheck1973 : row1973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1973 := by decide +kernel

theorem rowEval1973 (x : Key → ℝ) : Integer.Sparse.eval row1973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1973, Integer.Sparse.eval_collectBalanced, rawRowCheck1973]

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

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1960 x
  · exact rowEval1961 x
  · exact rowEval1962 x
  · exact rowEval1963 x
  · exact rowEval1964 x
  · exact rowEval1965 x
  · exact rowEval1966 x
  · exact rowEval1967 x
  · exact rowEval1968 x
  · exact rowEval1969 x
  · exact rowEval1970 x
  · exact rowEval1971 x
  · exact rowEval1972 x
  · exact rowEval1973 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

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

theorem rawRowCheck2176 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2176 := by decide +kernel

theorem rowCheck2176 : row2176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2176 := by decide +kernel

theorem rowEval2176 (x : Key → ℝ) : Integer.Sparse.eval row2176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2176, Integer.Sparse.eval_collectBalanced, rawRowCheck2176]

theorem rawRowCheck2177 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2177 := by decide +kernel

theorem rowCheck2177 : row2177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2177 := by decide +kernel

theorem rowEval2177 (x : Key → ℝ) : Integer.Sparse.eval row2177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2177, Integer.Sparse.eval_collectBalanced, rawRowCheck2177]

theorem rawRowCheck2178 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2178 := by decide +kernel

theorem rowCheck2178 : row2178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2178 := by decide +kernel

theorem rowEval2178 (x : Key → ℝ) : Integer.Sparse.eval row2178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2178, Integer.Sparse.eval_collectBalanced, rawRowCheck2178]

theorem rawRowCheck2185 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2185 := by decide +kernel

theorem rowCheck2185 : row2185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2185 := by decide +kernel

theorem rowEval2185 (x : Key → ℝ) : Integer.Sparse.eval row2185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2185, Integer.Sparse.eval_collectBalanced, rawRowCheck2185]

theorem rawRowCheck2186 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2186 := by decide +kernel

theorem rowCheck2186 : row2186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2186 := by decide +kernel

theorem rowEval2186 (x : Key → ℝ) : Integer.Sparse.eval row2186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2186, Integer.Sparse.eval_collectBalanced, rawRowCheck2186]

theorem rawRowCheck2187 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2187 := by decide +kernel

theorem rowCheck2187 : row2187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2187 := by decide +kernel

theorem rowEval2187 (x : Key → ℝ) : Integer.Sparse.eval row2187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2187, Integer.Sparse.eval_collectBalanced, rawRowCheck2187]

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

theorem rawRowCheck2518 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2518 := by decide +kernel

theorem rowCheck2518 : row2518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2518 := by decide +kernel

theorem rowEval2518 (x : Key → ℝ) : Integer.Sparse.eval row2518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2518, Integer.Sparse.eval_collectBalanced, rawRowCheck2518]

theorem rawRowCheck2519 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2519 := by decide +kernel

theorem rowCheck2519 : row2519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2519 := by decide +kernel

theorem rowEval2519 (x : Key → ℝ) : Integer.Sparse.eval row2519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2519, Integer.Sparse.eval_collectBalanced, rawRowCheck2519]

theorem rawRowCheck2520 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2520 := by decide +kernel

theorem rowCheck2520 : row2520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2520 := by decide +kernel

theorem rowEval2520 (x : Key → ℝ) : Integer.Sparse.eval row2520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2520, Integer.Sparse.eval_collectBalanced, rawRowCheck2520]

theorem rawRowCheck2521 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2521 := by decide +kernel

theorem rowCheck2521 : row2521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2521 := by decide +kernel

theorem rowEval2521 (x : Key → ℝ) : Integer.Sparse.eval row2521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2521, Integer.Sparse.eval_collectBalanced, rawRowCheck2521]

theorem rawRowCheck2522 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2522 := by decide +kernel

theorem rowCheck2522 : row2522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2522 := by decide +kernel

theorem rowEval2522 (x : Key → ℝ) : Integer.Sparse.eval row2522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2522, Integer.Sparse.eval_collectBalanced, rawRowCheck2522]

theorem rawRowCheck2523 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2523 := by decide +kernel

theorem rowCheck2523 : row2523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2523 := by decide +kernel

theorem rowEval2523 (x : Key → ℝ) : Integer.Sparse.eval row2523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2523, Integer.Sparse.eval_collectBalanced, rawRowCheck2523]

theorem rawRowCheck2524 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2524 := by decide +kernel

theorem rowCheck2524 : row2524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2524 := by decide +kernel

theorem rowEval2524 (x : Key → ℝ) : Integer.Sparse.eval row2524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2524, Integer.Sparse.eval_collectBalanced, rawRowCheck2524]

theorem rawRowCheck2525 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2525 := by decide +kernel

theorem rowCheck2525 : row2525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2525 := by decide +kernel

theorem rowEval2525 (x : Key → ℝ) : Integer.Sparse.eval row2525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2525, Integer.Sparse.eval_collectBalanced, rawRowCheck2525]

theorem rawRowCheck2526 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2526 := by decide +kernel

theorem rowCheck2526 : row2526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2526 := by decide +kernel

theorem rowEval2526 (x : Key → ℝ) : Integer.Sparse.eval row2526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2526, Integer.Sparse.eval_collectBalanced, rawRowCheck2526]

theorem rawRowCheck2527 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2527 := by decide +kernel

theorem rowCheck2527 : row2527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2527 := by decide +kernel

theorem rowEval2527 (x : Key → ℝ) : Integer.Sparse.eval row2527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2527, Integer.Sparse.eval_collectBalanced, rawRowCheck2527]

theorem rawRowCheck2528 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2528 := by decide +kernel

theorem rowCheck2528 : row2528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2528 := by decide +kernel

theorem rowEval2528 (x : Key → ℝ) : Integer.Sparse.eval row2528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2528, Integer.Sparse.eval_collectBalanced, rawRowCheck2528]

theorem rawRowCheck2529 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2529 := by decide +kernel

theorem rowCheck2529 : row2529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2529 := by decide +kernel

theorem rowEval2529 (x : Key → ℝ) : Integer.Sparse.eval row2529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2529, Integer.Sparse.eval_collectBalanced, rawRowCheck2529]

theorem rawRowCheck2530 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2530 := by decide +kernel

theorem rowCheck2530 : row2530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2530 := by decide +kernel

theorem rowEval2530 (x : Key → ℝ) : Integer.Sparse.eval row2530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2530, Integer.Sparse.eval_collectBalanced, rawRowCheck2530]

theorem rawRowCheck2531 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2531 := by decide +kernel

theorem rowCheck2531 : row2531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2531 := by decide +kernel

theorem rowEval2531 (x : Key → ℝ) : Integer.Sparse.eval row2531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2531, Integer.Sparse.eval_collectBalanced, rawRowCheck2531]

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

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2518 x
  · exact rowEval2519 x
  · exact rowEval2520 x
  · exact rowEval2521 x
  · exact rowEval2522 x
  · exact rowEval2523 x
  · exact rowEval2524 x
  · exact rowEval2525 x
  · exact rowEval2526 x
  · exact rowEval2527 x
  · exact rowEval2528 x
  · exact rowEval2529 x
  · exact rowEval2530 x
  · exact rowEval2531 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

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

theorem rawRowCheck2744 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form3 = rawRow2744 := by decide +kernel

theorem rowCheck2744 : row2744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2744 := by decide +kernel

theorem rowEval2744 (x : Key → ℝ) : Integer.Sparse.eval row2744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2744, Integer.Sparse.eval_collectBalanced, rawRowCheck2744]

theorem rawRowCheck2745 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form3 = rawRow2745 := by decide +kernel

theorem rowCheck2745 : row2745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2745 := by decide +kernel

theorem rowEval2745 (x : Key → ℝ) : Integer.Sparse.eval row2745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2745, Integer.Sparse.eval_collectBalanced, rawRowCheck2745]

theorem rawRowCheck2746 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form3 = rawRow2746 := by decide +kernel

theorem rowCheck2746 : row2746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2746 := by decide +kernel

theorem rowEval2746 (x : Key → ℝ) : Integer.Sparse.eval row2746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2746, Integer.Sparse.eval_collectBalanced, rawRowCheck2746]

theorem rawRowCheck2747 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2747 := by decide +kernel

theorem rowCheck2747 : row2747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2747 := by decide +kernel

theorem rowEval2747 (x : Key → ℝ) : Integer.Sparse.eval row2747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2747, Integer.Sparse.eval_collectBalanced, rawRowCheck2747]

theorem rawRowCheck2748 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2748 := by decide +kernel

theorem rowCheck2748 : row2748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2748 := by decide +kernel

theorem rowEval2748 (x : Key → ℝ) : Integer.Sparse.eval row2748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2748, Integer.Sparse.eval_collectBalanced, rawRowCheck2748]

theorem rawRowCheck2749 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2749 := by decide +kernel

theorem rowCheck2749 : row2749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2749 := by decide +kernel

theorem rowEval2749 (x : Key → ℝ) : Integer.Sparse.eval row2749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2749, Integer.Sparse.eval_collectBalanced, rawRowCheck2749]

theorem rawRowCheck2750 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form3 = rawRow2750 := by decide +kernel

theorem rowCheck2750 : row2750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2750 := by decide +kernel

theorem rowEval2750 (x : Key → ℝ) : Integer.Sparse.eval row2750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2750, Integer.Sparse.eval_collectBalanced, rawRowCheck2750]

theorem rawRowCheck2751 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form3 = rawRow2751 := by decide +kernel

theorem rowCheck2751 : row2751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2751 := by decide +kernel

theorem rowEval2751 (x : Key → ℝ) : Integer.Sparse.eval row2751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2751, Integer.Sparse.eval_collectBalanced, rawRowCheck2751]

theorem rawRowCheck2752 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form3 = rawRow2752 := by decide +kernel

theorem rowCheck2752 : row2752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2752 := by decide +kernel

theorem rowEval2752 (x : Key → ℝ) : Integer.Sparse.eval row2752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2752, Integer.Sparse.eval_collectBalanced, rawRowCheck2752]

theorem rawRowCheck2753 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form3 = rawRow2753 := by decide +kernel

theorem rowCheck2753 : row2753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2753 := by decide +kernel

theorem rowEval2753 (x : Key → ℝ) : Integer.Sparse.eval row2753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2753, Integer.Sparse.eval_collectBalanced, rawRowCheck2753]

theorem rawRowCheck2754 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form3 = rawRow2754 := by decide +kernel

theorem rowCheck2754 : row2754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2754 := by decide +kernel

theorem rowEval2754 (x : Key → ℝ) : Integer.Sparse.eval row2754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2754, Integer.Sparse.eval_collectBalanced, rawRowCheck2754]

theorem rawRowCheck2755 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form3 = rawRow2755 := by decide +kernel

theorem rowCheck2755 : row2755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2755 := by decide +kernel

theorem rowEval2755 (x : Key → ℝ) : Integer.Sparse.eval row2755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2755, Integer.Sparse.eval_collectBalanced, rawRowCheck2755]

theorem rawRowCheck2756 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form3 = rawRow2756 := by decide +kernel

theorem rowCheck2756 : row2756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2756 := by decide +kernel

theorem rowEval2756 (x : Key → ℝ) : Integer.Sparse.eval row2756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2756, Integer.Sparse.eval_collectBalanced, rawRowCheck2756]

theorem rawRowCheck2757 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form3 = rawRow2757 := by decide +kernel

theorem rowCheck2757 : row2757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2757 := by decide +kernel

theorem rowEval2757 (x : Key → ℝ) : Integer.Sparse.eval row2757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2757, Integer.Sparse.eval_collectBalanced, rawRowCheck2757]

theorem rawRowCheck2758 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form3 = rawRow2758 := by decide +kernel

theorem rowCheck2758 : row2758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2758 := by decide +kernel

theorem rowEval2758 (x : Key → ℝ) : Integer.Sparse.eval row2758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2758, Integer.Sparse.eval_collectBalanced, rawRowCheck2758]

theorem rawRowCheck2759 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow2759 := by decide +kernel

theorem rowCheck2759 : row2759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2759 := by decide +kernel

theorem rowEval2759 (x : Key → ℝ) : Integer.Sparse.eval row2759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2759, Integer.Sparse.eval_collectBalanced, rawRowCheck2759]

theorem rawRowCheck2760 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow2760 := by decide +kernel

theorem rowCheck2760 : row2760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2760 := by decide +kernel

theorem rowEval2760 (x : Key → ℝ) : Integer.Sparse.eval row2760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2760, Integer.Sparse.eval_collectBalanced, rawRowCheck2760]

theorem rawRowCheck2761 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow2761 := by decide +kernel

theorem rowCheck2761 : row2761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2761 := by decide +kernel

theorem rowEval2761 (x : Key → ℝ) : Integer.Sparse.eval row2761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2761, Integer.Sparse.eval_collectBalanced, rawRowCheck2761]

theorem rawRowCheck2762 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form3 = rawRow2762 := by decide +kernel

theorem rowCheck2762 : row2762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2762 := by decide +kernel

theorem rowEval2762 (x : Key → ℝ) : Integer.Sparse.eval row2762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2762, Integer.Sparse.eval_collectBalanced, rawRowCheck2762]

theorem rawRowCheck2763 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form3 = rawRow2763 := by decide +kernel

theorem rowCheck2763 : row2763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2763 := by decide +kernel

theorem rowEval2763 (x : Key → ℝ) : Integer.Sparse.eval row2763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2763, Integer.Sparse.eval_collectBalanced, rawRowCheck2763]

theorem rawRowCheck2764 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form3 = rawRow2764 := by decide +kernel

theorem rowCheck2764 : row2764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2764 := by decide +kernel

theorem rowEval2764 (x : Key → ℝ) : Integer.Sparse.eval row2764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2764, Integer.Sparse.eval_collectBalanced, rawRowCheck2764]

theorem rawRowCheck2765 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form3 = rawRow2765 := by decide +kernel

theorem rowCheck2765 : row2765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2765 := by decide +kernel

theorem rowEval2765 (x : Key → ℝ) : Integer.Sparse.eval row2765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2765, Integer.Sparse.eval_collectBalanced, rawRowCheck2765]

theorem rawRowCheck2766 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form3 = rawRow2766 := by decide +kernel

theorem rowCheck2766 : row2766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2766 := by decide +kernel

theorem rowEval2766 (x : Key → ℝ) : Integer.Sparse.eval row2766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2766, Integer.Sparse.eval_collectBalanced, rawRowCheck2766]

theorem rawRowCheck2767 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form3 = rawRow2767 := by decide +kernel

theorem rowCheck2767 : row2767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2767 := by decide +kernel

theorem rowEval2767 (x : Key → ℝ) : Integer.Sparse.eval row2767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck2767, Integer.Sparse.eval_collectBalanced, rawRowCheck2767]

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

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2744 x
  · exact rowEval2745 x
  · exact rowEval2746 x
  · exact rowEval2747 x
  · exact rowEval2748 x
  · exact rowEval2749 x
  · exact rowEval2750 x
  · exact rowEval2751 x
  · exact rowEval2752 x
  · exact rowEval2753 x
  · exact rowEval2754 x
  · exact rowEval2755 x
  · exact rowEval2756 x
  · exact rowEval2757 x
  · exact rowEval2758 x
  · exact rowEval2759 x
  · exact rowEval2760 x
  · exact rowEval2761 x
  · exact rowEval2762 x
  · exact rowEval2763 x
  · exact rowEval2764 x
  · exact rowEval2765 x
  · exact rowEval2766 x
  · exact rowEval2767 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

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

theorem rawRowCheck778 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow778 := by decide +kernel

theorem rowCheck778 : row778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow778 := by decide +kernel

theorem rowEval778 (x : Key → ℝ) : Integer.Sparse.eval row778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck778, Integer.Sparse.eval_collectBalanced, rawRowCheck778]

theorem rawRowCheck779 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow779 := by decide +kernel

theorem rowCheck779 : row779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow779 := by decide +kernel

theorem rowEval779 (x : Key → ℝ) : Integer.Sparse.eval row779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck779, Integer.Sparse.eval_collectBalanced, rawRowCheck779]

theorem rawRowCheck780 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow780 := by decide +kernel

theorem rowCheck780 : row780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow780 := by decide +kernel

theorem rowEval780 (x : Key → ℝ) : Integer.Sparse.eval row780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck780, Integer.Sparse.eval_collectBalanced, rawRowCheck780]

theorem rawRowCheck781 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow781 := by decide +kernel

theorem rowCheck781 : row781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow781 := by decide +kernel

theorem rowEval781 (x : Key → ℝ) : Integer.Sparse.eval row781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck781, Integer.Sparse.eval_collectBalanced, rawRowCheck781]

theorem rawRowCheck782 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0 = rawRow782 := by decide +kernel

theorem rowCheck782 : row782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow782 := by decide +kernel

theorem rowEval782 (x : Key → ℝ) : Integer.Sparse.eval row782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck782, Integer.Sparse.eval_collectBalanced, rawRowCheck782]

theorem rawRowCheck783 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0 = rawRow783 := by decide +kernel

theorem rowCheck783 : row783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow783 := by decide +kernel

theorem rowEval783 (x : Key → ℝ) : Integer.Sparse.eval row783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck783, Integer.Sparse.eval_collectBalanced, rawRowCheck783]

theorem rawRowCheck784 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0 = rawRow784 := by decide +kernel

theorem rowCheck784 : row784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow784 := by decide +kernel

theorem rowEval784 (x : Key → ℝ) : Integer.Sparse.eval row784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck784, Integer.Sparse.eval_collectBalanced, rawRowCheck784]

theorem rawRowCheck785 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0 = rawRow785 := by decide +kernel

theorem rowCheck785 : row785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow785 := by decide +kernel

theorem rowEval785 (x : Key → ℝ) : Integer.Sparse.eval row785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck785, Integer.Sparse.eval_collectBalanced, rawRowCheck785]

theorem rawRowCheck786 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0 = rawRow786 := by decide +kernel

theorem rowCheck786 : row786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow786 := by decide +kernel

theorem rowEval786 (x : Key → ℝ) : Integer.Sparse.eval row786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck786, Integer.Sparse.eval_collectBalanced, rawRowCheck786]

theorem rawRowCheck787 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0 = rawRow787 := by decide +kernel

theorem rowCheck787 : row787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow787 := by decide +kernel

theorem rowEval787 (x : Key → ℝ) : Integer.Sparse.eval row787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck787, Integer.Sparse.eval_collectBalanced, rawRowCheck787]

theorem rawRowCheck788 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow788 := by decide +kernel

theorem rowCheck788 : row788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow788 := by decide +kernel

theorem rowEval788 (x : Key → ℝ) : Integer.Sparse.eval row788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck788, Integer.Sparse.eval_collectBalanced, rawRowCheck788]

theorem rawRowCheck789 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow789 := by decide +kernel

theorem rowCheck789 : row789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow789 := by decide +kernel

theorem rowEval789 (x : Key → ℝ) : Integer.Sparse.eval row789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck789, Integer.Sparse.eval_collectBalanced, rawRowCheck789]

theorem rawRowCheck790 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow790 := by decide +kernel

theorem rowCheck790 : row790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow790 := by decide +kernel

theorem rowEval790 (x : Key → ℝ) : Integer.Sparse.eval row790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck790, Integer.Sparse.eval_collectBalanced, rawRowCheck790]

theorem rawRowCheck791 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow791 := by decide +kernel

theorem rowCheck791 : row791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow791 := by decide +kernel

theorem rowEval791 (x : Key → ℝ) : Integer.Sparse.eval row791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck791, Integer.Sparse.eval_collectBalanced, rawRowCheck791]

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

theorem rawRowCheck3512 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form3 = rawRow3512 := by decide +kernel

theorem rowCheck3512 : row3512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3512 := by decide +kernel

theorem rowEval3512 (x : Key → ℝ) : Integer.Sparse.eval row3512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3512, Integer.Sparse.eval_collectBalanced, rawRowCheck3512]

theorem rawRowCheck3513 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form3 = rawRow3513 := by decide +kernel

theorem rowCheck3513 : row3513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3513 := by decide +kernel

theorem rowEval3513 (x : Key → ℝ) : Integer.Sparse.eval row3513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3513, Integer.Sparse.eval_collectBalanced, rawRowCheck3513]

theorem rawRowCheck3514 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form3 = rawRow3514 := by decide +kernel

theorem rowCheck3514 : row3514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3514 := by decide +kernel

theorem rowEval3514 (x : Key → ℝ) : Integer.Sparse.eval row3514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3514, Integer.Sparse.eval_collectBalanced, rawRowCheck3514]

theorem rawRowCheck3515 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3515 := by decide +kernel

theorem rowCheck3515 : row3515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3515 := by decide +kernel

theorem rowEval3515 (x : Key → ℝ) : Integer.Sparse.eval row3515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3515, Integer.Sparse.eval_collectBalanced, rawRowCheck3515]

theorem rawRowCheck3516 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3516 := by decide +kernel

theorem rowCheck3516 : row3516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3516 := by decide +kernel

theorem rowEval3516 (x : Key → ℝ) : Integer.Sparse.eval row3516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3516, Integer.Sparse.eval_collectBalanced, rawRowCheck3516]

theorem rawRowCheck3517 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3517 := by decide +kernel

theorem rowCheck3517 : row3517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3517 := by decide +kernel

theorem rowEval3517 (x : Key → ℝ) : Integer.Sparse.eval row3517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3517, Integer.Sparse.eval_collectBalanced, rawRowCheck3517]

theorem rawRowCheck3518 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow3518 := by decide +kernel

theorem rowCheck3518 : row3518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3518 := by decide +kernel

theorem rowEval3518 (x : Key → ℝ) : Integer.Sparse.eval row3518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3518, Integer.Sparse.eval_collectBalanced, rawRowCheck3518]

theorem rawRowCheck3519 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow3519 := by decide +kernel

theorem rowCheck3519 : row3519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3519 := by decide +kernel

theorem rowEval3519 (x : Key → ℝ) : Integer.Sparse.eval row3519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3519, Integer.Sparse.eval_collectBalanced, rawRowCheck3519]

theorem rawRowCheck3520 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow3520 := by decide +kernel

theorem rowCheck3520 : row3520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3520 := by decide +kernel

theorem rowEval3520 (x : Key → ℝ) : Integer.Sparse.eval row3520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3520, Integer.Sparse.eval_collectBalanced, rawRowCheck3520]

theorem rawRowCheck3521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3521 := by decide +kernel

theorem rowCheck3521 : row3521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3521 := by decide +kernel

theorem rowEval3521 (x : Key → ℝ) : Integer.Sparse.eval row3521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3521, Integer.Sparse.eval_collectBalanced, rawRowCheck3521]

theorem rawRowCheck3522 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3522 := by decide +kernel

theorem rowCheck3522 : row3522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3522 := by decide +kernel

theorem rowEval3522 (x : Key → ℝ) : Integer.Sparse.eval row3522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3522, Integer.Sparse.eval_collectBalanced, rawRowCheck3522]

theorem rawRowCheck3523 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3523 := by decide +kernel

theorem rowCheck3523 : row3523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3523 := by decide +kernel

theorem rowEval3523 (x : Key → ℝ) : Integer.Sparse.eval row3523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3523, Integer.Sparse.eval_collectBalanced, rawRowCheck3523]

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

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2176 x
  · exact rowEval2177 x
  · exact rowEval2178 x
  · exact rowEval3512 x
  · exact rowEval3513 x
  · exact rowEval3514 x
  · exact rowEval2185 x
  · exact rowEval2186 x
  · exact rowEval2187 x
  · exact rowEval3515 x
  · exact rowEval3516 x
  · exact rowEval3517 x
  · exact rowEval3518 x
  · exact rowEval3519 x
  · exact rowEval3520 x
  · exact rowEval3521 x
  · exact rowEval3522 x
  · exact rowEval3523 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

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

theorem rawRowCheck3794 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3794 := by decide +kernel

theorem rowCheck3794 : row3794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3794 := by decide +kernel

theorem rowEval3794 (x : Key → ℝ) : Integer.Sparse.eval row3794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3794, Integer.Sparse.eval_collectBalanced, rawRowCheck3794]

theorem rawRowCheck3795 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3795 := by decide +kernel

theorem rowCheck3795 : row3795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3795 := by decide +kernel

theorem rowEval3795 (x : Key → ℝ) : Integer.Sparse.eval row3795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3795, Integer.Sparse.eval_collectBalanced, rawRowCheck3795]

theorem rawRowCheck3796 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3796 := by decide +kernel

theorem rowCheck3796 : row3796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3796 := by decide +kernel

theorem rowEval3796 (x : Key → ℝ) : Integer.Sparse.eval row3796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3796, Integer.Sparse.eval_collectBalanced, rawRowCheck3796]

theorem rawRowCheck3797 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3797 := by decide +kernel

theorem rowCheck3797 : row3797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3797 := by decide +kernel

theorem rowEval3797 (x : Key → ℝ) : Integer.Sparse.eval row3797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3797, Integer.Sparse.eval_collectBalanced, rawRowCheck3797]

theorem rawRowCheck3798 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3798 := by decide +kernel

theorem rowCheck3798 : row3798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3798 := by decide +kernel

theorem rowEval3798 (x : Key → ℝ) : Integer.Sparse.eval row3798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3798, Integer.Sparse.eval_collectBalanced, rawRowCheck3798]

theorem rawRowCheck3799 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3799 := by decide +kernel

theorem rowCheck3799 : row3799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3799 := by decide +kernel

theorem rowEval3799 (x : Key → ℝ) : Integer.Sparse.eval row3799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3799, Integer.Sparse.eval_collectBalanced, rawRowCheck3799]

theorem rawRowCheck3800 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3800 := by decide +kernel

theorem rowCheck3800 : row3800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3800 := by decide +kernel

theorem rowEval3800 (x : Key → ℝ) : Integer.Sparse.eval row3800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3800, Integer.Sparse.eval_collectBalanced, rawRowCheck3800]

theorem rawRowCheck3801 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3801 := by decide +kernel

theorem rowCheck3801 : row3801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3801 := by decide +kernel

theorem rowEval3801 (x : Key → ℝ) : Integer.Sparse.eval row3801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3801, Integer.Sparse.eval_collectBalanced, rawRowCheck3801]

theorem rawRowCheck3802 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3802 := by decide +kernel

theorem rowCheck3802 : row3802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3802 := by decide +kernel

theorem rowEval3802 (x : Key → ℝ) : Integer.Sparse.eval row3802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3802, Integer.Sparse.eval_collectBalanced, rawRowCheck3802]

theorem rawRowCheck3803 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3803 := by decide +kernel

theorem rowCheck3803 : row3803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3803 := by decide +kernel

theorem rowEval3803 (x : Key → ℝ) : Integer.Sparse.eval row3803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3803, Integer.Sparse.eval_collectBalanced, rawRowCheck3803]

theorem rawRowCheck3804 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3804 := by decide +kernel

theorem rowCheck3804 : row3804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3804 := by decide +kernel

theorem rowEval3804 (x : Key → ℝ) : Integer.Sparse.eval row3804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3804, Integer.Sparse.eval_collectBalanced, rawRowCheck3804]

theorem rawRowCheck3805 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3805 := by decide +kernel

theorem rowCheck3805 : row3805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3805 := by decide +kernel

theorem rowEval3805 (x : Key → ℝ) : Integer.Sparse.eval row3805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3805, Integer.Sparse.eval_collectBalanced, rawRowCheck3805]

theorem rawRowCheck3806 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3806 := by decide +kernel

theorem rowCheck3806 : row3806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3806 := by decide +kernel

theorem rowEval3806 (x : Key → ℝ) : Integer.Sparse.eval row3806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3806, Integer.Sparse.eval_collectBalanced, rawRowCheck3806]

theorem rawRowCheck3807 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3807 := by decide +kernel

theorem rowCheck3807 : row3807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3807 := by decide +kernel

theorem rowEval3807 (x : Key → ℝ) : Integer.Sparse.eval row3807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3807, Integer.Sparse.eval_collectBalanced, rawRowCheck3807]

theorem rawRowCheck3808 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3808 := by decide +kernel

theorem rowCheck3808 : row3808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3808 := by decide +kernel

theorem rowEval3808 (x : Key → ℝ) : Integer.Sparse.eval row3808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3808, Integer.Sparse.eval_collectBalanced, rawRowCheck3808]

theorem rawRowCheck3809 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3809 := by decide +kernel

theorem rowCheck3809 : row3809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3809 := by decide +kernel

theorem rowEval3809 (x : Key → ℝ) : Integer.Sparse.eval row3809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3809, Integer.Sparse.eval_collectBalanced, rawRowCheck3809]

theorem rawRowCheck3810 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3810 := by decide +kernel

theorem rowCheck3810 : row3810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3810 := by decide +kernel

theorem rowEval3810 (x : Key → ℝ) : Integer.Sparse.eval row3810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3810, Integer.Sparse.eval_collectBalanced, rawRowCheck3810]

theorem rawRowCheck3811 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3811 := by decide +kernel

theorem rowCheck3811 : row3811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3811 := by decide +kernel

theorem rowEval3811 (x : Key → ℝ) : Integer.Sparse.eval row3811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3811, Integer.Sparse.eval_collectBalanced, rawRowCheck3811]

theorem rawRowCheck3812 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3812 := by decide +kernel

theorem rowCheck3812 : row3812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3812 := by decide +kernel

theorem rowEval3812 (x : Key → ℝ) : Integer.Sparse.eval row3812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3812, Integer.Sparse.eval_collectBalanced, rawRowCheck3812]

theorem rawRowCheck3813 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3813 := by decide +kernel

theorem rowCheck3813 : row3813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3813 := by decide +kernel

theorem rowEval3813 (x : Key → ℝ) : Integer.Sparse.eval row3813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3813, Integer.Sparse.eval_collectBalanced, rawRowCheck3813]

theorem rawRowCheck3814 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3814 := by decide +kernel

theorem rowCheck3814 : row3814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3814 := by decide +kernel

theorem rowEval3814 (x : Key → ℝ) : Integer.Sparse.eval row3814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3814, Integer.Sparse.eval_collectBalanced, rawRowCheck3814]

theorem rawRowCheck3815 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3815 := by decide +kernel

theorem rowCheck3815 : row3815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3815 := by decide +kernel

theorem rowEval3815 (x : Key → ℝ) : Integer.Sparse.eval row3815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3815, Integer.Sparse.eval_collectBalanced, rawRowCheck3815]

theorem rawRowCheck3816 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3816 := by decide +kernel

theorem rowCheck3816 : row3816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3816 := by decide +kernel

theorem rowEval3816 (x : Key → ℝ) : Integer.Sparse.eval row3816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3816, Integer.Sparse.eval_collectBalanced, rawRowCheck3816]

theorem rawRowCheck3817 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3817 := by decide +kernel

theorem rowCheck3817 : row3817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3817 := by decide +kernel

theorem rowEval3817 (x : Key → ℝ) : Integer.Sparse.eval row3817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3817, Integer.Sparse.eval_collectBalanced, rawRowCheck3817]

theorem rawRowCheck3818 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3818 := by decide +kernel

theorem rowCheck3818 : row3818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3818 := by decide +kernel

theorem rowEval3818 (x : Key → ℝ) : Integer.Sparse.eval row3818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3818, Integer.Sparse.eval_collectBalanced, rawRowCheck3818]

theorem rawRowCheck3819 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3819 := by decide +kernel

theorem rowCheck3819 : row3819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3819 := by decide +kernel

theorem rowEval3819 (x : Key → ℝ) : Integer.Sparse.eval row3819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3819, Integer.Sparse.eval_collectBalanced, rawRowCheck3819]

theorem rawRowCheck3820 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3820 := by decide +kernel

theorem rowCheck3820 : row3820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3820 := by decide +kernel

theorem rowEval3820 (x : Key → ℝ) : Integer.Sparse.eval row3820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3820, Integer.Sparse.eval_collectBalanced, rawRowCheck3820]

theorem rawRowCheck3821 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3821 := by decide +kernel

theorem rowCheck3821 : row3821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3821 := by decide +kernel

theorem rowEval3821 (x : Key → ℝ) : Integer.Sparse.eval row3821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3821, Integer.Sparse.eval_collectBalanced, rawRowCheck3821]

theorem rawRowCheck3822 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3822 := by decide +kernel

theorem rowCheck3822 : row3822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3822 := by decide +kernel

theorem rowEval3822 (x : Key → ℝ) : Integer.Sparse.eval row3822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3822, Integer.Sparse.eval_collectBalanced, rawRowCheck3822]

theorem rawRowCheck3823 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3823 := by decide +kernel

theorem rowCheck3823 : row3823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3823 := by decide +kernel

theorem rowEval3823 (x : Key → ℝ) : Integer.Sparse.eval row3823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3823, Integer.Sparse.eval_collectBalanced, rawRowCheck3823]

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

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval3794 x
  · exact rowEval3795 x
  · exact rowEval3796 x
  · exact rowEval3797 x
  · exact rowEval3798 x
  · exact rowEval3799 x
  · exact rowEval3800 x
  · exact rowEval3801 x
  · exact rowEval3802 x
  · exact rowEval3803 x
  · exact rowEval3804 x
  · exact rowEval3805 x
  · exact rowEval3806 x
  · exact rowEval3807 x
  · exact rowEval3808 x
  · exact rowEval3809 x
  · exact rowEval3810 x
  · exact rowEval3811 x
  · exact rowEval3812 x
  · exact rowEval3813 x
  · exact rowEval3814 x
  · exact rowEval3815 x
  · exact rowEval3816 x
  · exact rowEval3817 x
  · exact rowEval3818 x
  · exact rowEval3819 x
  · exact rowEval3820 x
  · exact rowEval3821 x
  · exact rowEval3822 x
  · exact rowEval3823 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

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

theorem rawRowCheck4598 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4598 := by decide +kernel

theorem rowCheck4598 : row4598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4598 := by decide +kernel

theorem rowEval4598 (x : Key → ℝ) : Integer.Sparse.eval row4598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4598, Integer.Sparse.eval_collectBalanced, rawRowCheck4598]

theorem rawRowCheck4599 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4599 := by decide +kernel

theorem rowCheck4599 : row4599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4599 := by decide +kernel

theorem rowEval4599 (x : Key → ℝ) : Integer.Sparse.eval row4599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4599, Integer.Sparse.eval_collectBalanced, rawRowCheck4599]

theorem rawRowCheck4600 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4600 := by decide +kernel

theorem rowCheck4600 : row4600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4600 := by decide +kernel

theorem rowEval4600 (x : Key → ℝ) : Integer.Sparse.eval row4600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4600, Integer.Sparse.eval_collectBalanced, rawRowCheck4600]

theorem rawRowCheck4601 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4601 := by decide +kernel

theorem rowCheck4601 : row4601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4601 := by decide +kernel

theorem rowEval4601 (x : Key → ℝ) : Integer.Sparse.eval row4601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4601, Integer.Sparse.eval_collectBalanced, rawRowCheck4601]

theorem rawRowCheck4602 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4602 := by decide +kernel

theorem rowCheck4602 : row4602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4602 := by decide +kernel

theorem rowEval4602 (x : Key → ℝ) : Integer.Sparse.eval row4602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4602, Integer.Sparse.eval_collectBalanced, rawRowCheck4602]

theorem rawRowCheck4603 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4603 := by decide +kernel

theorem rowCheck4603 : row4603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4603 := by decide +kernel

theorem rowEval4603 (x : Key → ℝ) : Integer.Sparse.eval row4603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4603, Integer.Sparse.eval_collectBalanced, rawRowCheck4603]

theorem rawRowCheck4604 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4604 := by decide +kernel

theorem rowCheck4604 : row4604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4604 := by decide +kernel

theorem rowEval4604 (x : Key → ℝ) : Integer.Sparse.eval row4604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4604, Integer.Sparse.eval_collectBalanced, rawRowCheck4604]

theorem rawRowCheck4605 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4605 := by decide +kernel

theorem rowCheck4605 : row4605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4605 := by decide +kernel

theorem rowEval4605 (x : Key → ℝ) : Integer.Sparse.eval row4605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4605, Integer.Sparse.eval_collectBalanced, rawRowCheck4605]

theorem rawRowCheck4606 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4606 := by decide +kernel

theorem rowCheck4606 : row4606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4606 := by decide +kernel

theorem rowEval4606 (x : Key → ℝ) : Integer.Sparse.eval row4606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4606, Integer.Sparse.eval_collectBalanced, rawRowCheck4606]

theorem rawRowCheck4607 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4607 := by decide +kernel

theorem rowCheck4607 : row4607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4607 := by decide +kernel

theorem rowEval4607 (x : Key → ℝ) : Integer.Sparse.eval row4607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4607, Integer.Sparse.eval_collectBalanced, rawRowCheck4607]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck4608 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4608 := by decide +kernel

theorem rowCheck4608 : row4608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4608 := by decide +kernel

theorem rowEval4608 (x : Key → ℝ) : Integer.Sparse.eval row4608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4608, Integer.Sparse.eval_collectBalanced, rawRowCheck4608]

theorem rawRowCheck4609 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4609 := by decide +kernel

theorem rowCheck4609 : row4609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4609 := by decide +kernel

theorem rowEval4609 (x : Key → ℝ) : Integer.Sparse.eval row4609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4609, Integer.Sparse.eval_collectBalanced, rawRowCheck4609]

theorem rawRowCheck4610 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4610 := by decide +kernel

theorem rowCheck4610 : row4610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4610 := by decide +kernel

theorem rowEval4610 (x : Key → ℝ) : Integer.Sparse.eval row4610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4610, Integer.Sparse.eval_collectBalanced, rawRowCheck4610]

theorem rawRowCheck4611 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4611 := by decide +kernel

theorem rowCheck4611 : row4611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4611 := by decide +kernel

theorem rowEval4611 (x : Key → ℝ) : Integer.Sparse.eval row4611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4611, Integer.Sparse.eval_collectBalanced, rawRowCheck4611]

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

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4598 x
  · exact rowEval4599 x
  · exact rowEval4600 x
  · exact rowEval4601 x
  · exact rowEval4602 x
  · exact rowEval4603 x
  · exact rowEval4604 x
  · exact rowEval4605 x
  · exact rowEval4606 x
  · exact rowEval4607 x
  · exact rowEval4608 x
  · exact rowEval4609 x
  · exact rowEval4610 x
  · exact rowEval4611 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1554 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1554 := by decide +kernel

theorem rowCheck1554 : row1554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1554 := by decide +kernel

theorem rowEval1554 (x : Key → ℝ) : Integer.Sparse.eval row1554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1554, Integer.Sparse.eval_collectBalanced, rawRowCheck1554]

theorem rawRowCheck1555 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1555 := by decide +kernel

theorem rowCheck1555 : row1555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1555 := by decide +kernel

theorem rowEval1555 (x : Key → ℝ) : Integer.Sparse.eval row1555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1555, Integer.Sparse.eval_collectBalanced, rawRowCheck1555]

theorem rawRowCheck1556 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1556 := by decide +kernel

theorem rowCheck1556 : row1556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1556 := by decide +kernel

theorem rowEval1556 (x : Key → ℝ) : Integer.Sparse.eval row1556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1556, Integer.Sparse.eval_collectBalanced, rawRowCheck1556]

theorem rawRowCheck1563 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1563 := by decide +kernel

theorem rowCheck1563 : row1563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1563 := by decide +kernel

theorem rowEval1563 (x : Key → ℝ) : Integer.Sparse.eval row1563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1563, Integer.Sparse.eval_collectBalanced, rawRowCheck1563]

theorem rawRowCheck1564 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1564 := by decide +kernel

theorem rowCheck1564 : row1564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1564 := by decide +kernel

theorem rowEval1564 (x : Key → ℝ) : Integer.Sparse.eval row1564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1564, Integer.Sparse.eval_collectBalanced, rawRowCheck1564]

theorem rawRowCheck1565 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1565 := by decide +kernel

theorem rowCheck1565 : row1565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1565 := by decide +kernel

theorem rowEval1565 (x : Key → ℝ) : Integer.Sparse.eval row1565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1565, Integer.Sparse.eval_collectBalanced, rawRowCheck1565]

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

theorem rawRowCheck4866 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4866 := by decide +kernel

theorem rowCheck4866 : row4866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4866 := by decide +kernel

theorem rowEval4866 (x : Key → ℝ) : Integer.Sparse.eval row4866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4866, Integer.Sparse.eval_collectBalanced, rawRowCheck4866]

theorem rawRowCheck4867 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4867 := by decide +kernel

theorem rowCheck4867 : row4867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4867 := by decide +kernel

theorem rowEval4867 (x : Key → ℝ) : Integer.Sparse.eval row4867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4867, Integer.Sparse.eval_collectBalanced, rawRowCheck4867]

theorem rawRowCheck4868 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4868 := by decide +kernel

theorem rowCheck4868 : row4868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4868 := by decide +kernel

theorem rowEval4868 (x : Key → ℝ) : Integer.Sparse.eval row4868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4868, Integer.Sparse.eval_collectBalanced, rawRowCheck4868]

theorem rawRowCheck4869 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3 = rawRow4869 := by decide +kernel

theorem rowCheck4869 : row4869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4869 := by decide +kernel

theorem rowEval4869 (x : Key → ℝ) : Integer.Sparse.eval row4869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4869, Integer.Sparse.eval_collectBalanced, rawRowCheck4869]

theorem rawRowCheck4870 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3 = rawRow4870 := by decide +kernel

theorem rowCheck4870 : row4870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4870 := by decide +kernel

theorem rowEval4870 (x : Key → ℝ) : Integer.Sparse.eval row4870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4870, Integer.Sparse.eval_collectBalanced, rawRowCheck4870]

theorem rawRowCheck4871 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3 = rawRow4871 := by decide +kernel

theorem rowCheck4871 : row4871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4871 := by decide +kernel

theorem rowEval4871 (x : Key → ℝ) : Integer.Sparse.eval row4871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4871, Integer.Sparse.eval_collectBalanced, rawRowCheck4871]

theorem rawRowCheck4872 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4872 := by decide +kernel

theorem rowCheck4872 : row4872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4872 := by decide +kernel

theorem rowEval4872 (x : Key → ℝ) : Integer.Sparse.eval row4872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4872, Integer.Sparse.eval_collectBalanced, rawRowCheck4872]

theorem rawRowCheck4873 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4873 := by decide +kernel

theorem rowCheck4873 : row4873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4873 := by decide +kernel

theorem rowEval4873 (x : Key → ℝ) : Integer.Sparse.eval row4873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4873, Integer.Sparse.eval_collectBalanced, rawRowCheck4873]

theorem rawRowCheck4874 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4874 := by decide +kernel

theorem rowCheck4874 : row4874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4874 := by decide +kernel

theorem rowEval4874 (x : Key → ℝ) : Integer.Sparse.eval row4874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4874, Integer.Sparse.eval_collectBalanced, rawRowCheck4874]

theorem rawRowCheck4875 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3 = rawRow4875 := by decide +kernel

theorem rowCheck4875 : row4875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4875 := by decide +kernel

theorem rowEval4875 (x : Key → ℝ) : Integer.Sparse.eval row4875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4875, Integer.Sparse.eval_collectBalanced, rawRowCheck4875]

theorem rawRowCheck4876 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3 = rawRow4876 := by decide +kernel

theorem rowCheck4876 : row4876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4876 := by decide +kernel

theorem rowEval4876 (x : Key → ℝ) : Integer.Sparse.eval row4876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4876, Integer.Sparse.eval_collectBalanced, rawRowCheck4876]

theorem rawRowCheck4877 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3 = rawRow4877 := by decide +kernel

theorem rowCheck4877 : row4877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4877 := by decide +kernel

theorem rowEval4877 (x : Key → ℝ) : Integer.Sparse.eval row4877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4877, Integer.Sparse.eval_collectBalanced, rawRowCheck4877]

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

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4866 x
  · exact rowEval4867 x
  · exact rowEval4868 x
  · exact rowEval1554 x
  · exact rowEval1555 x
  · exact rowEval1556 x
  · exact rowEval4869 x
  · exact rowEval4870 x
  · exact rowEval4871 x
  · exact rowEval4872 x
  · exact rowEval4873 x
  · exact rowEval4874 x
  · exact rowEval1563 x
  · exact rowEval1564 x
  · exact rowEval1565 x
  · exact rowEval4875 x
  · exact rowEval4876 x
  · exact rowEval4877 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

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

theorem rawRowCheck806 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow806 := by decide +kernel

theorem rowCheck806 : row806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow806 := by decide +kernel

theorem rowEval806 (x : Key → ℝ) : Integer.Sparse.eval row806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck806, Integer.Sparse.eval_collectBalanced, rawRowCheck806]

theorem rawRowCheck807 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow807 := by decide +kernel

theorem rowCheck807 : row807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow807 := by decide +kernel

theorem rowEval807 (x : Key → ℝ) : Integer.Sparse.eval row807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck807, Integer.Sparse.eval_collectBalanced, rawRowCheck807]

theorem rawRowCheck808 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow808 := by decide +kernel

theorem rowCheck808 : row808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow808 := by decide +kernel

theorem rowEval808 (x : Key → ℝ) : Integer.Sparse.eval row808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck808, Integer.Sparse.eval_collectBalanced, rawRowCheck808]

theorem rawRowCheck809 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow809 := by decide +kernel

theorem rowCheck809 : row809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow809 := by decide +kernel

theorem rowEval809 (x : Key → ℝ) : Integer.Sparse.eval row809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck809, Integer.Sparse.eval_collectBalanced, rawRowCheck809]

theorem rawRowCheck810 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2 = rawRow810 := by decide +kernel

theorem rowCheck810 : row810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow810 := by decide +kernel

theorem rowEval810 (x : Key → ℝ) : Integer.Sparse.eval row810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck810, Integer.Sparse.eval_collectBalanced, rawRowCheck810]

theorem rawRowCheck811 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2 = rawRow811 := by decide +kernel

theorem rowCheck811 : row811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow811 := by decide +kernel

theorem rowEval811 (x : Key → ℝ) : Integer.Sparse.eval row811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck811, Integer.Sparse.eval_collectBalanced, rawRowCheck811]

theorem rawRowCheck812 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2 = rawRow812 := by decide +kernel

theorem rowCheck812 : row812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow812 := by decide +kernel

theorem rowEval812 (x : Key → ℝ) : Integer.Sparse.eval row812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck812, Integer.Sparse.eval_collectBalanced, rawRowCheck812]

theorem rawRowCheck813 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2 = rawRow813 := by decide +kernel

theorem rowCheck813 : row813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow813 := by decide +kernel

theorem rowEval813 (x : Key → ℝ) : Integer.Sparse.eval row813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck813, Integer.Sparse.eval_collectBalanced, rawRowCheck813]

theorem rawRowCheck814 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2 = rawRow814 := by decide +kernel

theorem rowCheck814 : row814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow814 := by decide +kernel

theorem rowEval814 (x : Key → ℝ) : Integer.Sparse.eval row814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck814, Integer.Sparse.eval_collectBalanced, rawRowCheck814]

theorem rawRowCheck815 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2 = rawRow815 := by decide +kernel

theorem rowCheck815 : row815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow815 := by decide +kernel

theorem rowEval815 (x : Key → ℝ) : Integer.Sparse.eval row815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck815, Integer.Sparse.eval_collectBalanced, rawRowCheck815]

theorem rawRowCheck816 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow816 := by decide +kernel

theorem rowCheck816 : row816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow816 := by decide +kernel

theorem rowEval816 (x : Key → ℝ) : Integer.Sparse.eval row816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck816, Integer.Sparse.eval_collectBalanced, rawRowCheck816]

theorem rawRowCheck817 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow817 := by decide +kernel

theorem rowCheck817 : row817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow817 := by decide +kernel

theorem rowEval817 (x : Key → ℝ) : Integer.Sparse.eval row817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck817, Integer.Sparse.eval_collectBalanced, rawRowCheck817]

theorem rawRowCheck818 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow818 := by decide +kernel

theorem rowCheck818 : row818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow818 := by decide +kernel

theorem rowEval818 (x : Key → ℝ) : Integer.Sparse.eval row818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck818, Integer.Sparse.eval_collectBalanced, rawRowCheck818]

theorem rawRowCheck819 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow819 := by decide +kernel

theorem rowCheck819 : row819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow819 := by decide +kernel

theorem rowEval819 (x : Key → ℝ) : Integer.Sparse.eval row819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck819, Integer.Sparse.eval_collectBalanced, rawRowCheck819]

theorem rawRowCheck820 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow820 := by decide +kernel

theorem rowCheck820 : row820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow820 := by decide +kernel

theorem rowEval820 (x : Key → ℝ) : Integer.Sparse.eval row820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck820, Integer.Sparse.eval_collectBalanced, rawRowCheck820]

theorem rawRowCheck821 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow821 := by decide +kernel

theorem rowCheck821 : row821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow821 := by decide +kernel

theorem rowEval821 (x : Key → ℝ) : Integer.Sparse.eval row821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck821, Integer.Sparse.eval_collectBalanced, rawRowCheck821]

theorem rawRowCheck822 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow822 := by decide +kernel

theorem rowCheck822 : row822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow822 := by decide +kernel

theorem rowEval822 (x : Key → ℝ) : Integer.Sparse.eval row822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck822, Integer.Sparse.eval_collectBalanced, rawRowCheck822]

theorem rawRowCheck823 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow823 := by decide +kernel

theorem rowCheck823 : row823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow823 := by decide +kernel

theorem rowEval823 (x : Key → ℝ) : Integer.Sparse.eval row823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck823, Integer.Sparse.eval_collectBalanced, rawRowCheck823]

theorem rawRowCheck824 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3 = rawRow824 := by decide +kernel

theorem rowCheck824 : row824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow824 := by decide +kernel

theorem rowEval824 (x : Key → ℝ) : Integer.Sparse.eval row824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck824, Integer.Sparse.eval_collectBalanced, rawRowCheck824]

theorem rawRowCheck825 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3 = rawRow825 := by decide +kernel

theorem rowCheck825 : row825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow825 := by decide +kernel

theorem rowEval825 (x : Key → ℝ) : Integer.Sparse.eval row825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck825, Integer.Sparse.eval_collectBalanced, rawRowCheck825]

theorem rawRowCheck826 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3 = rawRow826 := by decide +kernel

theorem rowCheck826 : row826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow826 := by decide +kernel

theorem rowEval826 (x : Key → ℝ) : Integer.Sparse.eval row826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck826, Integer.Sparse.eval_collectBalanced, rawRowCheck826]

theorem rawRowCheck827 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3 = rawRow827 := by decide +kernel

theorem rowCheck827 : row827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow827 := by decide +kernel

theorem rowEval827 (x : Key → ℝ) : Integer.Sparse.eval row827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck827, Integer.Sparse.eval_collectBalanced, rawRowCheck827]

theorem rawRowCheck828 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3 = rawRow828 := by decide +kernel

theorem rowCheck828 : row828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow828 := by decide +kernel

theorem rowEval828 (x : Key → ℝ) : Integer.Sparse.eval row828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck828, Integer.Sparse.eval_collectBalanced, rawRowCheck828]

theorem rawRowCheck829 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3 = rawRow829 := by decide +kernel

theorem rowCheck829 : row829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow829 := by decide +kernel

theorem rowEval829 (x : Key → ℝ) : Integer.Sparse.eval row829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck829, Integer.Sparse.eval_collectBalanced, rawRowCheck829]

theorem rawRowCheck830 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow830 := by decide +kernel

theorem rowCheck830 : row830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow830 := by decide +kernel

theorem rowEval830 (x : Key → ℝ) : Integer.Sparse.eval row830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck830, Integer.Sparse.eval_collectBalanced, rawRowCheck830]

theorem rawRowCheck831 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow831 := by decide +kernel

theorem rowCheck831 : row831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow831 := by decide +kernel

theorem rowEval831 (x : Key → ℝ) : Integer.Sparse.eval row831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck831, Integer.Sparse.eval_collectBalanced, rawRowCheck831]

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

theorem rawRowCheck832 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow832 := by decide +kernel

theorem rowCheck832 : row832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow832 := by decide +kernel

theorem rowEval832 (x : Key → ℝ) : Integer.Sparse.eval row832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck832, Integer.Sparse.eval_collectBalanced, rawRowCheck832]

theorem rawRowCheck833 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow833 := by decide +kernel

theorem rowCheck833 : row833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow833 := by decide +kernel

theorem rowEval833 (x : Key → ℝ) : Integer.Sparse.eval row833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck833, Integer.Sparse.eval_collectBalanced, rawRowCheck833]

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

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval778 x
  · exact rowEval779 x
  · exact rowEval780 x
  · exact rowEval781 x
  · exact rowEval782 x
  · exact rowEval783 x
  · exact rowEval784 x
  · exact rowEval785 x
  · exact rowEval786 x
  · exact rowEval787 x
  · exact rowEval788 x
  · exact rowEval789 x
  · exact rowEval790 x
  · exact rowEval791 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

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

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval806 x
  · exact rowEval807 x
  · exact rowEval808 x
  · exact rowEval809 x
  · exact rowEval810 x
  · exact rowEval811 x
  · exact rowEval812 x
  · exact rowEval813 x
  · exact rowEval814 x
  · exact rowEval815 x
  · exact rowEval816 x
  · exact rowEval817 x
  · exact rowEval818 x
  · exact rowEval819 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block1.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form3.terms k).tag (GramFunctions.Block1.form3.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval820 x
  · exact rowEval821 x
  · exact rowEval822 x
  · exact rowEval823 x
  · exact rowEval824 x
  · exact rowEval825 x
  · exact rowEval826 x
  · exact rowEval827 x
  · exact rowEval828 x
  · exact rowEval829 x
  · exact rowEval830 x
  · exact rowEval831 x
  · exact rowEval832 x
  · exact rowEval833 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block1.form3.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form3 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block1

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

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck1000 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3 = rawRow1000 := by decide +kernel

theorem rowCheck1000 : row1000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1000 := by decide +kernel

theorem rowEval1000 (x : Key → ℝ) : Integer.Sparse.eval row1000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1000, Integer.Sparse.eval_collectBalanced, rawRowCheck1000]

theorem rawRowCheck1001 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3 = rawRow1001 := by decide +kernel

theorem rowCheck1001 : row1001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1001 := by decide +kernel

theorem rowEval1001 (x : Key → ℝ) : Integer.Sparse.eval row1001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1001, Integer.Sparse.eval_collectBalanced, rawRowCheck1001]

theorem rawRowCheck1002 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3 = rawRow1002 := by decide +kernel

theorem rowCheck1002 : row1002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1002 := by decide +kernel

theorem rowEval1002 (x : Key → ℝ) : Integer.Sparse.eval row1002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1002, Integer.Sparse.eval_collectBalanced, rawRowCheck1002]

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

theorem rawRowCheck1009 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3 = rawRow1009 := by decide +kernel

theorem rowCheck1009 : row1009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1009 := by decide +kernel

theorem rowEval1009 (x : Key → ℝ) : Integer.Sparse.eval row1009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1009, Integer.Sparse.eval_collectBalanced, rawRowCheck1009]

theorem rawRowCheck1010 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3 = rawRow1010 := by decide +kernel

theorem rowCheck1010 : row1010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1010 := by decide +kernel

theorem rowEval1010 (x : Key → ℝ) : Integer.Sparse.eval row1010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1010, Integer.Sparse.eval_collectBalanced, rawRowCheck1010]

theorem rawRowCheck1011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3 = rawRow1011 := by decide +kernel

theorem rowCheck1011 : row1011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1011 := by decide +kernel

theorem rowEval1011 (x : Key → ℝ) : Integer.Sparse.eval row1011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1011, Integer.Sparse.eval_collectBalanced, rawRowCheck1011]

theorem rawRowCheck1012 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3 = rawRow1012 := by decide +kernel

theorem rowCheck1012 : row1012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1012 := by decide +kernel

theorem rowEval1012 (x : Key → ℝ) : Integer.Sparse.eval row1012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1012, Integer.Sparse.eval_collectBalanced, rawRowCheck1012]

theorem rawRowCheck1013 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3 = rawRow1013 := by decide +kernel

theorem rowCheck1013 : row1013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1013 := by decide +kernel

theorem rowEval1013 (x : Key → ℝ) : Integer.Sparse.eval row1013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1013, Integer.Sparse.eval_collectBalanced, rawRowCheck1013]

theorem rawRowCheck1014 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3 = rawRow1014 := by decide +kernel

theorem rowCheck1014 : row1014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1014 := by decide +kernel

theorem rowEval1014 (x : Key → ℝ) : Integer.Sparse.eval row1014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1014, Integer.Sparse.eval_collectBalanced, rawRowCheck1014]

theorem rawRowCheck1015 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow1015 := by decide +kernel

theorem rowCheck1015 : row1015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1015 := by decide +kernel

theorem rowEval1015 (x : Key → ℝ) : Integer.Sparse.eval row1015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1015, Integer.Sparse.eval_collectBalanced, rawRowCheck1015]

theorem rawRowCheck1016 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow1016 := by decide +kernel

theorem rowCheck1016 : row1016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1016 := by decide +kernel

theorem rowEval1016 (x : Key → ℝ) : Integer.Sparse.eval row1016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1016, Integer.Sparse.eval_collectBalanced, rawRowCheck1016]

theorem rawRowCheck1017 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow1017 := by decide +kernel

theorem rowCheck1017 : row1017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1017 := by decide +kernel

theorem rowEval1017 (x : Key → ℝ) : Integer.Sparse.eval row1017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1017, Integer.Sparse.eval_collectBalanced, rawRowCheck1017]

theorem rawRowCheck1018 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow1018 := by decide +kernel

theorem rowCheck1018 : row1018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1018 := by decide +kernel

theorem rowEval1018 (x : Key → ℝ) : Integer.Sparse.eval row1018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1018, Integer.Sparse.eval_collectBalanced, rawRowCheck1018]

theorem rawRowCheck1019 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow1019 := by decide +kernel

theorem rowCheck1019 : row1019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1019 := by decide +kernel

theorem rowEval1019 (x : Key → ℝ) : Integer.Sparse.eval row1019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1019, Integer.Sparse.eval_collectBalanced, rawRowCheck1019]

theorem rawRowCheck1020 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow1020 := by decide +kernel

theorem rowCheck1020 : row1020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1020 := by decide +kernel

theorem rowEval1020 (x : Key → ℝ) : Integer.Sparse.eval row1020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1020, Integer.Sparse.eval_collectBalanced, rawRowCheck1020]

theorem rawRowCheck1021 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow1021 := by decide +kernel

theorem rowCheck1021 : row1021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1021 := by decide +kernel

theorem rowEval1021 (x : Key → ℝ) : Integer.Sparse.eval row1021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1021, Integer.Sparse.eval_collectBalanced, rawRowCheck1021]

theorem rawRowCheck1022 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow1022 := by decide +kernel

theorem rowCheck1022 : row1022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1022 := by decide +kernel

theorem rowEval1022 (x : Key → ℝ) : Integer.Sparse.eval row1022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1022, Integer.Sparse.eval_collectBalanced, rawRowCheck1022]

theorem rawRowCheck1023 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow1023 := by decide +kernel

theorem rowCheck1023 : row1023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1023 := by decide +kernel

theorem rowEval1023 (x : Key → ℝ) : Integer.Sparse.eval row1023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1023, Integer.Sparse.eval_collectBalanced, rawRowCheck1023]

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

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block1.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form5.terms k).tag (GramFunctions.Block1.form5.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval994 x
  · exact rowEval995 x
  · exact rowEval996 x
  · exact rowEval997 x
  · exact rowEval998 x
  · exact rowEval999 x
  · exact rowEval1000 x
  · exact rowEval1001 x
  · exact rowEval1002 x
  · exact rowEval1003 x
  · exact rowEval1004 x
  · exact rowEval1005 x
  · exact rowEval1006 x
  · exact rowEval1007 x
  · exact rowEval1008 x
  · exact rowEval1009 x
  · exact rowEval1010 x
  · exact rowEval1011 x
  · exact rowEval1012 x
  · exact rowEval1013 x
  · exact rowEval1014 x
  · exact rowEval1015 x
  · exact rowEval1016 x
  · exact rowEval1017 x
  · exact rowEval1018 x
  · exact rowEval1019 x
  · exact rowEval1020 x
  · exact rowEval1021 x
  · exact rowEval1022 x
  · exact rowEval1023 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block1.form5.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form5 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

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

theorem rawRowCheck1392 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1392 := by decide +kernel

theorem rowCheck1392 : row1392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1392 := by decide +kernel

theorem rowEval1392 (x : Key → ℝ) : Integer.Sparse.eval row1392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1392, Integer.Sparse.eval_collectBalanced, rawRowCheck1392]

theorem rawRowCheck1393 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1393 := by decide +kernel

theorem rowCheck1393 : row1393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1393 := by decide +kernel

theorem rowEval1393 (x : Key → ℝ) : Integer.Sparse.eval row1393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1393, Integer.Sparse.eval_collectBalanced, rawRowCheck1393]

theorem rawRowCheck1394 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1394 := by decide +kernel

theorem rowCheck1394 : row1394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1394 := by decide +kernel

theorem rowEval1394 (x : Key → ℝ) : Integer.Sparse.eval row1394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1394, Integer.Sparse.eval_collectBalanced, rawRowCheck1394]

theorem rawRowCheck1395 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1395 := by decide +kernel

theorem rowCheck1395 : row1395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1395 := by decide +kernel

theorem rowEval1395 (x : Key → ℝ) : Integer.Sparse.eval row1395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1395, Integer.Sparse.eval_collectBalanced, rawRowCheck1395]

theorem rawRowCheck1396 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1396 := by decide +kernel

theorem rowCheck1396 : row1396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1396 := by decide +kernel

theorem rowEval1396 (x : Key → ℝ) : Integer.Sparse.eval row1396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1396, Integer.Sparse.eval_collectBalanced, rawRowCheck1396]

theorem rawRowCheck1397 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1397 := by decide +kernel

theorem rowCheck1397 : row1397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1397 := by decide +kernel

theorem rowEval1397 (x : Key → ℝ) : Integer.Sparse.eval row1397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1397, Integer.Sparse.eval_collectBalanced, rawRowCheck1397]

theorem rawRowCheck1398 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1398 := by decide +kernel

theorem rowCheck1398 : row1398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1398 := by decide +kernel

theorem rowEval1398 (x : Key → ℝ) : Integer.Sparse.eval row1398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1398, Integer.Sparse.eval_collectBalanced, rawRowCheck1398]

theorem rawRowCheck1399 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1399 := by decide +kernel

theorem rowCheck1399 : row1399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1399 := by decide +kernel

theorem rowEval1399 (x : Key → ℝ) : Integer.Sparse.eval row1399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1399, Integer.Sparse.eval_collectBalanced, rawRowCheck1399]

theorem rawRowCheck1400 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1400 := by decide +kernel

theorem rowCheck1400 : row1400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1400 := by decide +kernel

theorem rowEval1400 (x : Key → ℝ) : Integer.Sparse.eval row1400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1400, Integer.Sparse.eval_collectBalanced, rawRowCheck1400]

theorem rawRowCheck1401 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1401 := by decide +kernel

theorem rowCheck1401 : row1401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1401 := by decide +kernel

theorem rowEval1401 (x : Key → ℝ) : Integer.Sparse.eval row1401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1401, Integer.Sparse.eval_collectBalanced, rawRowCheck1401]

theorem rawRowCheck1402 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1402 := by decide +kernel

theorem rowCheck1402 : row1402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1402 := by decide +kernel

theorem rowEval1402 (x : Key → ℝ) : Integer.Sparse.eval row1402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1402, Integer.Sparse.eval_collectBalanced, rawRowCheck1402]

theorem rawRowCheck1403 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1403 := by decide +kernel

theorem rowCheck1403 : row1403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1403 := by decide +kernel

theorem rowEval1403 (x : Key → ℝ) : Integer.Sparse.eval row1403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1403, Integer.Sparse.eval_collectBalanced, rawRowCheck1403]

theorem rawRowCheck1404 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1404 := by decide +kernel

theorem rowCheck1404 : row1404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1404 := by decide +kernel

theorem rowEval1404 (x : Key → ℝ) : Integer.Sparse.eval row1404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1404, Integer.Sparse.eval_collectBalanced, rawRowCheck1404]

theorem rawRowCheck1405 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1405 := by decide +kernel

theorem rowCheck1405 : row1405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1405 := by decide +kernel

theorem rowEval1405 (x : Key → ℝ) : Integer.Sparse.eval row1405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1405, Integer.Sparse.eval_collectBalanced, rawRowCheck1405]

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

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1392 x
  · exact rowEval1393 x
  · exact rowEval1394 x
  · exact rowEval1395 x
  · exact rowEval1396 x
  · exact rowEval1397 x
  · exact rowEval1398 x
  · exact rowEval1399 x
  · exact rowEval1400 x
  · exact rowEval1401 x
  · exact rowEval1402 x
  · exact rowEval1403 x
  · exact rowEval1404 x
  · exact rowEval1405 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

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

theorem entryEvalRow3_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 3).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3 B hB
  · exact (entryEval4_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e_oai
