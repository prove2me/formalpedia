-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:43:20.986618+00:00
-- url     : https://prove2.me/submissions/fa14a8f6-a8c9-41b2-8b50-9e5cf72eb3bf

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E020
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_16_e

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

theorem rawRowCheck2236 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2236 := by decide +kernel

theorem rowCheck2236 : row2236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2236 := by decide +kernel

theorem rowEval2236 (x : Key → ℝ) : Integer.Sparse.eval row2236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2236, Integer.Sparse.eval_collectBalanced, rawRowCheck2236]

theorem rawRowCheck2237 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2237 := by decide +kernel

theorem rowCheck2237 : row2237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2237 := by decide +kernel

theorem rowEval2237 (x : Key → ℝ) : Integer.Sparse.eval row2237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2237, Integer.Sparse.eval_collectBalanced, rawRowCheck2237]

theorem rawRowCheck2238 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2238 := by decide +kernel

theorem rowCheck2238 : row2238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2238 := by decide +kernel

theorem rowEval2238 (x : Key → ℝ) : Integer.Sparse.eval row2238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2238, Integer.Sparse.eval_collectBalanced, rawRowCheck2238]

theorem rawRowCheck2245 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form5 = rawRow2245 := by decide +kernel

theorem rowCheck2245 : row2245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2245 := by decide +kernel

theorem rowEval2245 (x : Key → ℝ) : Integer.Sparse.eval row2245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2245, Integer.Sparse.eval_collectBalanced, rawRowCheck2245]

theorem rawRowCheck2246 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form5 = rawRow2246 := by decide +kernel

theorem rowCheck2246 : row2246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2246 := by decide +kernel

theorem rowEval2246 (x : Key → ℝ) : Integer.Sparse.eval row2246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2246, Integer.Sparse.eval_collectBalanced, rawRowCheck2246]

theorem rawRowCheck2247 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form5 = rawRow2247 := by decide +kernel

theorem rowCheck2247 : row2247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2247 := by decide +kernel

theorem rowEval2247 (x : Key → ℝ) : Integer.Sparse.eval row2247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2247, Integer.Sparse.eval_collectBalanced, rawRowCheck2247]

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2326 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2326 := by decide +kernel

theorem rowCheck2326 : row2326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2326 := by decide +kernel

theorem rowEval2326 (x : Key → ℝ) : Integer.Sparse.eval row2326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2326, Integer.Sparse.eval_collectBalanced, rawRowCheck2326]

theorem rawRowCheck2327 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2327 := by decide +kernel

theorem rowCheck2327 : row2327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2327 := by decide +kernel

theorem rowEval2327 (x : Key → ℝ) : Integer.Sparse.eval row2327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2327, Integer.Sparse.eval_collectBalanced, rawRowCheck2327]

theorem rawRowCheck2328 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2328 := by decide +kernel

theorem rowCheck2328 : row2328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2328 := by decide +kernel

theorem rowEval2328 (x : Key → ℝ) : Integer.Sparse.eval row2328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2328, Integer.Sparse.eval_collectBalanced, rawRowCheck2328]

theorem rawRowCheck2335 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2335 := by decide +kernel

theorem rowCheck2335 : row2335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2335 := by decide +kernel

theorem rowEval2335 (x : Key → ℝ) : Integer.Sparse.eval row2335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2335, Integer.Sparse.eval_collectBalanced, rawRowCheck2335]

theorem rawRowCheck2336 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2336 := by decide +kernel

theorem rowCheck2336 : row2336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2336 := by decide +kernel

theorem rowEval2336 (x : Key → ℝ) : Integer.Sparse.eval row2336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2336, Integer.Sparse.eval_collectBalanced, rawRowCheck2336]

theorem rawRowCheck2337 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2337 := by decide +kernel

theorem rowCheck2337 : row2337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2337 := by decide +kernel

theorem rowEval2337 (x : Key → ℝ) : Integer.Sparse.eval row2337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2337, Integer.Sparse.eval_collectBalanced, rawRowCheck2337]

theorem rawRowCheck2386 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2386 := by decide +kernel

theorem rowCheck2386 : row2386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2386 := by decide +kernel

theorem rowEval2386 (x : Key → ℝ) : Integer.Sparse.eval row2386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2386, Integer.Sparse.eval_collectBalanced, rawRowCheck2386]

theorem rawRowCheck2387 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2387 := by decide +kernel

theorem rowCheck2387 : row2387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2387 := by decide +kernel

theorem rowEval2387 (x : Key → ℝ) : Integer.Sparse.eval row2387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2387, Integer.Sparse.eval_collectBalanced, rawRowCheck2387]

theorem rawRowCheck2388 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2388 := by decide +kernel

theorem rowCheck2388 : row2388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2388 := by decide +kernel

theorem rowEval2388 (x : Key → ℝ) : Integer.Sparse.eval row2388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2388, Integer.Sparse.eval_collectBalanced, rawRowCheck2388]

theorem rawRowCheck2395 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2395 := by decide +kernel

theorem rowCheck2395 : row2395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2395 := by decide +kernel

theorem rowEval2395 (x : Key → ℝ) : Integer.Sparse.eval row2395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2395, Integer.Sparse.eval_collectBalanced, rawRowCheck2395]

theorem rawRowCheck2396 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2396 := by decide +kernel

theorem rowCheck2396 : row2396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2396 := by decide +kernel

theorem rowEval2396 (x : Key → ℝ) : Integer.Sparse.eval row2396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2396, Integer.Sparse.eval_collectBalanced, rawRowCheck2396]

theorem rawRowCheck2397 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2397 := by decide +kernel

theorem rowCheck2397 : row2397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2397 := by decide +kernel

theorem rowEval2397 (x : Key → ℝ) : Integer.Sparse.eval row2397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2397, Integer.Sparse.eval_collectBalanced, rawRowCheck2397]

theorem rawRowCheck2416 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2416 := by decide +kernel

theorem rowCheck2416 : row2416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2416 := by decide +kernel

theorem rowEval2416 (x : Key → ℝ) : Integer.Sparse.eval row2416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2416, Integer.Sparse.eval_collectBalanced, rawRowCheck2416]

theorem rawRowCheck2417 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2417 := by decide +kernel

theorem rowCheck2417 : row2417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2417 := by decide +kernel

theorem rowEval2417 (x : Key → ℝ) : Integer.Sparse.eval row2417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2417, Integer.Sparse.eval_collectBalanced, rawRowCheck2417]

theorem rawRowCheck2418 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2418 := by decide +kernel

theorem rowCheck2418 : row2418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2418 := by decide +kernel

theorem rowEval2418 (x : Key → ℝ) : Integer.Sparse.eval row2418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2418, Integer.Sparse.eval_collectBalanced, rawRowCheck2418]

theorem rawRowCheck2425 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2425 := by decide +kernel

theorem rowCheck2425 : row2425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2425 := by decide +kernel

theorem rowEval2425 (x : Key → ℝ) : Integer.Sparse.eval row2425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2425, Integer.Sparse.eval_collectBalanced, rawRowCheck2425]

theorem rawRowCheck2426 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2426 := by decide +kernel

theorem rowCheck2426 : row2426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2426 := by decide +kernel

theorem rowEval2426 (x : Key → ℝ) : Integer.Sparse.eval row2426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2426, Integer.Sparse.eval_collectBalanced, rawRowCheck2426]

theorem rawRowCheck2427 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2427 := by decide +kernel

theorem rowCheck2427 : row2427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2427 := by decide +kernel

theorem rowEval2427 (x : Key → ℝ) : Integer.Sparse.eval row2427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2427, Integer.Sparse.eval_collectBalanced, rawRowCheck2427]

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

theorem rawRowCheck2446 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2446 := by decide +kernel

theorem rowCheck2446 : row2446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2446 := by decide +kernel

theorem rowEval2446 (x : Key → ℝ) : Integer.Sparse.eval row2446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2446, Integer.Sparse.eval_collectBalanced, rawRowCheck2446]

theorem rawRowCheck2447 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2447 := by decide +kernel

theorem rowCheck2447 : row2447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2447 := by decide +kernel

theorem rowEval2447 (x : Key → ℝ) : Integer.Sparse.eval row2447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2447, Integer.Sparse.eval_collectBalanced, rawRowCheck2447]

theorem rawRowCheck2448 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2448 := by decide +kernel

theorem rowCheck2448 : row2448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2448 := by decide +kernel

theorem rowEval2448 (x : Key → ℝ) : Integer.Sparse.eval row2448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2448, Integer.Sparse.eval_collectBalanced, rawRowCheck2448]

theorem rawRowCheck2455 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form12 = rawRow2455 := by decide +kernel

theorem rowCheck2455 : row2455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2455 := by decide +kernel

theorem rowEval2455 (x : Key → ℝ) : Integer.Sparse.eval row2455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2455, Integer.Sparse.eval_collectBalanced, rawRowCheck2455]

theorem rawRowCheck2456 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form12 = rawRow2456 := by decide +kernel

theorem rowCheck2456 : row2456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2456 := by decide +kernel

theorem rowEval2456 (x : Key → ℝ) : Integer.Sparse.eval row2456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2456, Integer.Sparse.eval_collectBalanced, rawRowCheck2456]

theorem rawRowCheck2457 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form12 = rawRow2457 := by decide +kernel

theorem rowCheck2457 : row2457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2457 := by decide +kernel

theorem rowEval2457 (x : Key → ℝ) : Integer.Sparse.eval row2457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2457, Integer.Sparse.eval_collectBalanced, rawRowCheck2457]

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

theorem rawRowCheck3536 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form5 = rawRow3536 := by decide +kernel

theorem rowCheck3536 : row3536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3536 := by decide +kernel

theorem rowEval3536 (x : Key → ℝ) : Integer.Sparse.eval row3536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3536, Integer.Sparse.eval_collectBalanced, rawRowCheck3536]

theorem rawRowCheck3537 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form5 = rawRow3537 := by decide +kernel

theorem rowCheck3537 : row3537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3537 := by decide +kernel

theorem rowEval3537 (x : Key → ℝ) : Integer.Sparse.eval row3537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3537, Integer.Sparse.eval_collectBalanced, rawRowCheck3537]

theorem rawRowCheck3538 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form5 = rawRow3538 := by decide +kernel

theorem rowCheck3538 : row3538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3538 := by decide +kernel

theorem rowEval3538 (x : Key → ℝ) : Integer.Sparse.eval row3538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3538, Integer.Sparse.eval_collectBalanced, rawRowCheck3538]

theorem rawRowCheck3539 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3539 := by decide +kernel

theorem rowCheck3539 : row3539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3539 := by decide +kernel

theorem rowEval3539 (x : Key → ℝ) : Integer.Sparse.eval row3539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3539, Integer.Sparse.eval_collectBalanced, rawRowCheck3539]

theorem rawRowCheck3540 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3540 := by decide +kernel

theorem rowCheck3540 : row3540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3540 := by decide +kernel

theorem rowEval3540 (x : Key → ℝ) : Integer.Sparse.eval row3540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3540, Integer.Sparse.eval_collectBalanced, rawRowCheck3540]

theorem rawRowCheck3541 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3541 := by decide +kernel

theorem rowCheck3541 : row3541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3541 := by decide +kernel

theorem rowEval3541 (x : Key → ℝ) : Integer.Sparse.eval row3541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3541, Integer.Sparse.eval_collectBalanced, rawRowCheck3541]

theorem rawRowCheck3542 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form5 = rawRow3542 := by decide +kernel

theorem rowCheck3542 : row3542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3542 := by decide +kernel

theorem rowEval3542 (x : Key → ℝ) : Integer.Sparse.eval row3542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3542, Integer.Sparse.eval_collectBalanced, rawRowCheck3542]

theorem rawRowCheck3543 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form5 = rawRow3543 := by decide +kernel

theorem rowCheck3543 : row3543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3543 := by decide +kernel

theorem rowEval3543 (x : Key → ℝ) : Integer.Sparse.eval row3543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3543, Integer.Sparse.eval_collectBalanced, rawRowCheck3543]

theorem rawRowCheck3544 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form5 = rawRow3544 := by decide +kernel

theorem rowCheck3544 : row3544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3544 := by decide +kernel

theorem rowEval3544 (x : Key → ℝ) : Integer.Sparse.eval row3544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck3544, Integer.Sparse.eval_collectBalanced, rawRowCheck3544]

theorem rawRowCheck3545 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow3545 := by decide +kernel

theorem rowCheck3545 : row3545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3545 := by decide +kernel

theorem rowEval3545 (x : Key → ℝ) : Integer.Sparse.eval row3545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3545, Integer.Sparse.eval_collectBalanced, rawRowCheck3545]

theorem rawRowCheck3546 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow3546 := by decide +kernel

theorem rowCheck3546 : row3546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3546 := by decide +kernel

theorem rowEval3546 (x : Key → ℝ) : Integer.Sparse.eval row3546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck3546, Integer.Sparse.eval_collectBalanced, rawRowCheck3546]

theorem rawRowCheck3547 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow3547 := by decide +kernel

theorem rowCheck3547 : row3547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3547 := by decide +kernel

theorem rowEval3547 (x : Key → ℝ) : Integer.Sparse.eval row3547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3547, Integer.Sparse.eval_collectBalanced, rawRowCheck3547]

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

theorem rawRowCheck3572 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form8 = rawRow3572 := by decide +kernel

theorem rowCheck3572 : row3572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3572 := by decide +kernel

theorem rowEval3572 (x : Key → ℝ) : Integer.Sparse.eval row3572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3572, Integer.Sparse.eval_collectBalanced, rawRowCheck3572]

theorem rawRowCheck3573 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form8 = rawRow3573 := by decide +kernel

theorem rowCheck3573 : row3573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3573 := by decide +kernel

theorem rowEval3573 (x : Key → ℝ) : Integer.Sparse.eval row3573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3573, Integer.Sparse.eval_collectBalanced, rawRowCheck3573]

theorem rawRowCheck3574 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form8 = rawRow3574 := by decide +kernel

theorem rowCheck3574 : row3574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3574 := by decide +kernel

theorem rowEval3574 (x : Key → ℝ) : Integer.Sparse.eval row3574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3574, Integer.Sparse.eval_collectBalanced, rawRowCheck3574]

theorem rawRowCheck3575 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3575 := by decide +kernel

theorem rowCheck3575 : row3575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3575 := by decide +kernel

theorem rowEval3575 (x : Key → ℝ) : Integer.Sparse.eval row3575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3575, Integer.Sparse.eval_collectBalanced, rawRowCheck3575]

theorem rawRowCheck3576 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3576 := by decide +kernel

theorem rowCheck3576 : row3576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3576 := by decide +kernel

theorem rowEval3576 (x : Key → ℝ) : Integer.Sparse.eval row3576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3576, Integer.Sparse.eval_collectBalanced, rawRowCheck3576]

theorem rawRowCheck3577 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3577 := by decide +kernel

theorem rowCheck3577 : row3577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3577 := by decide +kernel

theorem rowEval3577 (x : Key → ℝ) : Integer.Sparse.eval row3577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3577, Integer.Sparse.eval_collectBalanced, rawRowCheck3577]

theorem rawRowCheck3578 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form8 = rawRow3578 := by decide +kernel

theorem rowCheck3578 : row3578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3578 := by decide +kernel

theorem rowEval3578 (x : Key → ℝ) : Integer.Sparse.eval row3578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3578, Integer.Sparse.eval_collectBalanced, rawRowCheck3578]

theorem rawRowCheck3579 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form8 = rawRow3579 := by decide +kernel

theorem rowCheck3579 : row3579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3579 := by decide +kernel

theorem rowEval3579 (x : Key → ℝ) : Integer.Sparse.eval row3579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3579, Integer.Sparse.eval_collectBalanced, rawRowCheck3579]

theorem rawRowCheck3580 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form8 = rawRow3580 := by decide +kernel

theorem rowCheck3580 : row3580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3580 := by decide +kernel

theorem rowEval3580 (x : Key → ℝ) : Integer.Sparse.eval row3580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3580, Integer.Sparse.eval_collectBalanced, rawRowCheck3580]

theorem rawRowCheck3581 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3581 := by decide +kernel

theorem rowCheck3581 : row3581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3581 := by decide +kernel

theorem rowEval3581 (x : Key → ℝ) : Integer.Sparse.eval row3581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3581, Integer.Sparse.eval_collectBalanced, rawRowCheck3581]

theorem rawRowCheck3582 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3582 := by decide +kernel

theorem rowCheck3582 : row3582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3582 := by decide +kernel

theorem rowEval3582 (x : Key → ℝ) : Integer.Sparse.eval row3582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3582, Integer.Sparse.eval_collectBalanced, rawRowCheck3582]

theorem rawRowCheck3583 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3583 := by decide +kernel

theorem rowCheck3583 : row3583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3583 := by decide +kernel

theorem rowEval3583 (x : Key → ℝ) : Integer.Sparse.eval row3583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3583, Integer.Sparse.eval_collectBalanced, rawRowCheck3583]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck3596 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form10 = rawRow3596 := by decide +kernel

theorem rowCheck3596 : row3596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3596 := by decide +kernel

theorem rowEval3596 (x : Key → ℝ) : Integer.Sparse.eval row3596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3596, Integer.Sparse.eval_collectBalanced, rawRowCheck3596]

theorem rawRowCheck3597 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form10 = rawRow3597 := by decide +kernel

theorem rowCheck3597 : row3597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3597 := by decide +kernel

theorem rowEval3597 (x : Key → ℝ) : Integer.Sparse.eval row3597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3597, Integer.Sparse.eval_collectBalanced, rawRowCheck3597]

theorem rawRowCheck3598 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form10 = rawRow3598 := by decide +kernel

theorem rowCheck3598 : row3598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3598 := by decide +kernel

theorem rowEval3598 (x : Key → ℝ) : Integer.Sparse.eval row3598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3598, Integer.Sparse.eval_collectBalanced, rawRowCheck3598]

theorem rawRowCheck3599 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3599 := by decide +kernel

theorem rowCheck3599 : row3599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3599 := by decide +kernel

theorem rowEval3599 (x : Key → ℝ) : Integer.Sparse.eval row3599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3599, Integer.Sparse.eval_collectBalanced, rawRowCheck3599]

theorem rawRowCheck3600 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3600 := by decide +kernel

theorem rowCheck3600 : row3600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3600 := by decide +kernel

theorem rowEval3600 (x : Key → ℝ) : Integer.Sparse.eval row3600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3600, Integer.Sparse.eval_collectBalanced, rawRowCheck3600]

theorem rawRowCheck3601 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3601 := by decide +kernel

theorem rowCheck3601 : row3601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3601 := by decide +kernel

theorem rowEval3601 (x : Key → ℝ) : Integer.Sparse.eval row3601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3601, Integer.Sparse.eval_collectBalanced, rawRowCheck3601]

theorem rawRowCheck3602 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form10 = rawRow3602 := by decide +kernel

theorem rowCheck3602 : row3602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3602 := by decide +kernel

theorem rowEval3602 (x : Key → ℝ) : Integer.Sparse.eval row3602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3602, Integer.Sparse.eval_collectBalanced, rawRowCheck3602]

theorem rawRowCheck3603 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form10 = rawRow3603 := by decide +kernel

theorem rowCheck3603 : row3603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3603 := by decide +kernel

theorem rowEval3603 (x : Key → ℝ) : Integer.Sparse.eval row3603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3603, Integer.Sparse.eval_collectBalanced, rawRowCheck3603]

theorem rawRowCheck3604 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form10 = rawRow3604 := by decide +kernel

theorem rowCheck3604 : row3604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3604 := by decide +kernel

theorem rowEval3604 (x : Key → ℝ) : Integer.Sparse.eval row3604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3604, Integer.Sparse.eval_collectBalanced, rawRowCheck3604]

theorem rawRowCheck3605 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3605 := by decide +kernel

theorem rowCheck3605 : row3605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3605 := by decide +kernel

theorem rowEval3605 (x : Key → ℝ) : Integer.Sparse.eval row3605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3605, Integer.Sparse.eval_collectBalanced, rawRowCheck3605]

theorem rawRowCheck3606 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3606 := by decide +kernel

theorem rowCheck3606 : row3606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3606 := by decide +kernel

theorem rowEval3606 (x : Key → ℝ) : Integer.Sparse.eval row3606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3606, Integer.Sparse.eval_collectBalanced, rawRowCheck3606]

theorem rawRowCheck3607 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3607 := by decide +kernel

theorem rowCheck3607 : row3607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3607 := by decide +kernel

theorem rowEval3607 (x : Key → ℝ) : Integer.Sparse.eval row3607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3607, Integer.Sparse.eval_collectBalanced, rawRowCheck3607]

theorem rawRowCheck3608 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form11 = rawRow3608 := by decide +kernel

theorem rowCheck3608 : row3608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3608 := by decide +kernel

theorem rowEval3608 (x : Key → ℝ) : Integer.Sparse.eval row3608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3608, Integer.Sparse.eval_collectBalanced, rawRowCheck3608]

theorem rawRowCheck3609 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form11 = rawRow3609 := by decide +kernel

theorem rowCheck3609 : row3609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3609 := by decide +kernel

theorem rowEval3609 (x : Key → ℝ) : Integer.Sparse.eval row3609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3609, Integer.Sparse.eval_collectBalanced, rawRowCheck3609]

theorem rawRowCheck3610 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form11 = rawRow3610 := by decide +kernel

theorem rowCheck3610 : row3610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3610 := by decide +kernel

theorem rowEval3610 (x : Key → ℝ) : Integer.Sparse.eval row3610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3610, Integer.Sparse.eval_collectBalanced, rawRowCheck3610]

theorem rawRowCheck3611 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3611 := by decide +kernel

theorem rowCheck3611 : row3611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3611 := by decide +kernel

theorem rowEval3611 (x : Key → ℝ) : Integer.Sparse.eval row3611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3611, Integer.Sparse.eval_collectBalanced, rawRowCheck3611]

theorem rawRowCheck3612 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3612 := by decide +kernel

theorem rowCheck3612 : row3612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3612 := by decide +kernel

theorem rowEval3612 (x : Key → ℝ) : Integer.Sparse.eval row3612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3612, Integer.Sparse.eval_collectBalanced, rawRowCheck3612]

theorem rawRowCheck3613 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3613 := by decide +kernel

theorem rowCheck3613 : row3613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3613 := by decide +kernel

theorem rowEval3613 (x : Key → ℝ) : Integer.Sparse.eval row3613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3613, Integer.Sparse.eval_collectBalanced, rawRowCheck3613]

theorem rawRowCheck3614 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form11 = rawRow3614 := by decide +kernel

theorem rowCheck3614 : row3614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3614 := by decide +kernel

theorem rowEval3614 (x : Key → ℝ) : Integer.Sparse.eval row3614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3614, Integer.Sparse.eval_collectBalanced, rawRowCheck3614]

theorem rawRowCheck3615 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form11 = rawRow3615 := by decide +kernel

theorem rowCheck3615 : row3615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3615 := by decide +kernel

theorem rowEval3615 (x : Key → ℝ) : Integer.Sparse.eval row3615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3615, Integer.Sparse.eval_collectBalanced, rawRowCheck3615]

theorem rawRowCheck3616 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form11 = rawRow3616 := by decide +kernel

theorem rowCheck3616 : row3616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3616 := by decide +kernel

theorem rowEval3616 (x : Key → ℝ) : Integer.Sparse.eval row3616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3616, Integer.Sparse.eval_collectBalanced, rawRowCheck3616]

theorem rawRowCheck3617 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3617 := by decide +kernel

theorem rowCheck3617 : row3617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3617 := by decide +kernel

theorem rowEval3617 (x : Key → ℝ) : Integer.Sparse.eval row3617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3617, Integer.Sparse.eval_collectBalanced, rawRowCheck3617]

theorem rawRowCheck3618 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3618 := by decide +kernel

theorem rowCheck3618 : row3618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3618 := by decide +kernel

theorem rowEval3618 (x : Key → ℝ) : Integer.Sparse.eval row3618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3618, Integer.Sparse.eval_collectBalanced, rawRowCheck3618]

theorem rawRowCheck3619 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3619 := by decide +kernel

theorem rowCheck3619 : row3619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3619 := by decide +kernel

theorem rowEval3619 (x : Key → ℝ) : Integer.Sparse.eval row3619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3619, Integer.Sparse.eval_collectBalanced, rawRowCheck3619]

theorem rawRowCheck3620 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form12 = rawRow3620 := by decide +kernel

theorem rowCheck3620 : row3620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3620 := by decide +kernel

theorem rowEval3620 (x : Key → ℝ) : Integer.Sparse.eval row3620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3620, Integer.Sparse.eval_collectBalanced, rawRowCheck3620]

theorem rawRowCheck3621 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form12 = rawRow3621 := by decide +kernel

theorem rowCheck3621 : row3621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3621 := by decide +kernel

theorem rowEval3621 (x : Key → ℝ) : Integer.Sparse.eval row3621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3621, Integer.Sparse.eval_collectBalanced, rawRowCheck3621]

theorem rawRowCheck3622 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form12 = rawRow3622 := by decide +kernel

theorem rowCheck3622 : row3622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3622 := by decide +kernel

theorem rowEval3622 (x : Key → ℝ) : Integer.Sparse.eval row3622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3622, Integer.Sparse.eval_collectBalanced, rawRowCheck3622]

theorem rawRowCheck3623 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3623 := by decide +kernel

theorem rowCheck3623 : row3623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3623 := by decide +kernel

theorem rowEval3623 (x : Key → ℝ) : Integer.Sparse.eval row3623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3623, Integer.Sparse.eval_collectBalanced, rawRowCheck3623]

theorem rawRowCheck3624 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3624 := by decide +kernel

theorem rowCheck3624 : row3624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3624 := by decide +kernel

theorem rowEval3624 (x : Key → ℝ) : Integer.Sparse.eval row3624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3624, Integer.Sparse.eval_collectBalanced, rawRowCheck3624]

theorem rawRowCheck3625 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3625 := by decide +kernel

theorem rowCheck3625 : row3625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3625 := by decide +kernel

theorem rowEval3625 (x : Key → ℝ) : Integer.Sparse.eval row3625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3625, Integer.Sparse.eval_collectBalanced, rawRowCheck3625]

theorem rawRowCheck3626 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form12 = rawRow3626 := by decide +kernel

theorem rowCheck3626 : row3626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3626 := by decide +kernel

theorem rowEval3626 (x : Key → ℝ) : Integer.Sparse.eval row3626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3626, Integer.Sparse.eval_collectBalanced, rawRowCheck3626]

theorem rawRowCheck3627 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form12 = rawRow3627 := by decide +kernel

theorem rowCheck3627 : row3627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3627 := by decide +kernel

theorem rowEval3627 (x : Key → ℝ) : Integer.Sparse.eval row3627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3627, Integer.Sparse.eval_collectBalanced, rawRowCheck3627]

theorem rawRowCheck3628 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form12 = rawRow3628 := by decide +kernel

theorem rowCheck3628 : row3628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3628 := by decide +kernel

theorem rowEval3628 (x : Key → ℝ) : Integer.Sparse.eval row3628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3628, Integer.Sparse.eval_collectBalanced, rawRowCheck3628]

theorem rawRowCheck3629 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3629 := by decide +kernel

theorem rowCheck3629 : row3629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3629 := by decide +kernel

theorem rowEval3629 (x : Key → ℝ) : Integer.Sparse.eval row3629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3629, Integer.Sparse.eval_collectBalanced, rawRowCheck3629]

theorem rawRowCheck3630 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3630 := by decide +kernel

theorem rowCheck3630 : row3630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3630 := by decide +kernel

theorem rowEval3630 (x : Key → ℝ) : Integer.Sparse.eval row3630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3630, Integer.Sparse.eval_collectBalanced, rawRowCheck3630]

theorem rawRowCheck3631 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3631 := by decide +kernel

theorem rowCheck3631 : row3631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3631 := by decide +kernel

theorem rowEval3631 (x : Key → ℝ) : Integer.Sparse.eval row3631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3631, Integer.Sparse.eval_collectBalanced, rawRowCheck3631]

theorem rawRowCheck3632 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3632 := by decide +kernel

theorem rowCheck3632 : row3632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3632 := by decide +kernel

theorem rowEval3632 (x : Key → ℝ) : Integer.Sparse.eval row3632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3632, Integer.Sparse.eval_collectBalanced, rawRowCheck3632]

theorem rawRowCheck3633 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3633 := by decide +kernel

theorem rowCheck3633 : row3633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3633 := by decide +kernel

theorem rowEval3633 (x : Key → ℝ) : Integer.Sparse.eval row3633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3633, Integer.Sparse.eval_collectBalanced, rawRowCheck3633]

theorem rawRowCheck3634 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3634 := by decide +kernel

theorem rowCheck3634 : row3634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3634 := by decide +kernel

theorem rowEval3634 (x : Key → ℝ) : Integer.Sparse.eval row3634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3634, Integer.Sparse.eval_collectBalanced, rawRowCheck3634]

theorem rawRowCheck3635 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3635 := by decide +kernel

theorem rowCheck3635 : row3635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3635 := by decide +kernel

theorem rowEval3635 (x : Key → ℝ) : Integer.Sparse.eval row3635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3635, Integer.Sparse.eval_collectBalanced, rawRowCheck3635]

theorem rawRowCheck3636 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3636 := by decide +kernel

theorem rowCheck3636 : row3636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3636 := by decide +kernel

theorem rowEval3636 (x : Key → ℝ) : Integer.Sparse.eval row3636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3636, Integer.Sparse.eval_collectBalanced, rawRowCheck3636]

theorem rawRowCheck3637 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3637 := by decide +kernel

theorem rowCheck3637 : row3637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3637 := by decide +kernel

theorem rowEval3637 (x : Key → ℝ) : Integer.Sparse.eval row3637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3637, Integer.Sparse.eval_collectBalanced, rawRowCheck3637]

theorem rawRowCheck3638 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3638 := by decide +kernel

theorem rowCheck3638 : row3638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3638 := by decide +kernel

theorem rowEval3638 (x : Key → ℝ) : Integer.Sparse.eval row3638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3638, Integer.Sparse.eval_collectBalanced, rawRowCheck3638]

theorem rawRowCheck3639 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3639 := by decide +kernel

theorem rowCheck3639 : row3639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3639 := by decide +kernel

theorem rowEval3639 (x : Key → ℝ) : Integer.Sparse.eval row3639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3639, Integer.Sparse.eval_collectBalanced, rawRowCheck3639]

theorem rawRowCheck3640 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3640 := by decide +kernel

theorem rowCheck3640 : row3640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3640 := by decide +kernel

theorem rowEval3640 (x : Key → ℝ) : Integer.Sparse.eval row3640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3640, Integer.Sparse.eval_collectBalanced, rawRowCheck3640]

theorem rawRowCheck3641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3641 := by decide +kernel

theorem rowCheck3641 : row3641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3641 := by decide +kernel

theorem rowEval3641 (x : Key → ℝ) : Integer.Sparse.eval row3641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3641, Integer.Sparse.eval_collectBalanced, rawRowCheck3641]

theorem rawRowCheck3642 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3642 := by decide +kernel

theorem rowCheck3642 : row3642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3642 := by decide +kernel

theorem rowEval3642 (x : Key → ℝ) : Integer.Sparse.eval row3642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3642, Integer.Sparse.eval_collectBalanced, rawRowCheck3642]

theorem rawRowCheck3643 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3643 := by decide +kernel

theorem rowCheck3643 : row3643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3643 := by decide +kernel

theorem rowEval3643 (x : Key → ℝ) : Integer.Sparse.eval row3643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3643, Integer.Sparse.eval_collectBalanced, rawRowCheck3643]

theorem rawRowCheck3644 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3644 := by decide +kernel

theorem rowCheck3644 : row3644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3644 := by decide +kernel

theorem rowEval3644 (x : Key → ℝ) : Integer.Sparse.eval row3644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3644, Integer.Sparse.eval_collectBalanced, rawRowCheck3644]

theorem rawRowCheck3645 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3645 := by decide +kernel

theorem rowCheck3645 : row3645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3645 := by decide +kernel

theorem rowEval3645 (x : Key → ℝ) : Integer.Sparse.eval row3645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3645, Integer.Sparse.eval_collectBalanced, rawRowCheck3645]

theorem rawRowCheck3646 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3646 := by decide +kernel

theorem rowCheck3646 : row3646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3646 := by decide +kernel

theorem rowEval3646 (x : Key → ℝ) : Integer.Sparse.eval row3646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3646, Integer.Sparse.eval_collectBalanced, rawRowCheck3646]

theorem rawRowCheck3647 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3647 := by decide +kernel

theorem rowCheck3647 : row3647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3647 := by decide +kernel

theorem rowEval3647 (x : Key → ℝ) : Integer.Sparse.eval row3647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3647, Integer.Sparse.eval_collectBalanced, rawRowCheck3647]

theorem rawRowCheck3648 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3648 := by decide +kernel

theorem rowCheck3648 : row3648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3648 := by decide +kernel

theorem rowEval3648 (x : Key → ℝ) : Integer.Sparse.eval row3648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3648, Integer.Sparse.eval_collectBalanced, rawRowCheck3648]

theorem rawRowCheck3649 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3649 := by decide +kernel

theorem rowCheck3649 : row3649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3649 := by decide +kernel

theorem rowEval3649 (x : Key → ℝ) : Integer.Sparse.eval row3649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3649, Integer.Sparse.eval_collectBalanced, rawRowCheck3649]

theorem rawRowCheck3650 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3650 := by decide +kernel

theorem rowCheck3650 : row3650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3650 := by decide +kernel

theorem rowEval3650 (x : Key → ℝ) : Integer.Sparse.eval row3650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3650, Integer.Sparse.eval_collectBalanced, rawRowCheck3650]

theorem rawRowCheck3651 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3651 := by decide +kernel

theorem rowCheck3651 : row3651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3651 := by decide +kernel

theorem rowEval3651 (x : Key → ℝ) : Integer.Sparse.eval row3651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3651, Integer.Sparse.eval_collectBalanced, rawRowCheck3651]

theorem rawRowCheck3652 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3652 := by decide +kernel

theorem rowCheck3652 : row3652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3652 := by decide +kernel

theorem rowEval3652 (x : Key → ℝ) : Integer.Sparse.eval row3652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3652, Integer.Sparse.eval_collectBalanced, rawRowCheck3652]

theorem rawRowCheck3653 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form14 = rawRow3653 := by decide +kernel

theorem rowCheck3653 : row3653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3653 := by decide +kernel

theorem rowEval3653 (x : Key → ℝ) : Integer.Sparse.eval row3653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3653, Integer.Sparse.eval_collectBalanced, rawRowCheck3653]

theorem rawRowCheck3654 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form14 = rawRow3654 := by decide +kernel

theorem rowCheck3654 : row3654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3654 := by decide +kernel

theorem rowEval3654 (x : Key → ℝ) : Integer.Sparse.eval row3654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3654, Integer.Sparse.eval_collectBalanced, rawRowCheck3654]

theorem rawRowCheck3655 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form14 = rawRow3655 := by decide +kernel

theorem rowCheck3655 : row3655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3655 := by decide +kernel

theorem rowEval3655 (x : Key → ℝ) : Integer.Sparse.eval row3655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3655, Integer.Sparse.eval_collectBalanced, rawRowCheck3655]

theorem rawRowCheck3656 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3656 := by decide +kernel

theorem rowCheck3656 : row3656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3656 := by decide +kernel

theorem rowEval3656 (x : Key → ℝ) : Integer.Sparse.eval row3656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3656, Integer.Sparse.eval_collectBalanced, rawRowCheck3656]

theorem rawRowCheck3657 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3657 := by decide +kernel

theorem rowCheck3657 : row3657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3657 := by decide +kernel

theorem rowEval3657 (x : Key → ℝ) : Integer.Sparse.eval row3657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3657, Integer.Sparse.eval_collectBalanced, rawRowCheck3657]

theorem rawRowCheck3658 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3658 := by decide +kernel

theorem rowCheck3658 : row3658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3658 := by decide +kernel

theorem rowEval3658 (x : Key → ℝ) : Integer.Sparse.eval row3658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3658, Integer.Sparse.eval_collectBalanced, rawRowCheck3658]

theorem rawRowCheck3659 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3659 := by decide +kernel

theorem rowCheck3659 : row3659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3659 := by decide +kernel

theorem rowEval3659 (x : Key → ℝ) : Integer.Sparse.eval row3659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3659, Integer.Sparse.eval_collectBalanced, rawRowCheck3659]

theorem rawRowCheck3660 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3660 := by decide +kernel

theorem rowCheck3660 : row3660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3660 := by decide +kernel

theorem rowEval3660 (x : Key → ℝ) : Integer.Sparse.eval row3660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3660, Integer.Sparse.eval_collectBalanced, rawRowCheck3660]

theorem rawRowCheck3661 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3661 := by decide +kernel

theorem rowCheck3661 : row3661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3661 := by decide +kernel

theorem rowEval3661 (x : Key → ℝ) : Integer.Sparse.eval row3661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3661, Integer.Sparse.eval_collectBalanced, rawRowCheck3661]

theorem rawRowCheck3662 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form14 = rawRow3662 := by decide +kernel

theorem rowCheck3662 : row3662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3662 := by decide +kernel

theorem rowEval3662 (x : Key → ℝ) : Integer.Sparse.eval row3662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3662, Integer.Sparse.eval_collectBalanced, rawRowCheck3662]

theorem rawRowCheck3663 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form14 = rawRow3663 := by decide +kernel

theorem rowCheck3663 : row3663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3663 := by decide +kernel

theorem rowEval3663 (x : Key → ℝ) : Integer.Sparse.eval row3663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3663, Integer.Sparse.eval_collectBalanced, rawRowCheck3663]

theorem rawRowCheck3664 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form14 = rawRow3664 := by decide +kernel

theorem rowCheck3664 : row3664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3664 := by decide +kernel

theorem rowEval3664 (x : Key → ℝ) : Integer.Sparse.eval row3664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3664, Integer.Sparse.eval_collectBalanced, rawRowCheck3664]

theorem rawRowCheck3665 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3665 := by decide +kernel

theorem rowCheck3665 : row3665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3665 := by decide +kernel

theorem rowEval3665 (x : Key → ℝ) : Integer.Sparse.eval row3665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3665, Integer.Sparse.eval_collectBalanced, rawRowCheck3665]

theorem rawRowCheck3666 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3666 := by decide +kernel

theorem rowCheck3666 : row3666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3666 := by decide +kernel

theorem rowEval3666 (x : Key → ℝ) : Integer.Sparse.eval row3666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3666, Integer.Sparse.eval_collectBalanced, rawRowCheck3666]

theorem rawRowCheck3667 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3667 := by decide +kernel

theorem rowCheck3667 : row3667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3667 := by decide +kernel

theorem rowEval3667 (x : Key → ℝ) : Integer.Sparse.eval row3667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3667, Integer.Sparse.eval_collectBalanced, rawRowCheck3667]

theorem rawRowCheck3686 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form16 = rawRow3686 := by decide +kernel

theorem rowCheck3686 : row3686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3686 := by decide +kernel

theorem rowEval3686 (x : Key → ℝ) : Integer.Sparse.eval row3686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3686, Integer.Sparse.eval_collectBalanced, rawRowCheck3686]

theorem rawRowCheck3687 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form16 = rawRow3687 := by decide +kernel

theorem rowCheck3687 : row3687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3687 := by decide +kernel

theorem rowEval3687 (x : Key → ℝ) : Integer.Sparse.eval row3687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3687, Integer.Sparse.eval_collectBalanced, rawRowCheck3687]

theorem rawRowCheck3688 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form16 = rawRow3688 := by decide +kernel

theorem rowCheck3688 : row3688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3688 := by decide +kernel

theorem rowEval3688 (x : Key → ℝ) : Integer.Sparse.eval row3688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3688, Integer.Sparse.eval_collectBalanced, rawRowCheck3688]

theorem rawRowCheck3689 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form16 = rawRow3689 := by decide +kernel

theorem rowCheck3689 : row3689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3689 := by decide +kernel

theorem rowEval3689 (x : Key → ℝ) : Integer.Sparse.eval row3689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3689, Integer.Sparse.eval_collectBalanced, rawRowCheck3689]

theorem rawRowCheck3690 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form16 = rawRow3690 := by decide +kernel

theorem rowCheck3690 : row3690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3690 := by decide +kernel

theorem rowEval3690 (x : Key → ℝ) : Integer.Sparse.eval row3690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3690, Integer.Sparse.eval_collectBalanced, rawRowCheck3690]

theorem rawRowCheck3691 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form16 = rawRow3691 := by decide +kernel

theorem rowCheck3691 : row3691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3691 := by decide +kernel

theorem rowEval3691 (x : Key → ℝ) : Integer.Sparse.eval row3691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3691, Integer.Sparse.eval_collectBalanced, rawRowCheck3691]

theorem rawRowCheck3692 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form16 = rawRow3692 := by decide +kernel

theorem rowCheck3692 : row3692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3692 := by decide +kernel

theorem rowEval3692 (x : Key → ℝ) : Integer.Sparse.eval row3692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3692, Integer.Sparse.eval_collectBalanced, rawRowCheck3692]

theorem rawRowCheck3693 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form16 = rawRow3693 := by decide +kernel

theorem rowCheck3693 : row3693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3693 := by decide +kernel

theorem rowEval3693 (x : Key → ℝ) : Integer.Sparse.eval row3693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3693, Integer.Sparse.eval_collectBalanced, rawRowCheck3693]

theorem rawRowCheck3694 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form16 = rawRow3694 := by decide +kernel

theorem rowCheck3694 : row3694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3694 := by decide +kernel

theorem rowEval3694 (x : Key → ℝ) : Integer.Sparse.eval row3694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3694, Integer.Sparse.eval_collectBalanced, rawRowCheck3694]

theorem rawRowCheck3695 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow3695 := by decide +kernel

theorem rowCheck3695 : row3695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3695 := by decide +kernel

theorem rowEval3695 (x : Key → ℝ) : Integer.Sparse.eval row3695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3695, Integer.Sparse.eval_collectBalanced, rawRowCheck3695]

theorem rawRowCheck3696 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow3696 := by decide +kernel

theorem rowCheck3696 : row3696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3696 := by decide +kernel

theorem rowEval3696 (x : Key → ℝ) : Integer.Sparse.eval row3696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3696, Integer.Sparse.eval_collectBalanced, rawRowCheck3696]

theorem rawRowCheck3697 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow3697 := by decide +kernel

theorem rowCheck3697 : row3697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3697 := by decide +kernel

theorem rowEval3697 (x : Key → ℝ) : Integer.Sparse.eval row3697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck3697, Integer.Sparse.eval_collectBalanced, rawRowCheck3697]

theorem rawRowCheck3698 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form16 = rawRow3698 := by decide +kernel

theorem rowCheck3698 : row3698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3698 := by decide +kernel

theorem rowEval3698 (x : Key → ℝ) : Integer.Sparse.eval row3698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3698, Integer.Sparse.eval_collectBalanced, rawRowCheck3698]

theorem rawRowCheck3699 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form16 = rawRow3699 := by decide +kernel

theorem rowCheck3699 : row3699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3699 := by decide +kernel

theorem rowEval3699 (x : Key → ℝ) : Integer.Sparse.eval row3699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3699, Integer.Sparse.eval_collectBalanced, rawRowCheck3699]

theorem rawRowCheck3700 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form16 = rawRow3700 := by decide +kernel

theorem rowCheck3700 : row3700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3700 := by decide +kernel

theorem rowEval3700 (x : Key → ℝ) : Integer.Sparse.eval row3700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3700, Integer.Sparse.eval_collectBalanced, rawRowCheck3700]

theorem rawRowCheck3701 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow3701 := by decide +kernel

theorem rowCheck3701 : row3701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3701 := by decide +kernel

theorem rowEval3701 (x : Key → ℝ) : Integer.Sparse.eval row3701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3701, Integer.Sparse.eval_collectBalanced, rawRowCheck3701]

theorem rawRowCheck3702 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow3702 := by decide +kernel

theorem rowCheck3702 : row3702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3702 := by decide +kernel

theorem rowEval3702 (x : Key → ℝ) : Integer.Sparse.eval row3702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3702, Integer.Sparse.eval_collectBalanced, rawRowCheck3702]

theorem rawRowCheck3703 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow3703 := by decide +kernel

theorem rowCheck3703 : row3703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3703 := by decide +kernel

theorem rowEval3703 (x : Key → ℝ) : Integer.Sparse.eval row3703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck3703, Integer.Sparse.eval_collectBalanced, rawRowCheck3703]

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

theorem entryCheck16_5 : entry16_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_5 k)) := by decide +kernel

theorem rowsSound16_5 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2236 x
  · exact rowEval2237 x
  · exact rowEval2238 x
  · exact rowEval3536 x
  · exact rowEval3537 x
  · exact rowEval3538 x
  · exact rowEval2245 x
  · exact rowEval2246 x
  · exact rowEval2247 x
  · exact rowEval3539 x
  · exact rowEval3540 x
  · exact rowEval3541 x
  · exact rowEval3542 x
  · exact rowEval3543 x
  · exact rowEval3544 x
  · exact rowEval3545 x
  · exact rowEval3546 x
  · exact rowEval3547 x

theorem entryEval16_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_5 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck16_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_5]

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

theorem entryCheck16_8 : entry16_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_8 k)) := by decide +kernel

theorem rowsSound16_8 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2326 x
  · exact rowEval2327 x
  · exact rowEval2328 x
  · exact rowEval3572 x
  · exact rowEval3573 x
  · exact rowEval3574 x
  · exact rowEval2335 x
  · exact rowEval2336 x
  · exact rowEval2337 x
  · exact rowEval3575 x
  · exact rowEval3576 x
  · exact rowEval3577 x
  · exact rowEval3578 x
  · exact rowEval3579 x
  · exact rowEval3580 x
  · exact rowEval3581 x
  · exact rowEval3582 x
  · exact rowEval3583 x

theorem entryEval16_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_8 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck16_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_8]

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2386 x
  · exact rowEval2387 x
  · exact rowEval2388 x
  · exact rowEval3596 x
  · exact rowEval3597 x
  · exact rowEval3598 x
  · exact rowEval2395 x
  · exact rowEval2396 x
  · exact rowEval2397 x
  · exact rowEval3599 x
  · exact rowEval3600 x
  · exact rowEval3601 x
  · exact rowEval3602 x
  · exact rowEval3603 x
  · exact rowEval3604 x
  · exact rowEval3605 x
  · exact rowEval3606 x
  · exact rowEval3607 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

theorem entryCheck16_11 : entry16_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_11 k)) := by decide +kernel

theorem rowsSound16_11 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2416 x
  · exact rowEval2417 x
  · exact rowEval2418 x
  · exact rowEval3608 x
  · exact rowEval3609 x
  · exact rowEval3610 x
  · exact rowEval2425 x
  · exact rowEval2426 x
  · exact rowEval2427 x
  · exact rowEval3611 x
  · exact rowEval3612 x
  · exact rowEval3613 x
  · exact rowEval3614 x
  · exact rowEval3615 x
  · exact rowEval3616 x
  · exact rowEval3617 x
  · exact rowEval3618 x
  · exact rowEval3619 x

theorem entryEval16_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_11 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck16_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_11]

theorem entryCheck16_12 : entry16_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_12 k)) := by decide +kernel

theorem rowsSound16_12 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2446 x
  · exact rowEval2447 x
  · exact rowEval2448 x
  · exact rowEval3620 x
  · exact rowEval3621 x
  · exact rowEval3622 x
  · exact rowEval2455 x
  · exact rowEval2456 x
  · exact rowEval2457 x
  · exact rowEval3623 x
  · exact rowEval3624 x
  · exact rowEval3625 x
  · exact rowEval3626 x
  · exact rowEval3627 x
  · exact rowEval3628 x
  · exact rowEval3629 x
  · exact rowEval3630 x
  · exact rowEval3631 x

theorem entryEval16_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_12 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck16_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_12]

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval3632 x
  · exact rowEval3633 x
  · exact rowEval3634 x
  · exact rowEval3635 x
  · exact rowEval3636 x
  · exact rowEval3637 x
  · exact rowEval3638 x
  · exact rowEval3639 x
  · exact rowEval3640 x
  · exact rowEval3641 x
  · exact rowEval3642 x
  · exact rowEval3643 x
  · exact rowEval3644 x
  · exact rowEval3645 x
  · exact rowEval3646 x
  · exact rowEval3647 x
  · exact rowEval3648 x
  · exact rowEval3649 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

theorem entryCheck16_14 : entry16_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_14 k)) := by decide +kernel

theorem rowsSound16_14 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval3650 x
  · exact rowEval3651 x
  · exact rowEval3652 x
  · exact rowEval3653 x
  · exact rowEval3654 x
  · exact rowEval3655 x
  · exact rowEval3656 x
  · exact rowEval3657 x
  · exact rowEval3658 x
  · exact rowEval3659 x
  · exact rowEval3660 x
  · exact rowEval3661 x
  · exact rowEval3662 x
  · exact rowEval3663 x
  · exact rowEval3664 x
  · exact rowEval3665 x
  · exact rowEval3666 x
  · exact rowEval3667 x

theorem entryEval16_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_14 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck16_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_14]

theorem entryCheck16_16 : entry16_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_16 k)) := by decide +kernel

theorem rowsSound16_16 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval3686 x
  · exact rowEval3687 x
  · exact rowEval3688 x
  · exact rowEval3689 x
  · exact rowEval3690 x
  · exact rowEval3691 x
  · exact rowEval3692 x
  · exact rowEval3693 x
  · exact rowEval3694 x
  · exact rowEval3695 x
  · exact rowEval3696 x
  · exact rowEval3697 x
  · exact rowEval3698 x
  · exact rowEval3699 x
  · exact rowEval3700 x
  · exact rowEval3701 x
  · exact rowEval3702 x
  · exact rowEval3703 x

theorem entryEval16_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_16 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck16_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_16]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck4780 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4780 := by decide +kernel

theorem rowCheck4780 : row4780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4780 := by decide +kernel

theorem rowEval4780 (x : Key → ℝ) : Integer.Sparse.eval row4780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4780, Integer.Sparse.eval_collectBalanced, rawRowCheck4780]

theorem rawRowCheck4781 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4781 := by decide +kernel

theorem rowCheck4781 : row4781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4781 := by decide +kernel

theorem rowEval4781 (x : Key → ℝ) : Integer.Sparse.eval row4781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4781, Integer.Sparse.eval_collectBalanced, rawRowCheck4781]

theorem rawRowCheck4782 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4782 := by decide +kernel

theorem rowCheck4782 : row4782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4782 := by decide +kernel

theorem rowEval4782 (x : Key → ℝ) : Integer.Sparse.eval row4782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4782, Integer.Sparse.eval_collectBalanced, rawRowCheck4782]

theorem rawRowCheck4783 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4783 := by decide +kernel

theorem rowCheck4783 : row4783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4783 := by decide +kernel

theorem rowEval4783 (x : Key → ℝ) : Integer.Sparse.eval row4783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4783, Integer.Sparse.eval_collectBalanced, rawRowCheck4783]

theorem rawRowCheck4784 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4784 := by decide +kernel

theorem rowCheck4784 : row4784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4784 := by decide +kernel

theorem rowEval4784 (x : Key → ℝ) : Integer.Sparse.eval row4784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4784, Integer.Sparse.eval_collectBalanced, rawRowCheck4784]

theorem rawRowCheck4785 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4785 := by decide +kernel

theorem rowCheck4785 : row4785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4785 := by decide +kernel

theorem rowEval4785 (x : Key → ℝ) : Integer.Sparse.eval row4785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4785, Integer.Sparse.eval_collectBalanced, rawRowCheck4785]

theorem rawRowCheck4786 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4786 := by decide +kernel

theorem rowCheck4786 : row4786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4786 := by decide +kernel

theorem rowEval4786 (x : Key → ℝ) : Integer.Sparse.eval row4786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4786, Integer.Sparse.eval_collectBalanced, rawRowCheck4786]

theorem rawRowCheck4787 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4787 := by decide +kernel

theorem rowCheck4787 : row4787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4787 := by decide +kernel

theorem rowEval4787 (x : Key → ℝ) : Integer.Sparse.eval row4787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4787, Integer.Sparse.eval_collectBalanced, rawRowCheck4787]

theorem rawRowCheck4788 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4788 := by decide +kernel

theorem rowCheck4788 : row4788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4788 := by decide +kernel

theorem rowEval4788 (x : Key → ℝ) : Integer.Sparse.eval row4788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4788, Integer.Sparse.eval_collectBalanced, rawRowCheck4788]

theorem rawRowCheck4789 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4789 := by decide +kernel

theorem rowCheck4789 : row4789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4789 := by decide +kernel

theorem rowEval4789 (x : Key → ℝ) : Integer.Sparse.eval row4789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4789, Integer.Sparse.eval_collectBalanced, rawRowCheck4789]

theorem rawRowCheck4790 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4790 := by decide +kernel

theorem rowCheck4790 : row4790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4790 := by decide +kernel

theorem rowEval4790 (x : Key → ℝ) : Integer.Sparse.eval row4790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4790, Integer.Sparse.eval_collectBalanced, rawRowCheck4790]

theorem rawRowCheck4791 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4791 := by decide +kernel

theorem rowCheck4791 : row4791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4791 := by decide +kernel

theorem rowEval4791 (x : Key → ℝ) : Integer.Sparse.eval row4791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4791, Integer.Sparse.eval_collectBalanced, rawRowCheck4791]

theorem rawRowCheck4792 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4792 := by decide +kernel

theorem rowCheck4792 : row4792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4792 := by decide +kernel

theorem rowEval4792 (x : Key → ℝ) : Integer.Sparse.eval row4792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4792, Integer.Sparse.eval_collectBalanced, rawRowCheck4792]

theorem rawRowCheck4793 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4793 := by decide +kernel

theorem rowCheck4793 : row4793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4793 := by decide +kernel

theorem rowEval4793 (x : Key → ℝ) : Integer.Sparse.eval row4793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4793, Integer.Sparse.eval_collectBalanced, rawRowCheck4793]

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

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval4780 x
  · exact rowEval4781 x
  · exact rowEval4782 x
  · exact rowEval4783 x
  · exact rowEval4784 x
  · exact rowEval4785 x
  · exact rowEval4786 x
  · exact rowEval4787 x
  · exact rowEval4788 x
  · exact rowEval4789 x
  · exact rowEval4790 x
  · exact rowEval4791 x
  · exact rowEval4792 x
  · exact rowEval4793 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5058 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5058 := by decide +kernel

theorem rowCheck5058 : row5058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5058 := by decide +kernel

theorem rowEval5058 (x : Key → ℝ) : Integer.Sparse.eval row5058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5058, Integer.Sparse.eval_collectBalanced, rawRowCheck5058]

theorem rawRowCheck5059 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5059 := by decide +kernel

theorem rowCheck5059 : row5059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5059 := by decide +kernel

theorem rowEval5059 (x : Key → ℝ) : Integer.Sparse.eval row5059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5059, Integer.Sparse.eval_collectBalanced, rawRowCheck5059]

theorem rawRowCheck5060 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5060 := by decide +kernel

theorem rowCheck5060 : row5060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5060 := by decide +kernel

theorem rowEval5060 (x : Key → ℝ) : Integer.Sparse.eval row5060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5060, Integer.Sparse.eval_collectBalanced, rawRowCheck5060]

theorem rawRowCheck5061 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5061 := by decide +kernel

theorem rowCheck5061 : row5061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5061 := by decide +kernel

theorem rowEval5061 (x : Key → ℝ) : Integer.Sparse.eval row5061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5061, Integer.Sparse.eval_collectBalanced, rawRowCheck5061]

theorem rawRowCheck5062 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5062 := by decide +kernel

theorem rowCheck5062 : row5062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5062 := by decide +kernel

theorem rowEval5062 (x : Key → ℝ) : Integer.Sparse.eval row5062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5062, Integer.Sparse.eval_collectBalanced, rawRowCheck5062]

theorem rawRowCheck5063 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5063 := by decide +kernel

theorem rowCheck5063 : row5063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5063 := by decide +kernel

theorem rowEval5063 (x : Key → ℝ) : Integer.Sparse.eval row5063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5063, Integer.Sparse.eval_collectBalanced, rawRowCheck5063]

theorem rawRowCheck5064 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5064 := by decide +kernel

theorem rowCheck5064 : row5064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5064 := by decide +kernel

theorem rowEval5064 (x : Key → ℝ) : Integer.Sparse.eval row5064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5064, Integer.Sparse.eval_collectBalanced, rawRowCheck5064]

theorem rawRowCheck5065 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5065 := by decide +kernel

theorem rowCheck5065 : row5065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5065 := by decide +kernel

theorem rowEval5065 (x : Key → ℝ) : Integer.Sparse.eval row5065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5065, Integer.Sparse.eval_collectBalanced, rawRowCheck5065]

theorem rawRowCheck5066 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5066 := by decide +kernel

theorem rowCheck5066 : row5066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5066 := by decide +kernel

theorem rowEval5066 (x : Key → ℝ) : Integer.Sparse.eval row5066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5066, Integer.Sparse.eval_collectBalanced, rawRowCheck5066]

theorem rawRowCheck5067 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5067 := by decide +kernel

theorem rowCheck5067 : row5067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5067 := by decide +kernel

theorem rowEval5067 (x : Key → ℝ) : Integer.Sparse.eval row5067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5067, Integer.Sparse.eval_collectBalanced, rawRowCheck5067]

theorem rawRowCheck5068 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5068 := by decide +kernel

theorem rowCheck5068 : row5068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5068 := by decide +kernel

theorem rowEval5068 (x : Key → ℝ) : Integer.Sparse.eval row5068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5068, Integer.Sparse.eval_collectBalanced, rawRowCheck5068]

theorem rawRowCheck5069 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5069 := by decide +kernel

theorem rowCheck5069 : row5069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5069 := by decide +kernel

theorem rowEval5069 (x : Key → ℝ) : Integer.Sparse.eval row5069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5069, Integer.Sparse.eval_collectBalanced, rawRowCheck5069]

theorem rawRowCheck5070 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5070 := by decide +kernel

theorem rowCheck5070 : row5070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5070 := by decide +kernel

theorem rowEval5070 (x : Key → ℝ) : Integer.Sparse.eval row5070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5070, Integer.Sparse.eval_collectBalanced, rawRowCheck5070]

theorem rawRowCheck5071 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5071 := by decide +kernel

theorem rowCheck5071 : row5071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5071 := by decide +kernel

theorem rowEval5071 (x : Key → ℝ) : Integer.Sparse.eval row5071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5071, Integer.Sparse.eval_collectBalanced, rawRowCheck5071]

theorem rawRowCheck5072 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5072 := by decide +kernel

theorem rowCheck5072 : row5072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5072 := by decide +kernel

theorem rowEval5072 (x : Key → ℝ) : Integer.Sparse.eval row5072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5072, Integer.Sparse.eval_collectBalanced, rawRowCheck5072]

theorem rawRowCheck5073 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5073 := by decide +kernel

theorem rowCheck5073 : row5073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5073 := by decide +kernel

theorem rowEval5073 (x : Key → ℝ) : Integer.Sparse.eval row5073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5073, Integer.Sparse.eval_collectBalanced, rawRowCheck5073]

theorem rawRowCheck5074 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5074 := by decide +kernel

theorem rowCheck5074 : row5074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5074 := by decide +kernel

theorem rowEval5074 (x : Key → ℝ) : Integer.Sparse.eval row5074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5074, Integer.Sparse.eval_collectBalanced, rawRowCheck5074]

theorem rawRowCheck5075 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5075 := by decide +kernel

theorem rowCheck5075 : row5075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5075 := by decide +kernel

theorem rowEval5075 (x : Key → ℝ) : Integer.Sparse.eval row5075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5075, Integer.Sparse.eval_collectBalanced, rawRowCheck5075]

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

theorem entryCheck20_16 : entry20_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_16 k)) := by decide +kernel

theorem rowsSound20_16 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval5058 x
  · exact rowEval5059 x
  · exact rowEval5060 x
  · exact rowEval5061 x
  · exact rowEval5062 x
  · exact rowEval5063 x
  · exact rowEval5064 x
  · exact rowEval5065 x
  · exact rowEval5066 x
  · exact rowEval5067 x
  · exact rowEval5068 x
  · exact rowEval5069 x
  · exact rowEval5070 x
  · exact rowEval5071 x
  · exact rowEval5072 x
  · exact rowEval5073 x
  · exact rowEval5074 x
  · exact rowEval5075 x

theorem entryEval20_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_16 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck20_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_16]

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

theorem entryEvalRow16_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 16 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 16).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval16_0_e B hB
  · exact entryEval16_1 B hB
  · exact entryEval16_2_e B hB
  · exact entryEval16_3 B hB
  · exact entryEval16_4 B hB
  · exact entryEval16_5 B hB
  · exact entryEval16_6 B hB
  · exact entryEval16_7_e B hB
  · exact entryEval16_8 B hB
  · exact entryEval16_9_e B hB
  · exact entryEval16_10 B hB
  · exact entryEval16_11 B hB
  · exact entryEval16_12 B hB
  · exact entryEval16_13 B hB
  · exact entryEval16_14 B hB
  · exact entryEval16_15_e B hB
  · exact entryEval16_16 B hB
  · exact (entryEval17_16_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_16_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_16 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e_oai
