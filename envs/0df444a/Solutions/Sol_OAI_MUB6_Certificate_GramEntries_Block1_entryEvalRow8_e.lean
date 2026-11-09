-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:46:42.466141+00:00
-- url     : https://prove2.me/submissions/9435d24f-5fec-4b74-8a73-7346512816e2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E016
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E020
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_8_e

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

theorem rawRowCheck1704 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1704 := by decide +kernel

theorem rowCheck1704 : row1704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1704 := by decide +kernel

theorem rowEval1704 (x : Key → ℝ) : Integer.Sparse.eval row1704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1704, Integer.Sparse.eval_collectBalanced, rawRowCheck1704]

theorem rawRowCheck1705 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1705 := by decide +kernel

theorem rowCheck1705 : row1705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1705 := by decide +kernel

theorem rowEval1705 (x : Key → ℝ) : Integer.Sparse.eval row1705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1705, Integer.Sparse.eval_collectBalanced, rawRowCheck1705]

theorem rawRowCheck1706 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1706 := by decide +kernel

theorem rowCheck1706 : row1706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1706 := by decide +kernel

theorem rowEval1706 (x : Key → ℝ) : Integer.Sparse.eval row1706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1706, Integer.Sparse.eval_collectBalanced, rawRowCheck1706]

theorem rawRowCheck1713 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8 = rawRow1713 := by decide +kernel

theorem rowCheck1713 : row1713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1713 := by decide +kernel

theorem rowEval1713 (x : Key → ℝ) : Integer.Sparse.eval row1713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1713, Integer.Sparse.eval_collectBalanced, rawRowCheck1713]

theorem rawRowCheck1714 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8 = rawRow1714 := by decide +kernel

theorem rowCheck1714 : row1714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1714 := by decide +kernel

theorem rowEval1714 (x : Key → ℝ) : Integer.Sparse.eval row1714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1714, Integer.Sparse.eval_collectBalanced, rawRowCheck1714]

theorem rawRowCheck1715 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8 = rawRow1715 := by decide +kernel

theorem rowCheck1715 : row1715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1715 := by decide +kernel

theorem rowEval1715 (x : Key → ℝ) : Integer.Sparse.eval row1715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1715, Integer.Sparse.eval_collectBalanced, rawRowCheck1715]

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

theorem rawRowCheck1876 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form8 = rawRow1876 := by decide +kernel

theorem rowCheck1876 : row1876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1876 := by decide +kernel

theorem rowEval1876 (x : Key → ℝ) : Integer.Sparse.eval row1876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1876, Integer.Sparse.eval_collectBalanced, rawRowCheck1876]

theorem rawRowCheck1877 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form8 = rawRow1877 := by decide +kernel

theorem rowCheck1877 : row1877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1877 := by decide +kernel

theorem rowEval1877 (x : Key → ℝ) : Integer.Sparse.eval row1877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1877, Integer.Sparse.eval_collectBalanced, rawRowCheck1877]

theorem rawRowCheck1878 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form8 = rawRow1878 := by decide +kernel

theorem rowCheck1878 : row1878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1878 := by decide +kernel

theorem rowEval1878 (x : Key → ℝ) : Integer.Sparse.eval row1878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1878, Integer.Sparse.eval_collectBalanced, rawRowCheck1878]

theorem rawRowCheck1879 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1879 := by decide +kernel

theorem rowCheck1879 : row1879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1879 := by decide +kernel

theorem rowEval1879 (x : Key → ℝ) : Integer.Sparse.eval row1879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1879, Integer.Sparse.eval_collectBalanced, rawRowCheck1879]

theorem rawRowCheck1880 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form8 = rawRow1880 := by decide +kernel

theorem rowCheck1880 : row1880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1880 := by decide +kernel

theorem rowEval1880 (x : Key → ℝ) : Integer.Sparse.eval row1880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck1880, Integer.Sparse.eval_collectBalanced, rawRowCheck1880]

theorem rawRowCheck1881 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form8 = rawRow1881 := by decide +kernel

theorem rowCheck1881 : row1881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1881 := by decide +kernel

theorem rowEval1881 (x : Key → ℝ) : Integer.Sparse.eval row1881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1881, Integer.Sparse.eval_collectBalanced, rawRowCheck1881]

theorem rawRowCheck1882 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form8 = rawRow1882 := by decide +kernel

theorem rowCheck1882 : row1882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1882 := by decide +kernel

theorem rowEval1882 (x : Key → ℝ) : Integer.Sparse.eval row1882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1882, Integer.Sparse.eval_collectBalanced, rawRowCheck1882]

theorem rawRowCheck1883 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1883 := by decide +kernel

theorem rowCheck1883 : row1883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1883 := by decide +kernel

theorem rowEval1883 (x : Key → ℝ) : Integer.Sparse.eval row1883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1883, Integer.Sparse.eval_collectBalanced, rawRowCheck1883]

theorem rawRowCheck1884 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1884 := by decide +kernel

theorem rowCheck1884 : row1884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1884 := by decide +kernel

theorem rowEval1884 (x : Key → ℝ) : Integer.Sparse.eval row1884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1884, Integer.Sparse.eval_collectBalanced, rawRowCheck1884]

theorem rawRowCheck1885 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1885 := by decide +kernel

theorem rowCheck1885 : row1885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1885 := by decide +kernel

theorem rowEval1885 (x : Key → ℝ) : Integer.Sparse.eval row1885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1885, Integer.Sparse.eval_collectBalanced, rawRowCheck1885]

theorem rawRowCheck1886 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1886 := by decide +kernel

theorem rowCheck1886 : row1886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1886 := by decide +kernel

theorem rowEval1886 (x : Key → ℝ) : Integer.Sparse.eval row1886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1886, Integer.Sparse.eval_collectBalanced, rawRowCheck1886]

theorem rawRowCheck1887 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1887 := by decide +kernel

theorem rowCheck1887 : row1887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1887 := by decide +kernel

theorem rowEval1887 (x : Key → ℝ) : Integer.Sparse.eval row1887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1887, Integer.Sparse.eval_collectBalanced, rawRowCheck1887]

theorem rawRowCheck1888 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1888 := by decide +kernel

theorem rowCheck1888 : row1888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1888 := by decide +kernel

theorem rowEval1888 (x : Key → ℝ) : Integer.Sparse.eval row1888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1888, Integer.Sparse.eval_collectBalanced, rawRowCheck1888]

theorem rawRowCheck1889 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1889 := by decide +kernel

theorem rowCheck1889 : row1889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1889 := by decide +kernel

theorem rowEval1889 (x : Key → ℝ) : Integer.Sparse.eval row1889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1889, Integer.Sparse.eval_collectBalanced, rawRowCheck1889]

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

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval1876 x
  · exact rowEval1877 x
  · exact rowEval1878 x
  · exact rowEval1879 x
  · exact rowEval1880 x
  · exact rowEval1881 x
  · exact rowEval1882 x
  · exact rowEval1883 x
  · exact rowEval1884 x
  · exact rowEval1885 x
  · exact rowEval1886 x
  · exact rowEval1887 x
  · exact rowEval1888 x
  · exact rowEval1889 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

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

theorem rawRowCheck2030 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2030 := by decide +kernel

theorem rowCheck2030 : row2030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2030 := by decide +kernel

theorem rowEval2030 (x : Key → ℝ) : Integer.Sparse.eval row2030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2030, Integer.Sparse.eval_collectBalanced, rawRowCheck2030]

theorem rawRowCheck2031 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2031 := by decide +kernel

theorem rowCheck2031 : row2031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2031 := by decide +kernel

theorem rowEval2031 (x : Key → ℝ) : Integer.Sparse.eval row2031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2031, Integer.Sparse.eval_collectBalanced, rawRowCheck2031]

theorem rawRowCheck2032 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2032 := by decide +kernel

theorem rowCheck2032 : row2032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2032 := by decide +kernel

theorem rowEval2032 (x : Key → ℝ) : Integer.Sparse.eval row2032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2032, Integer.Sparse.eval_collectBalanced, rawRowCheck2032]

theorem rawRowCheck2033 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2033 := by decide +kernel

theorem rowCheck2033 : row2033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2033 := by decide +kernel

theorem rowEval2033 (x : Key → ℝ) : Integer.Sparse.eval row2033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2033, Integer.Sparse.eval_collectBalanced, rawRowCheck2033]

theorem rawRowCheck2034 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2034 := by decide +kernel

theorem rowCheck2034 : row2034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2034 := by decide +kernel

theorem rowEval2034 (x : Key → ℝ) : Integer.Sparse.eval row2034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2034, Integer.Sparse.eval_collectBalanced, rawRowCheck2034]

theorem rawRowCheck2035 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2035 := by decide +kernel

theorem rowCheck2035 : row2035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2035 := by decide +kernel

theorem rowEval2035 (x : Key → ℝ) : Integer.Sparse.eval row2035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2035, Integer.Sparse.eval_collectBalanced, rawRowCheck2035]

theorem rawRowCheck2036 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2036 := by decide +kernel

theorem rowCheck2036 : row2036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2036 := by decide +kernel

theorem rowEval2036 (x : Key → ℝ) : Integer.Sparse.eval row2036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2036, Integer.Sparse.eval_collectBalanced, rawRowCheck2036]

theorem rawRowCheck2037 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8 = rawRow2037 := by decide +kernel

theorem rowCheck2037 : row2037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2037 := by decide +kernel

theorem rowEval2037 (x : Key → ℝ) : Integer.Sparse.eval row2037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2037, Integer.Sparse.eval_collectBalanced, rawRowCheck2037]

theorem rawRowCheck2038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8 = rawRow2038 := by decide +kernel

theorem rowCheck2038 : row2038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2038 := by decide +kernel

theorem rowEval2038 (x : Key → ℝ) : Integer.Sparse.eval row2038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2038, Integer.Sparse.eval_collectBalanced, rawRowCheck2038]

theorem rawRowCheck2039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8 = rawRow2039 := by decide +kernel

theorem rowCheck2039 : row2039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2039 := by decide +kernel

theorem rowEval2039 (x : Key → ℝ) : Integer.Sparse.eval row2039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2039, Integer.Sparse.eval_collectBalanced, rawRowCheck2039]

theorem rawRowCheck2040 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2040 := by decide +kernel

theorem rowCheck2040 : row2040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2040 := by decide +kernel

theorem rowEval2040 (x : Key → ℝ) : Integer.Sparse.eval row2040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2040, Integer.Sparse.eval_collectBalanced, rawRowCheck2040]

theorem rawRowCheck2041 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow2041 := by decide +kernel

theorem rowCheck2041 : row2041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2041 := by decide +kernel

theorem rowEval2041 (x : Key → ℝ) : Integer.Sparse.eval row2041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2041, Integer.Sparse.eval_collectBalanced, rawRowCheck2041]

theorem rawRowCheck2042 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow2042 := by decide +kernel

theorem rowCheck2042 : row2042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2042 := by decide +kernel

theorem rowEval2042 (x : Key → ℝ) : Integer.Sparse.eval row2042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2042, Integer.Sparse.eval_collectBalanced, rawRowCheck2042]

theorem rawRowCheck2043 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow2043 := by decide +kernel

theorem rowCheck2043 : row2043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2043 := by decide +kernel

theorem rowEval2043 (x : Key → ℝ) : Integer.Sparse.eval row2043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2043, Integer.Sparse.eval_collectBalanced, rawRowCheck2043]

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

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2030 x
  · exact rowEval2031 x
  · exact rowEval2032 x
  · exact rowEval2033 x
  · exact rowEval2034 x
  · exact rowEval2035 x
  · exact rowEval2036 x
  · exact rowEval2037 x
  · exact rowEval2038 x
  · exact rowEval2039 x
  · exact rowEval2040 x
  · exact rowEval2041 x
  · exact rowEval2042 x
  · exact rowEval2043 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck2329 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form8 = rawRow2329 := by decide +kernel

theorem rowCheck2329 : row2329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2329 := by decide +kernel

theorem rowEval2329 (x : Key → ℝ) : Integer.Sparse.eval row2329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2329, Integer.Sparse.eval_collectBalanced, rawRowCheck2329]

theorem rawRowCheck2330 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form8 = rawRow2330 := by decide +kernel

theorem rowCheck2330 : row2330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2330 := by decide +kernel

theorem rowEval2330 (x : Key → ℝ) : Integer.Sparse.eval row2330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2330, Integer.Sparse.eval_collectBalanced, rawRowCheck2330]

theorem rawRowCheck2331 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form8 = rawRow2331 := by decide +kernel

theorem rowCheck2331 : row2331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2331 := by decide +kernel

theorem rowEval2331 (x : Key → ℝ) : Integer.Sparse.eval row2331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2331, Integer.Sparse.eval_collectBalanced, rawRowCheck2331]

theorem rawRowCheck2332 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form8 = rawRow2332 := by decide +kernel

theorem rowCheck2332 : row2332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2332 := by decide +kernel

theorem rowEval2332 (x : Key → ℝ) : Integer.Sparse.eval row2332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2332, Integer.Sparse.eval_collectBalanced, rawRowCheck2332]

theorem rawRowCheck2333 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form8 = rawRow2333 := by decide +kernel

theorem rowCheck2333 : row2333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2333 := by decide +kernel

theorem rowEval2333 (x : Key → ℝ) : Integer.Sparse.eval row2333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2333, Integer.Sparse.eval_collectBalanced, rawRowCheck2333]

theorem rawRowCheck2334 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form8 = rawRow2334 := by decide +kernel

theorem rowCheck2334 : row2334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2334 := by decide +kernel

theorem rowEval2334 (x : Key → ℝ) : Integer.Sparse.eval row2334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2334, Integer.Sparse.eval_collectBalanced, rawRowCheck2334]

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

theorem rawRowCheck2338 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8 = rawRow2338 := by decide +kernel

theorem rowCheck2338 : row2338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2338 := by decide +kernel

theorem rowEval2338 (x : Key → ℝ) : Integer.Sparse.eval row2338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2338, Integer.Sparse.eval_collectBalanced, rawRowCheck2338]

theorem rawRowCheck2339 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8 = rawRow2339 := by decide +kernel

theorem rowCheck2339 : row2339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2339 := by decide +kernel

theorem rowEval2339 (x : Key → ℝ) : Integer.Sparse.eval row2339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2339, Integer.Sparse.eval_collectBalanced, rawRowCheck2339]

theorem rawRowCheck2340 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8 = rawRow2340 := by decide +kernel

theorem rowCheck2340 : row2340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2340 := by decide +kernel

theorem rowEval2340 (x : Key → ℝ) : Integer.Sparse.eval row2340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2340, Integer.Sparse.eval_collectBalanced, rawRowCheck2340]

theorem rawRowCheck2341 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8 = rawRow2341 := by decide +kernel

theorem rowCheck2341 : row2341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2341 := by decide +kernel

theorem rowEval2341 (x : Key → ℝ) : Integer.Sparse.eval row2341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2341, Integer.Sparse.eval_collectBalanced, rawRowCheck2341]

theorem rawRowCheck2342 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8 = rawRow2342 := by decide +kernel

theorem rowCheck2342 : row2342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2342 := by decide +kernel

theorem rowEval2342 (x : Key → ℝ) : Integer.Sparse.eval row2342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2342, Integer.Sparse.eval_collectBalanced, rawRowCheck2342]

theorem rawRowCheck2343 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8 = rawRow2343 := by decide +kernel

theorem rowCheck2343 : row2343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2343 := by decide +kernel

theorem rowEval2343 (x : Key → ℝ) : Integer.Sparse.eval row2343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2343, Integer.Sparse.eval_collectBalanced, rawRowCheck2343]

theorem rawRowCheck2344 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form8 = rawRow2344 := by decide +kernel

theorem rowCheck2344 : row2344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2344 := by decide +kernel

theorem rowEval2344 (x : Key → ℝ) : Integer.Sparse.eval row2344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2344, Integer.Sparse.eval_collectBalanced, rawRowCheck2344]

theorem rawRowCheck2345 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form8 = rawRow2345 := by decide +kernel

theorem rowCheck2345 : row2345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2345 := by decide +kernel

theorem rowEval2345 (x : Key → ℝ) : Integer.Sparse.eval row2345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2345, Integer.Sparse.eval_collectBalanced, rawRowCheck2345]

theorem rawRowCheck2346 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form8 = rawRow2346 := by decide +kernel

theorem rowCheck2346 : row2346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2346 := by decide +kernel

theorem rowEval2346 (x : Key → ℝ) : Integer.Sparse.eval row2346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2346, Integer.Sparse.eval_collectBalanced, rawRowCheck2346]

theorem rawRowCheck2347 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form8 = rawRow2347 := by decide +kernel

theorem rowCheck2347 : row2347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2347 := by decide +kernel

theorem rowEval2347 (x : Key → ℝ) : Integer.Sparse.eval row2347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2347, Integer.Sparse.eval_collectBalanced, rawRowCheck2347]

theorem rawRowCheck2348 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form8 = rawRow2348 := by decide +kernel

theorem rowCheck2348 : row2348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2348 := by decide +kernel

theorem rowEval2348 (x : Key → ℝ) : Integer.Sparse.eval row2348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2348, Integer.Sparse.eval_collectBalanced, rawRowCheck2348]

theorem rawRowCheck2349 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form8 = rawRow2349 := by decide +kernel

theorem rowCheck2349 : row2349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2349 := by decide +kernel

theorem rowEval2349 (x : Key → ℝ) : Integer.Sparse.eval row2349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2349, Integer.Sparse.eval_collectBalanced, rawRowCheck2349]

theorem rawRowCheck2350 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8 = rawRow2350 := by decide +kernel

theorem rowCheck2350 : row2350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2350 := by decide +kernel

theorem rowEval2350 (x : Key → ℝ) : Integer.Sparse.eval row2350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2350, Integer.Sparse.eval_collectBalanced, rawRowCheck2350]

theorem rawRowCheck2351 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8 = rawRow2351 := by decide +kernel

theorem rowCheck2351 : row2351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2351 := by decide +kernel

theorem rowEval2351 (x : Key → ℝ) : Integer.Sparse.eval row2351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2351, Integer.Sparse.eval_collectBalanced, rawRowCheck2351]

theorem rawRowCheck2352 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8 = rawRow2352 := by decide +kernel

theorem rowCheck2352 : row2352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2352 := by decide +kernel

theorem rowEval2352 (x : Key → ℝ) : Integer.Sparse.eval row2352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2352, Integer.Sparse.eval_collectBalanced, rawRowCheck2352]

theorem rawRowCheck2353 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8 = rawRow2353 := by decide +kernel

theorem rowCheck2353 : row2353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2353 := by decide +kernel

theorem rowEval2353 (x : Key → ℝ) : Integer.Sparse.eval row2353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2353, Integer.Sparse.eval_collectBalanced, rawRowCheck2353]

theorem rawRowCheck2354 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8 = rawRow2354 := by decide +kernel

theorem rowCheck2354 : row2354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2354 := by decide +kernel

theorem rowEval2354 (x : Key → ℝ) : Integer.Sparse.eval row2354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2354, Integer.Sparse.eval_collectBalanced, rawRowCheck2354]

theorem rawRowCheck2355 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8 = rawRow2355 := by decide +kernel

theorem rowCheck2355 : row2355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2355 := by decide +kernel

theorem rowEval2355 (x : Key → ℝ) : Integer.Sparse.eval row2355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2355, Integer.Sparse.eval_collectBalanced, rawRowCheck2355]

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

theorem entryCheck12_8 : entry12_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_8 k)) := by decide +kernel

theorem rowsSound12_8 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2326 x
  · exact rowEval2327 x
  · exact rowEval2328 x
  · exact rowEval2329 x
  · exact rowEval2330 x
  · exact rowEval2331 x
  · exact rowEval2332 x
  · exact rowEval2333 x
  · exact rowEval2334 x
  · exact rowEval2335 x
  · exact rowEval2336 x
  · exact rowEval2337 x
  · exact rowEval2338 x
  · exact rowEval2339 x
  · exact rowEval2340 x
  · exact rowEval2341 x
  · exact rowEval2342 x
  · exact rowEval2343 x
  · exact rowEval2344 x
  · exact rowEval2345 x
  · exact rowEval2346 x
  · exact rowEval2347 x
  · exact rowEval2348 x
  · exact rowEval2349 x
  · exact rowEval2350 x
  · exact rowEval2351 x
  · exact rowEval2352 x
  · exact rowEval2353 x
  · exact rowEval2354 x
  · exact rowEval2355 x

theorem entryEval12_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_8 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck12_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_8]

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

theorem rawRowCheck2588 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2588 := by decide +kernel

theorem rowCheck2588 : row2588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2588 := by decide +kernel

theorem rowEval2588 (x : Key → ℝ) : Integer.Sparse.eval row2588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2588, Integer.Sparse.eval_collectBalanced, rawRowCheck2588]

theorem rawRowCheck2589 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2589 := by decide +kernel

theorem rowCheck2589 : row2589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2589 := by decide +kernel

theorem rowEval2589 (x : Key → ℝ) : Integer.Sparse.eval row2589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2589, Integer.Sparse.eval_collectBalanced, rawRowCheck2589]

theorem rawRowCheck2590 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2590 := by decide +kernel

theorem rowCheck2590 : row2590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2590 := by decide +kernel

theorem rowEval2590 (x : Key → ℝ) : Integer.Sparse.eval row2590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2590, Integer.Sparse.eval_collectBalanced, rawRowCheck2590]

theorem rawRowCheck2591 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2591 := by decide +kernel

theorem rowCheck2591 : row2591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2591 := by decide +kernel

theorem rowEval2591 (x : Key → ℝ) : Integer.Sparse.eval row2591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2591, Integer.Sparse.eval_collectBalanced, rawRowCheck2591]

theorem rawRowCheck2592 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2592 := by decide +kernel

theorem rowCheck2592 : row2592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2592 := by decide +kernel

theorem rowEval2592 (x : Key → ℝ) : Integer.Sparse.eval row2592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2592, Integer.Sparse.eval_collectBalanced, rawRowCheck2592]

theorem rawRowCheck2593 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2593 := by decide +kernel

theorem rowCheck2593 : row2593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2593 := by decide +kernel

theorem rowEval2593 (x : Key → ℝ) : Integer.Sparse.eval row2593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2593, Integer.Sparse.eval_collectBalanced, rawRowCheck2593]

theorem rawRowCheck2594 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2594 := by decide +kernel

theorem rowCheck2594 : row2594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2594 := by decide +kernel

theorem rowEval2594 (x : Key → ℝ) : Integer.Sparse.eval row2594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2594, Integer.Sparse.eval_collectBalanced, rawRowCheck2594]

theorem rawRowCheck2595 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2595 := by decide +kernel

theorem rowCheck2595 : row2595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2595 := by decide +kernel

theorem rowEval2595 (x : Key → ℝ) : Integer.Sparse.eval row2595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2595, Integer.Sparse.eval_collectBalanced, rawRowCheck2595]

theorem rawRowCheck2596 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2596 := by decide +kernel

theorem rowCheck2596 : row2596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2596 := by decide +kernel

theorem rowEval2596 (x : Key → ℝ) : Integer.Sparse.eval row2596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2596, Integer.Sparse.eval_collectBalanced, rawRowCheck2596]

theorem rawRowCheck2597 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2597 := by decide +kernel

theorem rowCheck2597 : row2597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2597 := by decide +kernel

theorem rowEval2597 (x : Key → ℝ) : Integer.Sparse.eval row2597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2597, Integer.Sparse.eval_collectBalanced, rawRowCheck2597]

theorem rawRowCheck2598 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2598 := by decide +kernel

theorem rowCheck2598 : row2598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2598 := by decide +kernel

theorem rowEval2598 (x : Key → ℝ) : Integer.Sparse.eval row2598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2598, Integer.Sparse.eval_collectBalanced, rawRowCheck2598]

theorem rawRowCheck2599 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2599 := by decide +kernel

theorem rowCheck2599 : row2599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2599 := by decide +kernel

theorem rowEval2599 (x : Key → ℝ) : Integer.Sparse.eval row2599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2599, Integer.Sparse.eval_collectBalanced, rawRowCheck2599]

theorem rawRowCheck2600 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2600 := by decide +kernel

theorem rowCheck2600 : row2600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2600 := by decide +kernel

theorem rowEval2600 (x : Key → ℝ) : Integer.Sparse.eval row2600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2600, Integer.Sparse.eval_collectBalanced, rawRowCheck2600]

theorem rawRowCheck2601 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2601 := by decide +kernel

theorem rowCheck2601 : row2601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2601 := by decide +kernel

theorem rowEval2601 (x : Key → ℝ) : Integer.Sparse.eval row2601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2601, Integer.Sparse.eval_collectBalanced, rawRowCheck2601]

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

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2588 x
  · exact rowEval2589 x
  · exact rowEval2590 x
  · exact rowEval2591 x
  · exact rowEval2592 x
  · exact rowEval2593 x
  · exact rowEval2594 x
  · exact rowEval2595 x
  · exact rowEval2596 x
  · exact rowEval2597 x
  · exact rowEval2598 x
  · exact rowEval2599 x
  · exact rowEval2600 x
  · exact rowEval2601 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

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

theorem rawRowCheck2864 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form8 = rawRow2864 := by decide +kernel

theorem rowCheck2864 : row2864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2864 := by decide +kernel

theorem rowEval2864 (x : Key → ℝ) : Integer.Sparse.eval row2864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2864, Integer.Sparse.eval_collectBalanced, rawRowCheck2864]

theorem rawRowCheck2865 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form8 = rawRow2865 := by decide +kernel

theorem rowCheck2865 : row2865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2865 := by decide +kernel

theorem rowEval2865 (x : Key → ℝ) : Integer.Sparse.eval row2865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2865, Integer.Sparse.eval_collectBalanced, rawRowCheck2865]

theorem rawRowCheck2866 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form8 = rawRow2866 := by decide +kernel

theorem rowCheck2866 : row2866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2866 := by decide +kernel

theorem rowEval2866 (x : Key → ℝ) : Integer.Sparse.eval row2866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2866, Integer.Sparse.eval_collectBalanced, rawRowCheck2866]

theorem rawRowCheck2867 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2867 := by decide +kernel

theorem rowCheck2867 : row2867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2867 := by decide +kernel

theorem rowEval2867 (x : Key → ℝ) : Integer.Sparse.eval row2867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2867, Integer.Sparse.eval_collectBalanced, rawRowCheck2867]

theorem rawRowCheck2868 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2868 := by decide +kernel

theorem rowCheck2868 : row2868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2868 := by decide +kernel

theorem rowEval2868 (x : Key → ℝ) : Integer.Sparse.eval row2868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2868, Integer.Sparse.eval_collectBalanced, rawRowCheck2868]

theorem rawRowCheck2869 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2869 := by decide +kernel

theorem rowCheck2869 : row2869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2869 := by decide +kernel

theorem rowEval2869 (x : Key → ℝ) : Integer.Sparse.eval row2869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2869, Integer.Sparse.eval_collectBalanced, rawRowCheck2869]

theorem rawRowCheck2870 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form8 = rawRow2870 := by decide +kernel

theorem rowCheck2870 : row2870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2870 := by decide +kernel

theorem rowEval2870 (x : Key → ℝ) : Integer.Sparse.eval row2870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2870, Integer.Sparse.eval_collectBalanced, rawRowCheck2870]

theorem rawRowCheck2871 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form8 = rawRow2871 := by decide +kernel

theorem rowCheck2871 : row2871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2871 := by decide +kernel

theorem rowEval2871 (x : Key → ℝ) : Integer.Sparse.eval row2871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2871, Integer.Sparse.eval_collectBalanced, rawRowCheck2871]

theorem rawRowCheck2872 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form8 = rawRow2872 := by decide +kernel

theorem rowCheck2872 : row2872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2872 := by decide +kernel

theorem rowEval2872 (x : Key → ℝ) : Integer.Sparse.eval row2872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2872, Integer.Sparse.eval_collectBalanced, rawRowCheck2872]

theorem rawRowCheck2873 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form8 = rawRow2873 := by decide +kernel

theorem rowCheck2873 : row2873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2873 := by decide +kernel

theorem rowEval2873 (x : Key → ℝ) : Integer.Sparse.eval row2873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2873, Integer.Sparse.eval_collectBalanced, rawRowCheck2873]

theorem rawRowCheck2874 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form8 = rawRow2874 := by decide +kernel

theorem rowCheck2874 : row2874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2874 := by decide +kernel

theorem rowEval2874 (x : Key → ℝ) : Integer.Sparse.eval row2874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2874, Integer.Sparse.eval_collectBalanced, rawRowCheck2874]

theorem rawRowCheck2875 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form8 = rawRow2875 := by decide +kernel

theorem rowCheck2875 : row2875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2875 := by decide +kernel

theorem rowEval2875 (x : Key → ℝ) : Integer.Sparse.eval row2875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2875, Integer.Sparse.eval_collectBalanced, rawRowCheck2875]

theorem rawRowCheck2876 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form8 = rawRow2876 := by decide +kernel

theorem rowCheck2876 : row2876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2876 := by decide +kernel

theorem rowEval2876 (x : Key → ℝ) : Integer.Sparse.eval row2876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2876, Integer.Sparse.eval_collectBalanced, rawRowCheck2876]

theorem rawRowCheck2877 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form8 = rawRow2877 := by decide +kernel

theorem rowCheck2877 : row2877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2877 := by decide +kernel

theorem rowEval2877 (x : Key → ℝ) : Integer.Sparse.eval row2877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2877, Integer.Sparse.eval_collectBalanced, rawRowCheck2877]

theorem rawRowCheck2878 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form8 = rawRow2878 := by decide +kernel

theorem rowCheck2878 : row2878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2878 := by decide +kernel

theorem rowEval2878 (x : Key → ℝ) : Integer.Sparse.eval row2878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2878, Integer.Sparse.eval_collectBalanced, rawRowCheck2878]

theorem rawRowCheck2879 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2879 := by decide +kernel

theorem rowCheck2879 : row2879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2879 := by decide +kernel

theorem rowEval2879 (x : Key → ℝ) : Integer.Sparse.eval row2879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2879, Integer.Sparse.eval_collectBalanced, rawRowCheck2879]

theorem rawRowCheck2880 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2880 := by decide +kernel

theorem rowCheck2880 : row2880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2880 := by decide +kernel

theorem rowEval2880 (x : Key → ℝ) : Integer.Sparse.eval row2880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2880, Integer.Sparse.eval_collectBalanced, rawRowCheck2880]

theorem rawRowCheck2881 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2881 := by decide +kernel

theorem rowCheck2881 : row2881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2881 := by decide +kernel

theorem rowEval2881 (x : Key → ℝ) : Integer.Sparse.eval row2881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2881, Integer.Sparse.eval_collectBalanced, rawRowCheck2881]

theorem rawRowCheck2882 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form8 = rawRow2882 := by decide +kernel

theorem rowCheck2882 : row2882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2882 := by decide +kernel

theorem rowEval2882 (x : Key → ℝ) : Integer.Sparse.eval row2882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2882, Integer.Sparse.eval_collectBalanced, rawRowCheck2882]

theorem rawRowCheck2883 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form8 = rawRow2883 := by decide +kernel

theorem rowCheck2883 : row2883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2883 := by decide +kernel

theorem rowEval2883 (x : Key → ℝ) : Integer.Sparse.eval row2883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2883, Integer.Sparse.eval_collectBalanced, rawRowCheck2883]

theorem rawRowCheck2884 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form8 = rawRow2884 := by decide +kernel

theorem rowCheck2884 : row2884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2884 := by decide +kernel

theorem rowEval2884 (x : Key → ℝ) : Integer.Sparse.eval row2884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2884, Integer.Sparse.eval_collectBalanced, rawRowCheck2884]

theorem rawRowCheck2885 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form8 = rawRow2885 := by decide +kernel

theorem rowCheck2885 : row2885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2885 := by decide +kernel

theorem rowEval2885 (x : Key → ℝ) : Integer.Sparse.eval row2885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2885, Integer.Sparse.eval_collectBalanced, rawRowCheck2885]

theorem rawRowCheck2886 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form8 = rawRow2886 := by decide +kernel

theorem rowCheck2886 : row2886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2886 := by decide +kernel

theorem rowEval2886 (x : Key → ℝ) : Integer.Sparse.eval row2886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2886, Integer.Sparse.eval_collectBalanced, rawRowCheck2886]

theorem rawRowCheck2887 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form8 = rawRow2887 := by decide +kernel

theorem rowCheck2887 : row2887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2887 := by decide +kernel

theorem rowEval2887 (x : Key → ℝ) : Integer.Sparse.eval row2887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck2887, Integer.Sparse.eval_collectBalanced, rawRowCheck2887]

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

theorem entryCheck14_8 : entry14_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_8 k)) := by decide +kernel

theorem rowsSound14_8 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2864 x
  · exact rowEval2865 x
  · exact rowEval2866 x
  · exact rowEval2867 x
  · exact rowEval2868 x
  · exact rowEval2869 x
  · exact rowEval2870 x
  · exact rowEval2871 x
  · exact rowEval2872 x
  · exact rowEval2873 x
  · exact rowEval2874 x
  · exact rowEval2875 x
  · exact rowEval2876 x
  · exact rowEval2877 x
  · exact rowEval2878 x
  · exact rowEval2879 x
  · exact rowEval2880 x
  · exact rowEval2881 x
  · exact rowEval2882 x
  · exact rowEval2883 x
  · exact rowEval2884 x
  · exact rowEval2885 x
  · exact rowEval2886 x
  · exact rowEval2887 x

theorem entryEval14_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_8 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck14_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_8]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

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

theorem rawRowCheck4668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4668 := by decide +kernel

theorem rowCheck4668 : row4668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4668 := by decide +kernel

theorem rowEval4668 (x : Key → ℝ) : Integer.Sparse.eval row4668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4668, Integer.Sparse.eval_collectBalanced, rawRowCheck4668]

theorem rawRowCheck4669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4669 := by decide +kernel

theorem rowCheck4669 : row4669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4669 := by decide +kernel

theorem rowEval4669 (x : Key → ℝ) : Integer.Sparse.eval row4669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4669, Integer.Sparse.eval_collectBalanced, rawRowCheck4669]

theorem rawRowCheck4670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4670 := by decide +kernel

theorem rowCheck4670 : row4670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4670 := by decide +kernel

theorem rowEval4670 (x : Key → ℝ) : Integer.Sparse.eval row4670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4670, Integer.Sparse.eval_collectBalanced, rawRowCheck4670]

theorem rawRowCheck4671 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4671 := by decide +kernel

theorem rowCheck4671 : row4671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4671 := by decide +kernel

theorem rowEval4671 (x : Key → ℝ) : Integer.Sparse.eval row4671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4671, Integer.Sparse.eval_collectBalanced, rawRowCheck4671]

theorem rawRowCheck4672 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4672 := by decide +kernel

theorem rowCheck4672 : row4672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4672 := by decide +kernel

theorem rowEval4672 (x : Key → ℝ) : Integer.Sparse.eval row4672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4672, Integer.Sparse.eval_collectBalanced, rawRowCheck4672]

theorem rawRowCheck4673 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4673 := by decide +kernel

theorem rowCheck4673 : row4673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4673 := by decide +kernel

theorem rowEval4673 (x : Key → ℝ) : Integer.Sparse.eval row4673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4673, Integer.Sparse.eval_collectBalanced, rawRowCheck4673]

theorem rawRowCheck4674 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4674 := by decide +kernel

theorem rowCheck4674 : row4674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4674 := by decide +kernel

theorem rowEval4674 (x : Key → ℝ) : Integer.Sparse.eval row4674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4674, Integer.Sparse.eval_collectBalanced, rawRowCheck4674]

theorem rawRowCheck4675 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4675 := by decide +kernel

theorem rowCheck4675 : row4675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4675 := by decide +kernel

theorem rowEval4675 (x : Key → ℝ) : Integer.Sparse.eval row4675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4675, Integer.Sparse.eval_collectBalanced, rawRowCheck4675]

theorem rawRowCheck4676 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4676 := by decide +kernel

theorem rowCheck4676 : row4676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4676 := by decide +kernel

theorem rowEval4676 (x : Key → ℝ) : Integer.Sparse.eval row4676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4676, Integer.Sparse.eval_collectBalanced, rawRowCheck4676]

theorem rawRowCheck4677 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4677 := by decide +kernel

theorem rowCheck4677 : row4677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4677 := by decide +kernel

theorem rowEval4677 (x : Key → ℝ) : Integer.Sparse.eval row4677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4677, Integer.Sparse.eval_collectBalanced, rawRowCheck4677]

theorem rawRowCheck4678 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4678 := by decide +kernel

theorem rowCheck4678 : row4678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4678 := by decide +kernel

theorem rowEval4678 (x : Key → ℝ) : Integer.Sparse.eval row4678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4678, Integer.Sparse.eval_collectBalanced, rawRowCheck4678]

theorem rawRowCheck4679 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4679 := by decide +kernel

theorem rowCheck4679 : row4679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4679 := by decide +kernel

theorem rowEval4679 (x : Key → ℝ) : Integer.Sparse.eval row4679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4679, Integer.Sparse.eval_collectBalanced, rawRowCheck4679]

theorem rawRowCheck4680 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4680 := by decide +kernel

theorem rowCheck4680 : row4680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4680 := by decide +kernel

theorem rowEval4680 (x : Key → ℝ) : Integer.Sparse.eval row4680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4680, Integer.Sparse.eval_collectBalanced, rawRowCheck4680]

theorem rawRowCheck4681 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4681 := by decide +kernel

theorem rowCheck4681 : row4681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4681 := by decide +kernel

theorem rowEval4681 (x : Key → ℝ) : Integer.Sparse.eval row4681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4681, Integer.Sparse.eval_collectBalanced, rawRowCheck4681]

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

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4668 x
  · exact rowEval4669 x
  · exact rowEval4670 x
  · exact rowEval4671 x
  · exact rowEval4672 x
  · exact rowEval4673 x
  · exact rowEval4674 x
  · exact rowEval4675 x
  · exact rowEval4676 x
  · exact rowEval4677 x
  · exact rowEval4678 x
  · exact rowEval4679 x
  · exact rowEval4680 x
  · exact rowEval4681 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

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

theorem rawRowCheck1420 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1420 := by decide +kernel

theorem rowCheck1420 : row1420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1420 := by decide +kernel

theorem rowEval1420 (x : Key → ℝ) : Integer.Sparse.eval row1420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1420, Integer.Sparse.eval_collectBalanced, rawRowCheck1420]

theorem rawRowCheck1421 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1421 := by decide +kernel

theorem rowCheck1421 : row1421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1421 := by decide +kernel

theorem rowEval1421 (x : Key → ℝ) : Integer.Sparse.eval row1421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1421, Integer.Sparse.eval_collectBalanced, rawRowCheck1421]

theorem rawRowCheck1422 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1422 := by decide +kernel

theorem rowCheck1422 : row1422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1422 := by decide +kernel

theorem rowEval1422 (x : Key → ℝ) : Integer.Sparse.eval row1422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1422, Integer.Sparse.eval_collectBalanced, rawRowCheck1422]

theorem rawRowCheck1423 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1423 := by decide +kernel

theorem rowCheck1423 : row1423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1423 := by decide +kernel

theorem rowEval1423 (x : Key → ℝ) : Integer.Sparse.eval row1423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1423, Integer.Sparse.eval_collectBalanced, rawRowCheck1423]

theorem rawRowCheck1424 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1424 := by decide +kernel

theorem rowCheck1424 : row1424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1424 := by decide +kernel

theorem rowEval1424 (x : Key → ℝ) : Integer.Sparse.eval row1424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1424, Integer.Sparse.eval_collectBalanced, rawRowCheck1424]

theorem rawRowCheck1425 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1425 := by decide +kernel

theorem rowCheck1425 : row1425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1425 := by decide +kernel

theorem rowEval1425 (x : Key → ℝ) : Integer.Sparse.eval row1425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1425, Integer.Sparse.eval_collectBalanced, rawRowCheck1425]

theorem rawRowCheck1426 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1426 := by decide +kernel

theorem rowCheck1426 : row1426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1426 := by decide +kernel

theorem rowEval1426 (x : Key → ℝ) : Integer.Sparse.eval row1426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1426, Integer.Sparse.eval_collectBalanced, rawRowCheck1426]

theorem rawRowCheck1427 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1427 := by decide +kernel

theorem rowCheck1427 : row1427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1427 := by decide +kernel

theorem rowEval1427 (x : Key → ℝ) : Integer.Sparse.eval row1427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1427, Integer.Sparse.eval_collectBalanced, rawRowCheck1427]

theorem rawRowCheck1428 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1428 := by decide +kernel

theorem rowCheck1428 : row1428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1428 := by decide +kernel

theorem rowEval1428 (x : Key → ℝ) : Integer.Sparse.eval row1428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1428, Integer.Sparse.eval_collectBalanced, rawRowCheck1428]

theorem rawRowCheck1429 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1429 := by decide +kernel

theorem rowCheck1429 : row1429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1429 := by decide +kernel

theorem rowEval1429 (x : Key → ℝ) : Integer.Sparse.eval row1429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1429, Integer.Sparse.eval_collectBalanced, rawRowCheck1429]

theorem rawRowCheck1430 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1430 := by decide +kernel

theorem rowCheck1430 : row1430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1430 := by decide +kernel

theorem rowEval1430 (x : Key → ℝ) : Integer.Sparse.eval row1430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1430, Integer.Sparse.eval_collectBalanced, rawRowCheck1430]

theorem rawRowCheck1431 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1431 := by decide +kernel

theorem rowCheck1431 : row1431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1431 := by decide +kernel

theorem rowEval1431 (x : Key → ℝ) : Integer.Sparse.eval row1431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1431, Integer.Sparse.eval_collectBalanced, rawRowCheck1431]

theorem rawRowCheck1432 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1432 := by decide +kernel

theorem rowCheck1432 : row1432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1432 := by decide +kernel

theorem rowEval1432 (x : Key → ℝ) : Integer.Sparse.eval row1432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1432, Integer.Sparse.eval_collectBalanced, rawRowCheck1432]

theorem rawRowCheck1433 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1433 := by decide +kernel

theorem rowCheck1433 : row1433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1433 := by decide +kernel

theorem rowEval1433 (x : Key → ℝ) : Integer.Sparse.eval row1433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1433, Integer.Sparse.eval_collectBalanced, rawRowCheck1433]

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

theorem rawRowCheck1462 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow1462 := by decide +kernel

theorem rowCheck1462 : row1462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1462 := by decide +kernel

theorem rowEval1462 (x : Key → ℝ) : Integer.Sparse.eval row1462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1462, Integer.Sparse.eval_collectBalanced, rawRowCheck1462]

theorem rawRowCheck1463 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow1463 := by decide +kernel

theorem rowCheck1463 : row1463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1463 := by decide +kernel

theorem rowEval1463 (x : Key → ℝ) : Integer.Sparse.eval row1463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1463, Integer.Sparse.eval_collectBalanced, rawRowCheck1463]

theorem rawRowCheck1464 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow1464 := by decide +kernel

theorem rowCheck1464 : row1464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1464 := by decide +kernel

theorem rowEval1464 (x : Key → ℝ) : Integer.Sparse.eval row1464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1464, Integer.Sparse.eval_collectBalanced, rawRowCheck1464]

theorem rawRowCheck1465 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1465 := by decide +kernel

theorem rowCheck1465 : row1465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1465 := by decide +kernel

theorem rowEval1465 (x : Key → ℝ) : Integer.Sparse.eval row1465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1465, Integer.Sparse.eval_collectBalanced, rawRowCheck1465]

theorem rawRowCheck1466 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8 = rawRow1466 := by decide +kernel

theorem rowCheck1466 : row1466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1466 := by decide +kernel

theorem rowEval1466 (x : Key → ℝ) : Integer.Sparse.eval row1466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck1466, Integer.Sparse.eval_collectBalanced, rawRowCheck1466]

theorem rawRowCheck1467 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8 = rawRow1467 := by decide +kernel

theorem rowCheck1467 : row1467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1467 := by decide +kernel

theorem rowEval1467 (x : Key → ℝ) : Integer.Sparse.eval row1467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1467, Integer.Sparse.eval_collectBalanced, rawRowCheck1467]

theorem rawRowCheck1468 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8 = rawRow1468 := by decide +kernel

theorem rowCheck1468 : row1468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1468 := by decide +kernel

theorem rowEval1468 (x : Key → ℝ) : Integer.Sparse.eval row1468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1468, Integer.Sparse.eval_collectBalanced, rawRowCheck1468]

theorem rawRowCheck1469 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1469 := by decide +kernel

theorem rowCheck1469 : row1469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1469 := by decide +kernel

theorem rowEval1469 (x : Key → ℝ) : Integer.Sparse.eval row1469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1469, Integer.Sparse.eval_collectBalanced, rawRowCheck1469]

theorem rawRowCheck1470 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1470 := by decide +kernel

theorem rowCheck1470 : row1470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1470 := by decide +kernel

theorem rowEval1470 (x : Key → ℝ) : Integer.Sparse.eval row1470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1470, Integer.Sparse.eval_collectBalanced, rawRowCheck1470]

theorem rawRowCheck1471 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1471 := by decide +kernel

theorem rowCheck1471 : row1471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1471 := by decide +kernel

theorem rowEval1471 (x : Key → ℝ) : Integer.Sparse.eval row1471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1471, Integer.Sparse.eval_collectBalanced, rawRowCheck1471]

theorem rawRowCheck1472 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8 = rawRow1472 := by decide +kernel

theorem rowCheck1472 : row1472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1472 := by decide +kernel

theorem rowEval1472 (x : Key → ℝ) : Integer.Sparse.eval row1472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1472, Integer.Sparse.eval_collectBalanced, rawRowCheck1472]

theorem rawRowCheck1473 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8 = rawRow1473 := by decide +kernel

theorem rowCheck1473 : row1473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1473 := by decide +kernel

theorem rowEval1473 (x : Key → ℝ) : Integer.Sparse.eval row1473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1473, Integer.Sparse.eval_collectBalanced, rawRowCheck1473]

theorem rawRowCheck1474 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8 = rawRow1474 := by decide +kernel

theorem rowCheck1474 : row1474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1474 := by decide +kernel

theorem rowEval1474 (x : Key → ℝ) : Integer.Sparse.eval row1474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck1474, Integer.Sparse.eval_collectBalanced, rawRowCheck1474]

theorem rawRowCheck1475 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8 = rawRow1475 := by decide +kernel

theorem rowCheck1475 : row1475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1475 := by decide +kernel

theorem rowEval1475 (x : Key → ℝ) : Integer.Sparse.eval row1475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form8) x := by
  rw [rowCheck1475, Integer.Sparse.eval_collectBalanced, rawRowCheck1475]

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

theorem rawRowCheck4926 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4926 := by decide +kernel

theorem rowCheck4926 : row4926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4926 := by decide +kernel

theorem rowEval4926 (x : Key → ℝ) : Integer.Sparse.eval row4926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4926, Integer.Sparse.eval_collectBalanced, rawRowCheck4926]

theorem rawRowCheck4927 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4927 := by decide +kernel

theorem rowCheck4927 : row4927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4927 := by decide +kernel

theorem rowEval4927 (x : Key → ℝ) : Integer.Sparse.eval row4927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4927, Integer.Sparse.eval_collectBalanced, rawRowCheck4927]

theorem rawRowCheck4928 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4928 := by decide +kernel

theorem rowCheck4928 : row4928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4928 := by decide +kernel

theorem rowEval4928 (x : Key → ℝ) : Integer.Sparse.eval row4928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4928, Integer.Sparse.eval_collectBalanced, rawRowCheck4928]

theorem rawRowCheck4929 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8 = rawRow4929 := by decide +kernel

theorem rowCheck4929 : row4929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4929 := by decide +kernel

theorem rowEval4929 (x : Key → ℝ) : Integer.Sparse.eval row4929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4929, Integer.Sparse.eval_collectBalanced, rawRowCheck4929]

theorem rawRowCheck4930 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8 = rawRow4930 := by decide +kernel

theorem rowCheck4930 : row4930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4930 := by decide +kernel

theorem rowEval4930 (x : Key → ℝ) : Integer.Sparse.eval row4930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4930, Integer.Sparse.eval_collectBalanced, rawRowCheck4930]

theorem rawRowCheck4931 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8 = rawRow4931 := by decide +kernel

theorem rowCheck4931 : row4931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4931 := by decide +kernel

theorem rowEval4931 (x : Key → ℝ) : Integer.Sparse.eval row4931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4931, Integer.Sparse.eval_collectBalanced, rawRowCheck4931]

theorem rawRowCheck4932 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4932 := by decide +kernel

theorem rowCheck4932 : row4932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4932 := by decide +kernel

theorem rowEval4932 (x : Key → ℝ) : Integer.Sparse.eval row4932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4932, Integer.Sparse.eval_collectBalanced, rawRowCheck4932]

theorem rawRowCheck4933 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4933 := by decide +kernel

theorem rowCheck4933 : row4933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4933 := by decide +kernel

theorem rowEval4933 (x : Key → ℝ) : Integer.Sparse.eval row4933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4933, Integer.Sparse.eval_collectBalanced, rawRowCheck4933]

theorem rawRowCheck4934 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4934 := by decide +kernel

theorem rowCheck4934 : row4934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4934 := by decide +kernel

theorem rowEval4934 (x : Key → ℝ) : Integer.Sparse.eval row4934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4934, Integer.Sparse.eval_collectBalanced, rawRowCheck4934]

theorem rawRowCheck4935 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8 = rawRow4935 := by decide +kernel

theorem rowCheck4935 : row4935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4935 := by decide +kernel

theorem rowEval4935 (x : Key → ℝ) : Integer.Sparse.eval row4935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4935, Integer.Sparse.eval_collectBalanced, rawRowCheck4935]

theorem rawRowCheck4936 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8 = rawRow4936 := by decide +kernel

theorem rowCheck4936 : row4936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4936 := by decide +kernel

theorem rowEval4936 (x : Key → ℝ) : Integer.Sparse.eval row4936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4936, Integer.Sparse.eval_collectBalanced, rawRowCheck4936]

theorem rawRowCheck4937 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8 = rawRow4937 := by decide +kernel

theorem rowCheck4937 : row4937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4937 := by decide +kernel

theorem rowEval4937 (x : Key → ℝ) : Integer.Sparse.eval row4937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4937, Integer.Sparse.eval_collectBalanced, rawRowCheck4937]

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

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4926 x
  · exact rowEval4927 x
  · exact rowEval4928 x
  · exact rowEval1704 x
  · exact rowEval1705 x
  · exact rowEval1706 x
  · exact rowEval4929 x
  · exact rowEval4930 x
  · exact rowEval4931 x
  · exact rowEval4932 x
  · exact rowEval4933 x
  · exact rowEval4934 x
  · exact rowEval1713 x
  · exact rowEval1714 x
  · exact rowEval1715 x
  · exact rowEval4935 x
  · exact rowEval4936 x
  · exact rowEval4937 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

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

theorem rawRowCheck1350 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1350 := by decide +kernel

theorem rowCheck1350 : row1350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1350 := by decide +kernel

theorem rowEval1350 (x : Key → ℝ) : Integer.Sparse.eval row1350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1350, Integer.Sparse.eval_collectBalanced, rawRowCheck1350]

theorem rawRowCheck1351 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1351 := by decide +kernel

theorem rowCheck1351 : row1351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1351 := by decide +kernel

theorem rowEval1351 (x : Key → ℝ) : Integer.Sparse.eval row1351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1351, Integer.Sparse.eval_collectBalanced, rawRowCheck1351]

theorem rawRowCheck1352 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1352 := by decide +kernel

theorem rowCheck1352 : row1352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1352 := by decide +kernel

theorem rowEval1352 (x : Key → ℝ) : Integer.Sparse.eval row1352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1352, Integer.Sparse.eval_collectBalanced, rawRowCheck1352]

theorem rawRowCheck1353 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1353 := by decide +kernel

theorem rowCheck1353 : row1353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1353 := by decide +kernel

theorem rowEval1353 (x : Key → ℝ) : Integer.Sparse.eval row1353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1353, Integer.Sparse.eval_collectBalanced, rawRowCheck1353]

theorem rawRowCheck1354 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1354 := by decide +kernel

theorem rowCheck1354 : row1354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1354 := by decide +kernel

theorem rowEval1354 (x : Key → ℝ) : Integer.Sparse.eval row1354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1354, Integer.Sparse.eval_collectBalanced, rawRowCheck1354]

theorem rawRowCheck1355 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1355 := by decide +kernel

theorem rowCheck1355 : row1355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1355 := by decide +kernel

theorem rowEval1355 (x : Key → ℝ) : Integer.Sparse.eval row1355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1355, Integer.Sparse.eval_collectBalanced, rawRowCheck1355]

theorem rawRowCheck1356 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1356 := by decide +kernel

theorem rowCheck1356 : row1356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1356 := by decide +kernel

theorem rowEval1356 (x : Key → ℝ) : Integer.Sparse.eval row1356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1356, Integer.Sparse.eval_collectBalanced, rawRowCheck1356]

theorem rawRowCheck1357 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1357 := by decide +kernel

theorem rowCheck1357 : row1357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1357 := by decide +kernel

theorem rowEval1357 (x : Key → ℝ) : Integer.Sparse.eval row1357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1357, Integer.Sparse.eval_collectBalanced, rawRowCheck1357]

theorem rawRowCheck1358 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1358 := by decide +kernel

theorem rowCheck1358 : row1358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1358 := by decide +kernel

theorem rowEval1358 (x : Key → ℝ) : Integer.Sparse.eval row1358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1358, Integer.Sparse.eval_collectBalanced, rawRowCheck1358]

theorem rawRowCheck1359 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1359 := by decide +kernel

theorem rowCheck1359 : row1359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1359 := by decide +kernel

theorem rowEval1359 (x : Key → ℝ) : Integer.Sparse.eval row1359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1359, Integer.Sparse.eval_collectBalanced, rawRowCheck1359]

theorem rawRowCheck1360 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1360 := by decide +kernel

theorem rowCheck1360 : row1360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1360 := by decide +kernel

theorem rowEval1360 (x : Key → ℝ) : Integer.Sparse.eval row1360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1360, Integer.Sparse.eval_collectBalanced, rawRowCheck1360]

theorem rawRowCheck1361 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1361 := by decide +kernel

theorem rowCheck1361 : row1361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1361 := by decide +kernel

theorem rowEval1361 (x : Key → ℝ) : Integer.Sparse.eval row1361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1361, Integer.Sparse.eval_collectBalanced, rawRowCheck1361]

theorem rawRowCheck1362 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1362 := by decide +kernel

theorem rowCheck1362 : row1362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1362 := by decide +kernel

theorem rowEval1362 (x : Key → ℝ) : Integer.Sparse.eval row1362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1362, Integer.Sparse.eval_collectBalanced, rawRowCheck1362]

theorem rawRowCheck1363 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1363 := by decide +kernel

theorem rowCheck1363 : row1363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1363 := by decide +kernel

theorem rowEval1363 (x : Key → ℝ) : Integer.Sparse.eval row1363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1363, Integer.Sparse.eval_collectBalanced, rawRowCheck1363]

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

theorem rawRowCheck1378 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1378 := by decide +kernel

theorem rowCheck1378 : row1378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1378 := by decide +kernel

theorem rowEval1378 (x : Key → ℝ) : Integer.Sparse.eval row1378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1378, Integer.Sparse.eval_collectBalanced, rawRowCheck1378]

theorem rawRowCheck1379 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1379 := by decide +kernel

theorem rowCheck1379 : row1379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1379 := by decide +kernel

theorem rowEval1379 (x : Key → ℝ) : Integer.Sparse.eval row1379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1379, Integer.Sparse.eval_collectBalanced, rawRowCheck1379]

theorem rawRowCheck1380 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1380 := by decide +kernel

theorem rowCheck1380 : row1380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1380 := by decide +kernel

theorem rowEval1380 (x : Key → ℝ) : Integer.Sparse.eval row1380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1380, Integer.Sparse.eval_collectBalanced, rawRowCheck1380]

theorem rawRowCheck1381 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1381 := by decide +kernel

theorem rowCheck1381 : row1381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1381 := by decide +kernel

theorem rowEval1381 (x : Key → ℝ) : Integer.Sparse.eval row1381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1381, Integer.Sparse.eval_collectBalanced, rawRowCheck1381]

theorem rawRowCheck1382 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1382 := by decide +kernel

theorem rowCheck1382 : row1382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1382 := by decide +kernel

theorem rowEval1382 (x : Key → ℝ) : Integer.Sparse.eval row1382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1382, Integer.Sparse.eval_collectBalanced, rawRowCheck1382]

theorem rawRowCheck1383 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1383 := by decide +kernel

theorem rowCheck1383 : row1383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1383 := by decide +kernel

theorem rowEval1383 (x : Key → ℝ) : Integer.Sparse.eval row1383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1383, Integer.Sparse.eval_collectBalanced, rawRowCheck1383]

theorem rawRowCheck1384 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1384 := by decide +kernel

theorem rowCheck1384 : row1384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1384 := by decide +kernel

theorem rowEval1384 (x : Key → ℝ) : Integer.Sparse.eval row1384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1384, Integer.Sparse.eval_collectBalanced, rawRowCheck1384]

theorem rawRowCheck1385 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1385 := by decide +kernel

theorem rowCheck1385 : row1385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1385 := by decide +kernel

theorem rowEval1385 (x : Key → ℝ) : Integer.Sparse.eval row1385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1385, Integer.Sparse.eval_collectBalanced, rawRowCheck1385]

theorem rawRowCheck1386 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1386 := by decide +kernel

theorem rowCheck1386 : row1386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1386 := by decide +kernel

theorem rowEval1386 (x : Key → ℝ) : Integer.Sparse.eval row1386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1386, Integer.Sparse.eval_collectBalanced, rawRowCheck1386]

theorem rawRowCheck1387 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1387 := by decide +kernel

theorem rowCheck1387 : row1387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1387 := by decide +kernel

theorem rowEval1387 (x : Key → ℝ) : Integer.Sparse.eval row1387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1387, Integer.Sparse.eval_collectBalanced, rawRowCheck1387]

theorem rawRowCheck1388 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1388 := by decide +kernel

theorem rowCheck1388 : row1388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1388 := by decide +kernel

theorem rowEval1388 (x : Key → ℝ) : Integer.Sparse.eval row1388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1388, Integer.Sparse.eval_collectBalanced, rawRowCheck1388]

theorem rawRowCheck1389 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1389 := by decide +kernel

theorem rowCheck1389 : row1389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1389 := by decide +kernel

theorem rowEval1389 (x : Key → ℝ) : Integer.Sparse.eval row1389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1389, Integer.Sparse.eval_collectBalanced, rawRowCheck1389]

theorem rawRowCheck1390 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1390 := by decide +kernel

theorem rowCheck1390 : row1390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1390 := by decide +kernel

theorem rowEval1390 (x : Key → ℝ) : Integer.Sparse.eval row1390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1390, Integer.Sparse.eval_collectBalanced, rawRowCheck1390]

theorem rawRowCheck1391 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1391 := by decide +kernel

theorem rowCheck1391 : row1391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1391 := by decide +kernel

theorem rowEval1391 (x : Key → ℝ) : Integer.Sparse.eval row1391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1391, Integer.Sparse.eval_collectBalanced, rawRowCheck1391]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1350 x
  · exact rowEval1351 x
  · exact rowEval1352 x
  · exact rowEval1353 x
  · exact rowEval1354 x
  · exact rowEval1355 x
  · exact rowEval1356 x
  · exact rowEval1357 x
  · exact rowEval1358 x
  · exact rowEval1359 x
  · exact rowEval1360 x
  · exact rowEval1361 x
  · exact rowEval1362 x
  · exact rowEval1363 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

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

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1378 x
  · exact rowEval1379 x
  · exact rowEval1380 x
  · exact rowEval1381 x
  · exact rowEval1382 x
  · exact rowEval1383 x
  · exact rowEval1384 x
  · exact rowEval1385 x
  · exact rowEval1386 x
  · exact rowEval1387 x
  · exact rowEval1388 x
  · exact rowEval1389 x
  · exact rowEval1390 x
  · exact rowEval1391 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

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

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1420 x
  · exact rowEval1421 x
  · exact rowEval1422 x
  · exact rowEval1423 x
  · exact rowEval1424 x
  · exact rowEval1425 x
  · exact rowEval1426 x
  · exact rowEval1427 x
  · exact rowEval1428 x
  · exact rowEval1429 x
  · exact rowEval1430 x
  · exact rowEval1431 x
  · exact rowEval1432 x
  · exact rowEval1433 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

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

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block1.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form8.terms k).tag (GramFunctions.Block1.form8.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval1462 x
  · exact rowEval1463 x
  · exact rowEval1464 x
  · exact rowEval1465 x
  · exact rowEval1466 x
  · exact rowEval1467 x
  · exact rowEval1468 x
  · exact rowEval1469 x
  · exact rowEval1470 x
  · exact rowEval1471 x
  · exact rowEval1472 x
  · exact rowEval1473 x
  · exact rowEval1474 x
  · exact rowEval1475 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block1.form8.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form8 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

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

theorem entryEvalRow8_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 8).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval8_0 B hB
  · exact entryEval8_1 B hB
  · exact entryEval8_2 B hB
  · exact entryEval8_3 B hB
  · exact entryEval8_4 B hB
  · exact entryEval8_5 B hB
  · exact entryEval8_6 B hB
  · exact entryEval8_7 B hB
  · exact entryEval8_8 B hB
  · exact (entryEval9_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_8_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e_oai
