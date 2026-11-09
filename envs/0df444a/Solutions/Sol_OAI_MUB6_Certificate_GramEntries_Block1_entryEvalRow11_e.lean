-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:24:19.972192+00:00
-- url     : https://prove2.me/submissions/6ca70ce3-dd43-4b16-9611-451f9880b163

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_11_e

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

theorem rawRowCheck1918 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1918 := by decide +kernel

theorem rowCheck1918 : row1918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1918 := by decide +kernel

theorem rowEval1918 (x : Key → ℝ) : Integer.Sparse.eval row1918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1918, Integer.Sparse.eval_collectBalanced, rawRowCheck1918]

theorem rawRowCheck1919 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1919 := by decide +kernel

theorem rowCheck1919 : row1919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1919 := by decide +kernel

theorem rowEval1919 (x : Key → ℝ) : Integer.Sparse.eval row1919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1919, Integer.Sparse.eval_collectBalanced, rawRowCheck1919]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck1920 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1920 := by decide +kernel

theorem rowCheck1920 : row1920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1920 := by decide +kernel

theorem rowEval1920 (x : Key → ℝ) : Integer.Sparse.eval row1920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1920, Integer.Sparse.eval_collectBalanced, rawRowCheck1920]

theorem rawRowCheck1921 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1921 := by decide +kernel

theorem rowCheck1921 : row1921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1921 := by decide +kernel

theorem rowEval1921 (x : Key → ℝ) : Integer.Sparse.eval row1921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1921, Integer.Sparse.eval_collectBalanced, rawRowCheck1921]

theorem rawRowCheck1922 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1922 := by decide +kernel

theorem rowCheck1922 : row1922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1922 := by decide +kernel

theorem rowEval1922 (x : Key → ℝ) : Integer.Sparse.eval row1922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1922, Integer.Sparse.eval_collectBalanced, rawRowCheck1922]

theorem rawRowCheck1923 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1923 := by decide +kernel

theorem rowCheck1923 : row1923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1923 := by decide +kernel

theorem rowEval1923 (x : Key → ℝ) : Integer.Sparse.eval row1923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1923, Integer.Sparse.eval_collectBalanced, rawRowCheck1923]

theorem rawRowCheck1924 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1924 := by decide +kernel

theorem rowCheck1924 : row1924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1924 := by decide +kernel

theorem rowEval1924 (x : Key → ℝ) : Integer.Sparse.eval row1924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1924, Integer.Sparse.eval_collectBalanced, rawRowCheck1924]

theorem rawRowCheck1925 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1925 := by decide +kernel

theorem rowCheck1925 : row1925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1925 := by decide +kernel

theorem rowEval1925 (x : Key → ℝ) : Integer.Sparse.eval row1925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1925, Integer.Sparse.eval_collectBalanced, rawRowCheck1925]

theorem rawRowCheck1926 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1926 := by decide +kernel

theorem rowCheck1926 : row1926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1926 := by decide +kernel

theorem rowEval1926 (x : Key → ℝ) : Integer.Sparse.eval row1926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1926, Integer.Sparse.eval_collectBalanced, rawRowCheck1926]

theorem rawRowCheck1927 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1927 := by decide +kernel

theorem rowCheck1927 : row1927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1927 := by decide +kernel

theorem rowEval1927 (x : Key → ℝ) : Integer.Sparse.eval row1927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1927, Integer.Sparse.eval_collectBalanced, rawRowCheck1927]

theorem rawRowCheck1928 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1928 := by decide +kernel

theorem rowCheck1928 : row1928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1928 := by decide +kernel

theorem rowEval1928 (x : Key → ℝ) : Integer.Sparse.eval row1928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1928, Integer.Sparse.eval_collectBalanced, rawRowCheck1928]

theorem rawRowCheck1929 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1929 := by decide +kernel

theorem rowCheck1929 : row1929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1929 := by decide +kernel

theorem rowEval1929 (x : Key → ℝ) : Integer.Sparse.eval row1929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1929, Integer.Sparse.eval_collectBalanced, rawRowCheck1929]

theorem rawRowCheck1930 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1930 := by decide +kernel

theorem rowCheck1930 : row1930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1930 := by decide +kernel

theorem rowEval1930 (x : Key → ℝ) : Integer.Sparse.eval row1930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1930, Integer.Sparse.eval_collectBalanced, rawRowCheck1930]

theorem rawRowCheck1931 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1931 := by decide +kernel

theorem rowCheck1931 : row1931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1931 := by decide +kernel

theorem rowEval1931 (x : Key → ℝ) : Integer.Sparse.eval row1931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1931, Integer.Sparse.eval_collectBalanced, rawRowCheck1931]

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

theorem rawRowCheck1946 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1946 := by decide +kernel

theorem rowCheck1946 : row1946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1946 := by decide +kernel

theorem rowEval1946 (x : Key → ℝ) : Integer.Sparse.eval row1946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1946, Integer.Sparse.eval_collectBalanced, rawRowCheck1946]

theorem rawRowCheck1947 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1947 := by decide +kernel

theorem rowCheck1947 : row1947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1947 := by decide +kernel

theorem rowEval1947 (x : Key → ℝ) : Integer.Sparse.eval row1947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1947, Integer.Sparse.eval_collectBalanced, rawRowCheck1947]

theorem rawRowCheck1948 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1948 := by decide +kernel

theorem rowCheck1948 : row1948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1948 := by decide +kernel

theorem rowEval1948 (x : Key → ℝ) : Integer.Sparse.eval row1948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1948, Integer.Sparse.eval_collectBalanced, rawRowCheck1948]

theorem rawRowCheck1949 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1949 := by decide +kernel

theorem rowCheck1949 : row1949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1949 := by decide +kernel

theorem rowEval1949 (x : Key → ℝ) : Integer.Sparse.eval row1949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1949, Integer.Sparse.eval_collectBalanced, rawRowCheck1949]

theorem rawRowCheck1950 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1950 := by decide +kernel

theorem rowCheck1950 : row1950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1950 := by decide +kernel

theorem rowEval1950 (x : Key → ℝ) : Integer.Sparse.eval row1950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1950, Integer.Sparse.eval_collectBalanced, rawRowCheck1950]

theorem rawRowCheck1951 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1951 := by decide +kernel

theorem rowCheck1951 : row1951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1951 := by decide +kernel

theorem rowEval1951 (x : Key → ℝ) : Integer.Sparse.eval row1951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1951, Integer.Sparse.eval_collectBalanced, rawRowCheck1951]

theorem rawRowCheck1952 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1952 := by decide +kernel

theorem rowCheck1952 : row1952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1952 := by decide +kernel

theorem rowEval1952 (x : Key → ℝ) : Integer.Sparse.eval row1952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1952, Integer.Sparse.eval_collectBalanced, rawRowCheck1952]

theorem rawRowCheck1953 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1953 := by decide +kernel

theorem rowCheck1953 : row1953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1953 := by decide +kernel

theorem rowEval1953 (x : Key → ℝ) : Integer.Sparse.eval row1953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1953, Integer.Sparse.eval_collectBalanced, rawRowCheck1953]

theorem rawRowCheck1954 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1954 := by decide +kernel

theorem rowCheck1954 : row1954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1954 := by decide +kernel

theorem rowEval1954 (x : Key → ℝ) : Integer.Sparse.eval row1954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1954, Integer.Sparse.eval_collectBalanced, rawRowCheck1954]

theorem rawRowCheck1955 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1955 := by decide +kernel

theorem rowCheck1955 : row1955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1955 := by decide +kernel

theorem rowEval1955 (x : Key → ℝ) : Integer.Sparse.eval row1955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1955, Integer.Sparse.eval_collectBalanced, rawRowCheck1955]

theorem rawRowCheck1956 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1956 := by decide +kernel

theorem rowCheck1956 : row1956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1956 := by decide +kernel

theorem rowEval1956 (x : Key → ℝ) : Integer.Sparse.eval row1956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1956, Integer.Sparse.eval_collectBalanced, rawRowCheck1956]

theorem rawRowCheck1957 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1957 := by decide +kernel

theorem rowCheck1957 : row1957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1957 := by decide +kernel

theorem rowEval1957 (x : Key → ℝ) : Integer.Sparse.eval row1957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1957, Integer.Sparse.eval_collectBalanced, rawRowCheck1957]

theorem rawRowCheck1958 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1958 := by decide +kernel

theorem rowCheck1958 : row1958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1958 := by decide +kernel

theorem rowEval1958 (x : Key → ℝ) : Integer.Sparse.eval row1958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1958, Integer.Sparse.eval_collectBalanced, rawRowCheck1958]

theorem rawRowCheck1959 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1959 := by decide +kernel

theorem rowCheck1959 : row1959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1959 := by decide +kernel

theorem rowEval1959 (x : Key → ℝ) : Integer.Sparse.eval row1959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1959, Integer.Sparse.eval_collectBalanced, rawRowCheck1959]

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

theorem rawRowCheck1988 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1988 := by decide +kernel

theorem rowCheck1988 : row1988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1988 := by decide +kernel

theorem rowEval1988 (x : Key → ℝ) : Integer.Sparse.eval row1988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1988, Integer.Sparse.eval_collectBalanced, rawRowCheck1988]

theorem rawRowCheck1989 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1989 := by decide +kernel

theorem rowCheck1989 : row1989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1989 := by decide +kernel

theorem rowEval1989 (x : Key → ℝ) : Integer.Sparse.eval row1989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1989, Integer.Sparse.eval_collectBalanced, rawRowCheck1989]

theorem rawRowCheck1990 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1990 := by decide +kernel

theorem rowCheck1990 : row1990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1990 := by decide +kernel

theorem rowEval1990 (x : Key → ℝ) : Integer.Sparse.eval row1990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1990, Integer.Sparse.eval_collectBalanced, rawRowCheck1990]

theorem rawRowCheck1991 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1991 := by decide +kernel

theorem rowCheck1991 : row1991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1991 := by decide +kernel

theorem rowEval1991 (x : Key → ℝ) : Integer.Sparse.eval row1991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1991, Integer.Sparse.eval_collectBalanced, rawRowCheck1991]

theorem rawRowCheck1992 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5 = rawRow1992 := by decide +kernel

theorem rowCheck1992 : row1992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1992 := by decide +kernel

theorem rowEval1992 (x : Key → ℝ) : Integer.Sparse.eval row1992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1992, Integer.Sparse.eval_collectBalanced, rawRowCheck1992]

theorem rawRowCheck1993 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5 = rawRow1993 := by decide +kernel

theorem rowCheck1993 : row1993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1993 := by decide +kernel

theorem rowEval1993 (x : Key → ℝ) : Integer.Sparse.eval row1993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1993, Integer.Sparse.eval_collectBalanced, rawRowCheck1993]

theorem rawRowCheck1994 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5 = rawRow1994 := by decide +kernel

theorem rowCheck1994 : row1994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1994 := by decide +kernel

theorem rowEval1994 (x : Key → ℝ) : Integer.Sparse.eval row1994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1994, Integer.Sparse.eval_collectBalanced, rawRowCheck1994]

theorem rawRowCheck1995 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1995 := by decide +kernel

theorem rowCheck1995 : row1995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1995 := by decide +kernel

theorem rowEval1995 (x : Key → ℝ) : Integer.Sparse.eval row1995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1995, Integer.Sparse.eval_collectBalanced, rawRowCheck1995]

theorem rawRowCheck1996 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1996 := by decide +kernel

theorem rowCheck1996 : row1996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1996 := by decide +kernel

theorem rowEval1996 (x : Key → ℝ) : Integer.Sparse.eval row1996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1996, Integer.Sparse.eval_collectBalanced, rawRowCheck1996]

theorem rawRowCheck1997 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1997 := by decide +kernel

theorem rowCheck1997 : row1997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1997 := by decide +kernel

theorem rowEval1997 (x : Key → ℝ) : Integer.Sparse.eval row1997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1997, Integer.Sparse.eval_collectBalanced, rawRowCheck1997]

theorem rawRowCheck1998 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1998 := by decide +kernel

theorem rowCheck1998 : row1998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1998 := by decide +kernel

theorem rowEval1998 (x : Key → ℝ) : Integer.Sparse.eval row1998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1998, Integer.Sparse.eval_collectBalanced, rawRowCheck1998]

theorem rawRowCheck1999 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1999 := by decide +kernel

theorem rowCheck1999 : row1999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1999 := by decide +kernel

theorem rowEval1999 (x : Key → ℝ) : Integer.Sparse.eval row1999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1999, Integer.Sparse.eval_collectBalanced, rawRowCheck1999]

theorem rawRowCheck2000 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow2000 := by decide +kernel

theorem rowCheck2000 : row2000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2000 := by decide +kernel

theorem rowEval2000 (x : Key → ℝ) : Integer.Sparse.eval row2000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2000, Integer.Sparse.eval_collectBalanced, rawRowCheck2000]

theorem rawRowCheck2001 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow2001 := by decide +kernel

theorem rowCheck2001 : row2001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2001 := by decide +kernel

theorem rowEval2001 (x : Key → ℝ) : Integer.Sparse.eval row2001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck2001, Integer.Sparse.eval_collectBalanced, rawRowCheck2001]

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

theorem rawRowCheck2058 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2058 := by decide +kernel

theorem rowCheck2058 : row2058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2058 := by decide +kernel

theorem rowEval2058 (x : Key → ℝ) : Integer.Sparse.eval row2058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2058, Integer.Sparse.eval_collectBalanced, rawRowCheck2058]

theorem rawRowCheck2059 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2059 := by decide +kernel

theorem rowCheck2059 : row2059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2059 := by decide +kernel

theorem rowEval2059 (x : Key → ℝ) : Integer.Sparse.eval row2059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2059, Integer.Sparse.eval_collectBalanced, rawRowCheck2059]

theorem rawRowCheck2060 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2060 := by decide +kernel

theorem rowCheck2060 : row2060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2060 := by decide +kernel

theorem rowEval2060 (x : Key → ℝ) : Integer.Sparse.eval row2060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2060, Integer.Sparse.eval_collectBalanced, rawRowCheck2060]

theorem rawRowCheck2061 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2061 := by decide +kernel

theorem rowCheck2061 : row2061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2061 := by decide +kernel

theorem rowEval2061 (x : Key → ℝ) : Integer.Sparse.eval row2061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2061, Integer.Sparse.eval_collectBalanced, rawRowCheck2061]

theorem rawRowCheck2062 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2062 := by decide +kernel

theorem rowCheck2062 : row2062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2062 := by decide +kernel

theorem rowEval2062 (x : Key → ℝ) : Integer.Sparse.eval row2062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2062, Integer.Sparse.eval_collectBalanced, rawRowCheck2062]

theorem rawRowCheck2063 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2063 := by decide +kernel

theorem rowCheck2063 : row2063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2063 := by decide +kernel

theorem rowEval2063 (x : Key → ℝ) : Integer.Sparse.eval row2063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2063, Integer.Sparse.eval_collectBalanced, rawRowCheck2063]

theorem rawRowCheck2064 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2064 := by decide +kernel

theorem rowCheck2064 : row2064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2064 := by decide +kernel

theorem rowEval2064 (x : Key → ℝ) : Integer.Sparse.eval row2064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2064, Integer.Sparse.eval_collectBalanced, rawRowCheck2064]

theorem rawRowCheck2065 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form10 = rawRow2065 := by decide +kernel

theorem rowCheck2065 : row2065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2065 := by decide +kernel

theorem rowEval2065 (x : Key → ℝ) : Integer.Sparse.eval row2065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2065, Integer.Sparse.eval_collectBalanced, rawRowCheck2065]

theorem rawRowCheck2066 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form10 = rawRow2066 := by decide +kernel

theorem rowCheck2066 : row2066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2066 := by decide +kernel

theorem rowEval2066 (x : Key → ℝ) : Integer.Sparse.eval row2066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2066, Integer.Sparse.eval_collectBalanced, rawRowCheck2066]

theorem rawRowCheck2067 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form10 = rawRow2067 := by decide +kernel

theorem rowCheck2067 : row2067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2067 := by decide +kernel

theorem rowEval2067 (x : Key → ℝ) : Integer.Sparse.eval row2067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2067, Integer.Sparse.eval_collectBalanced, rawRowCheck2067]

theorem rawRowCheck2068 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2068 := by decide +kernel

theorem rowCheck2068 : row2068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2068 := by decide +kernel

theorem rowEval2068 (x : Key → ℝ) : Integer.Sparse.eval row2068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2068, Integer.Sparse.eval_collectBalanced, rawRowCheck2068]

theorem rawRowCheck2069 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form10 = rawRow2069 := by decide +kernel

theorem rowCheck2069 : row2069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2069 := by decide +kernel

theorem rowEval2069 (x : Key → ℝ) : Integer.Sparse.eval row2069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2069, Integer.Sparse.eval_collectBalanced, rawRowCheck2069]

theorem rawRowCheck2070 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form10 = rawRow2070 := by decide +kernel

theorem rowCheck2070 : row2070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2070 := by decide +kernel

theorem rowEval2070 (x : Key → ℝ) : Integer.Sparse.eval row2070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2070, Integer.Sparse.eval_collectBalanced, rawRowCheck2070]

theorem rawRowCheck2071 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form10 = rawRow2071 := by decide +kernel

theorem rowCheck2071 : row2071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2071 := by decide +kernel

theorem rowEval2071 (x : Key → ℝ) : Integer.Sparse.eval row2071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2071, Integer.Sparse.eval_collectBalanced, rawRowCheck2071]

theorem rawRowCheck2072 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2072 := by decide +kernel

theorem rowCheck2072 : row2072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2072 := by decide +kernel

theorem rowEval2072 (x : Key → ℝ) : Integer.Sparse.eval row2072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2072, Integer.Sparse.eval_collectBalanced, rawRowCheck2072]

theorem rawRowCheck2073 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2073 := by decide +kernel

theorem rowCheck2073 : row2073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2073 := by decide +kernel

theorem rowEval2073 (x : Key → ℝ) : Integer.Sparse.eval row2073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2073, Integer.Sparse.eval_collectBalanced, rawRowCheck2073]

theorem rawRowCheck2074 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2074 := by decide +kernel

theorem rowCheck2074 : row2074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2074 := by decide +kernel

theorem rowEval2074 (x : Key → ℝ) : Integer.Sparse.eval row2074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2074, Integer.Sparse.eval_collectBalanced, rawRowCheck2074]

theorem rawRowCheck2075 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2075 := by decide +kernel

theorem rowCheck2075 : row2075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2075 := by decide +kernel

theorem rowEval2075 (x : Key → ℝ) : Integer.Sparse.eval row2075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2075, Integer.Sparse.eval_collectBalanced, rawRowCheck2075]

theorem rawRowCheck2076 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2076 := by decide +kernel

theorem rowCheck2076 : row2076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2076 := by decide +kernel

theorem rowEval2076 (x : Key → ℝ) : Integer.Sparse.eval row2076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2076, Integer.Sparse.eval_collectBalanced, rawRowCheck2076]

theorem rawRowCheck2077 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2077 := by decide +kernel

theorem rowCheck2077 : row2077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2077 := by decide +kernel

theorem rowEval2077 (x : Key → ℝ) : Integer.Sparse.eval row2077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2077, Integer.Sparse.eval_collectBalanced, rawRowCheck2077]

theorem rawRowCheck2078 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2078 := by decide +kernel

theorem rowCheck2078 : row2078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2078 := by decide +kernel

theorem rowEval2078 (x : Key → ℝ) : Integer.Sparse.eval row2078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2078, Integer.Sparse.eval_collectBalanced, rawRowCheck2078]

theorem rawRowCheck2079 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form11 = rawRow2079 := by decide +kernel

theorem rowCheck2079 : row2079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2079 := by decide +kernel

theorem rowEval2079 (x : Key → ℝ) : Integer.Sparse.eval row2079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2079, Integer.Sparse.eval_collectBalanced, rawRowCheck2079]

theorem rawRowCheck2080 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form11 = rawRow2080 := by decide +kernel

theorem rowCheck2080 : row2080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2080 := by decide +kernel

theorem rowEval2080 (x : Key → ℝ) : Integer.Sparse.eval row2080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2080, Integer.Sparse.eval_collectBalanced, rawRowCheck2080]

theorem rawRowCheck2081 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form11 = rawRow2081 := by decide +kernel

theorem rowCheck2081 : row2081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2081 := by decide +kernel

theorem rowEval2081 (x : Key → ℝ) : Integer.Sparse.eval row2081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2081, Integer.Sparse.eval_collectBalanced, rawRowCheck2081]

theorem rawRowCheck2082 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2082 := by decide +kernel

theorem rowCheck2082 : row2082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2082 := by decide +kernel

theorem rowEval2082 (x : Key → ℝ) : Integer.Sparse.eval row2082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2082, Integer.Sparse.eval_collectBalanced, rawRowCheck2082]

theorem rawRowCheck2083 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form11 = rawRow2083 := by decide +kernel

theorem rowCheck2083 : row2083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2083 := by decide +kernel

theorem rowEval2083 (x : Key → ℝ) : Integer.Sparse.eval row2083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2083, Integer.Sparse.eval_collectBalanced, rawRowCheck2083]

theorem rawRowCheck2084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form11 = rawRow2084 := by decide +kernel

theorem rowCheck2084 : row2084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2084 := by decide +kernel

theorem rowEval2084 (x : Key → ℝ) : Integer.Sparse.eval row2084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2084, Integer.Sparse.eval_collectBalanced, rawRowCheck2084]

theorem rawRowCheck2085 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form11 = rawRow2085 := by decide +kernel

theorem rowCheck2085 : row2085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2085 := by decide +kernel

theorem rowEval2085 (x : Key → ℝ) : Integer.Sparse.eval row2085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2085, Integer.Sparse.eval_collectBalanced, rawRowCheck2085]

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

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1918 x
  · exact rowEval1919 x
  · exact rowEval1920 x
  · exact rowEval1921 x
  · exact rowEval1922 x
  · exact rowEval1923 x
  · exact rowEval1924 x
  · exact rowEval1925 x
  · exact rowEval1926 x
  · exact rowEval1927 x
  · exact rowEval1928 x
  · exact rowEval1929 x
  · exact rowEval1930 x
  · exact rowEval1931 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

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

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1946 x
  · exact rowEval1947 x
  · exact rowEval1948 x
  · exact rowEval1949 x
  · exact rowEval1950 x
  · exact rowEval1951 x
  · exact rowEval1952 x
  · exact rowEval1953 x
  · exact rowEval1954 x
  · exact rowEval1955 x
  · exact rowEval1956 x
  · exact rowEval1957 x
  · exact rowEval1958 x
  · exact rowEval1959 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

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

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1988 x
  · exact rowEval1989 x
  · exact rowEval1990 x
  · exact rowEval1991 x
  · exact rowEval1992 x
  · exact rowEval1993 x
  · exact rowEval1994 x
  · exact rowEval1995 x
  · exact rowEval1996 x
  · exact rowEval1997 x
  · exact rowEval1998 x
  · exact rowEval1999 x
  · exact rowEval2000 x
  · exact rowEval2001 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

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

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2058 x
  · exact rowEval2059 x
  · exact rowEval2060 x
  · exact rowEval2061 x
  · exact rowEval2062 x
  · exact rowEval2063 x
  · exact rowEval2064 x
  · exact rowEval2065 x
  · exact rowEval2066 x
  · exact rowEval2067 x
  · exact rowEval2068 x
  · exact rowEval2069 x
  · exact rowEval2070 x
  · exact rowEval2071 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2072 x
  · exact rowEval2073 x
  · exact rowEval2074 x
  · exact rowEval2075 x
  · exact rowEval2076 x
  · exact rowEval2077 x
  · exact rowEval2078 x
  · exact rowEval2079 x
  · exact rowEval2080 x
  · exact rowEval2081 x
  · exact rowEval2082 x
  · exact rowEval2083 x
  · exact rowEval2084 x
  · exact rowEval2085 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2630 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2630 := by decide +kernel

theorem rowCheck2630 : row2630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2630 := by decide +kernel

theorem rowEval2630 (x : Key → ℝ) : Integer.Sparse.eval row2630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2630, Integer.Sparse.eval_collectBalanced, rawRowCheck2630]

theorem rawRowCheck2631 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2631 := by decide +kernel

theorem rowCheck2631 : row2631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2631 := by decide +kernel

theorem rowEval2631 (x : Key → ℝ) : Integer.Sparse.eval row2631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2631, Integer.Sparse.eval_collectBalanced, rawRowCheck2631]

theorem rawRowCheck2632 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2632 := by decide +kernel

theorem rowCheck2632 : row2632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2632 := by decide +kernel

theorem rowEval2632 (x : Key → ℝ) : Integer.Sparse.eval row2632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2632, Integer.Sparse.eval_collectBalanced, rawRowCheck2632]

theorem rawRowCheck2633 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2633 := by decide +kernel

theorem rowCheck2633 : row2633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2633 := by decide +kernel

theorem rowEval2633 (x : Key → ℝ) : Integer.Sparse.eval row2633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2633, Integer.Sparse.eval_collectBalanced, rawRowCheck2633]

theorem rawRowCheck2634 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2634 := by decide +kernel

theorem rowCheck2634 : row2634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2634 := by decide +kernel

theorem rowEval2634 (x : Key → ℝ) : Integer.Sparse.eval row2634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2634, Integer.Sparse.eval_collectBalanced, rawRowCheck2634]

theorem rawRowCheck2635 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2635 := by decide +kernel

theorem rowCheck2635 : row2635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2635 := by decide +kernel

theorem rowEval2635 (x : Key → ℝ) : Integer.Sparse.eval row2635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2635, Integer.Sparse.eval_collectBalanced, rawRowCheck2635]

theorem rawRowCheck2636 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2636 := by decide +kernel

theorem rowCheck2636 : row2636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2636 := by decide +kernel

theorem rowEval2636 (x : Key → ℝ) : Integer.Sparse.eval row2636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2636, Integer.Sparse.eval_collectBalanced, rawRowCheck2636]

theorem rawRowCheck2637 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2637 := by decide +kernel

theorem rowCheck2637 : row2637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2637 := by decide +kernel

theorem rowEval2637 (x : Key → ℝ) : Integer.Sparse.eval row2637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2637, Integer.Sparse.eval_collectBalanced, rawRowCheck2637]

theorem rawRowCheck2638 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2638 := by decide +kernel

theorem rowCheck2638 : row2638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2638 := by decide +kernel

theorem rowEval2638 (x : Key → ℝ) : Integer.Sparse.eval row2638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2638, Integer.Sparse.eval_collectBalanced, rawRowCheck2638]

theorem rawRowCheck2639 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2639 := by decide +kernel

theorem rowCheck2639 : row2639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2639 := by decide +kernel

theorem rowEval2639 (x : Key → ℝ) : Integer.Sparse.eval row2639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2639, Integer.Sparse.eval_collectBalanced, rawRowCheck2639]

theorem rawRowCheck2640 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2640 := by decide +kernel

theorem rowCheck2640 : row2640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2640 := by decide +kernel

theorem rowEval2640 (x : Key → ℝ) : Integer.Sparse.eval row2640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2640, Integer.Sparse.eval_collectBalanced, rawRowCheck2640]

theorem rawRowCheck2641 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2641 := by decide +kernel

theorem rowCheck2641 : row2641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2641 := by decide +kernel

theorem rowEval2641 (x : Key → ℝ) : Integer.Sparse.eval row2641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2641, Integer.Sparse.eval_collectBalanced, rawRowCheck2641]

theorem rawRowCheck2642 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2642 := by decide +kernel

theorem rowCheck2642 : row2642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2642 := by decide +kernel

theorem rowEval2642 (x : Key → ℝ) : Integer.Sparse.eval row2642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2642, Integer.Sparse.eval_collectBalanced, rawRowCheck2642]

theorem rawRowCheck2643 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2643 := by decide +kernel

theorem rowCheck2643 : row2643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2643 := by decide +kernel

theorem rowEval2643 (x : Key → ℝ) : Integer.Sparse.eval row2643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2643, Integer.Sparse.eval_collectBalanced, rawRowCheck2643]

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

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2630 x
  · exact rowEval2631 x
  · exact rowEval2632 x
  · exact rowEval2633 x
  · exact rowEval2634 x
  · exact rowEval2635 x
  · exact rowEval2636 x
  · exact rowEval2637 x
  · exact rowEval2638 x
  · exact rowEval2639 x
  · exact rowEval2640 x
  · exact rowEval2641 x
  · exact rowEval2642 x
  · exact rowEval2643 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

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

theorem rawRowCheck2936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form11 = rawRow2936 := by decide +kernel

theorem rowCheck2936 : row2936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2936 := by decide +kernel

theorem rowEval2936 (x : Key → ℝ) : Integer.Sparse.eval row2936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2936, Integer.Sparse.eval_collectBalanced, rawRowCheck2936]

theorem rawRowCheck2937 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form11 = rawRow2937 := by decide +kernel

theorem rowCheck2937 : row2937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2937 := by decide +kernel

theorem rowEval2937 (x : Key → ℝ) : Integer.Sparse.eval row2937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2937, Integer.Sparse.eval_collectBalanced, rawRowCheck2937]

theorem rawRowCheck2938 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form11 = rawRow2938 := by decide +kernel

theorem rowCheck2938 : row2938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2938 := by decide +kernel

theorem rowEval2938 (x : Key → ℝ) : Integer.Sparse.eval row2938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2938, Integer.Sparse.eval_collectBalanced, rawRowCheck2938]

theorem rawRowCheck2939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2939 := by decide +kernel

theorem rowCheck2939 : row2939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2939 := by decide +kernel

theorem rowEval2939 (x : Key → ℝ) : Integer.Sparse.eval row2939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2939, Integer.Sparse.eval_collectBalanced, rawRowCheck2939]

theorem rawRowCheck2940 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2940 := by decide +kernel

theorem rowCheck2940 : row2940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2940 := by decide +kernel

theorem rowEval2940 (x : Key → ℝ) : Integer.Sparse.eval row2940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2940, Integer.Sparse.eval_collectBalanced, rawRowCheck2940]

theorem rawRowCheck2941 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2941 := by decide +kernel

theorem rowCheck2941 : row2941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2941 := by decide +kernel

theorem rowEval2941 (x : Key → ℝ) : Integer.Sparse.eval row2941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2941, Integer.Sparse.eval_collectBalanced, rawRowCheck2941]

theorem rawRowCheck2942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form11 = rawRow2942 := by decide +kernel

theorem rowCheck2942 : row2942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2942 := by decide +kernel

theorem rowEval2942 (x : Key → ℝ) : Integer.Sparse.eval row2942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2942, Integer.Sparse.eval_collectBalanced, rawRowCheck2942]

theorem rawRowCheck2943 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form11 = rawRow2943 := by decide +kernel

theorem rowCheck2943 : row2943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2943 := by decide +kernel

theorem rowEval2943 (x : Key → ℝ) : Integer.Sparse.eval row2943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2943, Integer.Sparse.eval_collectBalanced, rawRowCheck2943]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2944 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form11 = rawRow2944 := by decide +kernel

theorem rowCheck2944 : row2944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2944 := by decide +kernel

theorem rowEval2944 (x : Key → ℝ) : Integer.Sparse.eval row2944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2944, Integer.Sparse.eval_collectBalanced, rawRowCheck2944]

theorem rawRowCheck2945 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form11 = rawRow2945 := by decide +kernel

theorem rowCheck2945 : row2945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2945 := by decide +kernel

theorem rowEval2945 (x : Key → ℝ) : Integer.Sparse.eval row2945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2945, Integer.Sparse.eval_collectBalanced, rawRowCheck2945]

theorem rawRowCheck2946 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form11 = rawRow2946 := by decide +kernel

theorem rowCheck2946 : row2946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2946 := by decide +kernel

theorem rowEval2946 (x : Key → ℝ) : Integer.Sparse.eval row2946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2946, Integer.Sparse.eval_collectBalanced, rawRowCheck2946]

theorem rawRowCheck2947 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form11 = rawRow2947 := by decide +kernel

theorem rowCheck2947 : row2947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2947 := by decide +kernel

theorem rowEval2947 (x : Key → ℝ) : Integer.Sparse.eval row2947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2947, Integer.Sparse.eval_collectBalanced, rawRowCheck2947]

theorem rawRowCheck2948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form11 = rawRow2948 := by decide +kernel

theorem rowCheck2948 : row2948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2948 := by decide +kernel

theorem rowEval2948 (x : Key → ℝ) : Integer.Sparse.eval row2948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2948, Integer.Sparse.eval_collectBalanced, rawRowCheck2948]

theorem rawRowCheck2949 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form11 = rawRow2949 := by decide +kernel

theorem rowCheck2949 : row2949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2949 := by decide +kernel

theorem rowEval2949 (x : Key → ℝ) : Integer.Sparse.eval row2949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2949, Integer.Sparse.eval_collectBalanced, rawRowCheck2949]

theorem rawRowCheck2950 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form11 = rawRow2950 := by decide +kernel

theorem rowCheck2950 : row2950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2950 := by decide +kernel

theorem rowEval2950 (x : Key → ℝ) : Integer.Sparse.eval row2950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2950, Integer.Sparse.eval_collectBalanced, rawRowCheck2950]

theorem rawRowCheck2951 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2951 := by decide +kernel

theorem rowCheck2951 : row2951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2951 := by decide +kernel

theorem rowEval2951 (x : Key → ℝ) : Integer.Sparse.eval row2951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2951, Integer.Sparse.eval_collectBalanced, rawRowCheck2951]

theorem rawRowCheck2952 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2952 := by decide +kernel

theorem rowCheck2952 : row2952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2952 := by decide +kernel

theorem rowEval2952 (x : Key → ℝ) : Integer.Sparse.eval row2952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2952, Integer.Sparse.eval_collectBalanced, rawRowCheck2952]

theorem rawRowCheck2953 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2953 := by decide +kernel

theorem rowCheck2953 : row2953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2953 := by decide +kernel

theorem rowEval2953 (x : Key → ℝ) : Integer.Sparse.eval row2953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2953, Integer.Sparse.eval_collectBalanced, rawRowCheck2953]

theorem rawRowCheck2954 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form11 = rawRow2954 := by decide +kernel

theorem rowCheck2954 : row2954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2954 := by decide +kernel

theorem rowEval2954 (x : Key → ℝ) : Integer.Sparse.eval row2954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2954, Integer.Sparse.eval_collectBalanced, rawRowCheck2954]

theorem rawRowCheck2955 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form11 = rawRow2955 := by decide +kernel

theorem rowCheck2955 : row2955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2955 := by decide +kernel

theorem rowEval2955 (x : Key → ℝ) : Integer.Sparse.eval row2955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2955, Integer.Sparse.eval_collectBalanced, rawRowCheck2955]

theorem rawRowCheck2956 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form11 = rawRow2956 := by decide +kernel

theorem rowCheck2956 : row2956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2956 := by decide +kernel

theorem rowEval2956 (x : Key → ℝ) : Integer.Sparse.eval row2956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2956, Integer.Sparse.eval_collectBalanced, rawRowCheck2956]

theorem rawRowCheck2957 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form11 = rawRow2957 := by decide +kernel

theorem rowCheck2957 : row2957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2957 := by decide +kernel

theorem rowEval2957 (x : Key → ℝ) : Integer.Sparse.eval row2957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2957, Integer.Sparse.eval_collectBalanced, rawRowCheck2957]

theorem rawRowCheck2958 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form11 = rawRow2958 := by decide +kernel

theorem rowCheck2958 : row2958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2958 := by decide +kernel

theorem rowEval2958 (x : Key → ℝ) : Integer.Sparse.eval row2958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2958, Integer.Sparse.eval_collectBalanced, rawRowCheck2958]

theorem rawRowCheck2959 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form11 = rawRow2959 := by decide +kernel

theorem rowCheck2959 : row2959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2959 := by decide +kernel

theorem rowEval2959 (x : Key → ℝ) : Integer.Sparse.eval row2959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2959, Integer.Sparse.eval_collectBalanced, rawRowCheck2959]

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

theorem entryCheck14_11 : entry14_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_11 k)) := by decide +kernel

theorem rowsSound14_11 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2936 x
  · exact rowEval2937 x
  · exact rowEval2938 x
  · exact rowEval2939 x
  · exact rowEval2940 x
  · exact rowEval2941 x
  · exact rowEval2942 x
  · exact rowEval2943 x
  · exact rowEval2944 x
  · exact rowEval2945 x
  · exact rowEval2946 x
  · exact rowEval2947 x
  · exact rowEval2948 x
  · exact rowEval2949 x
  · exact rowEval2950 x
  · exact rowEval2951 x
  · exact rowEval2952 x
  · exact rowEval2953 x
  · exact rowEval2954 x
  · exact rowEval2955 x
  · exact rowEval2956 x
  · exact rowEval2957 x
  · exact rowEval2958 x
  · exact rowEval2959 x

theorem entryEval14_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_11 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck14_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_11]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck4710 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4710 := by decide +kernel

theorem rowCheck4710 : row4710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4710 := by decide +kernel

theorem rowEval4710 (x : Key → ℝ) : Integer.Sparse.eval row4710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4710, Integer.Sparse.eval_collectBalanced, rawRowCheck4710]

theorem rawRowCheck4711 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4711 := by decide +kernel

theorem rowCheck4711 : row4711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4711 := by decide +kernel

theorem rowEval4711 (x : Key → ℝ) : Integer.Sparse.eval row4711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4711, Integer.Sparse.eval_collectBalanced, rawRowCheck4711]

theorem rawRowCheck4712 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4712 := by decide +kernel

theorem rowCheck4712 : row4712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4712 := by decide +kernel

theorem rowEval4712 (x : Key → ℝ) : Integer.Sparse.eval row4712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4712, Integer.Sparse.eval_collectBalanced, rawRowCheck4712]

theorem rawRowCheck4713 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4713 := by decide +kernel

theorem rowCheck4713 : row4713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4713 := by decide +kernel

theorem rowEval4713 (x : Key → ℝ) : Integer.Sparse.eval row4713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4713, Integer.Sparse.eval_collectBalanced, rawRowCheck4713]

theorem rawRowCheck4714 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4714 := by decide +kernel

theorem rowCheck4714 : row4714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4714 := by decide +kernel

theorem rowEval4714 (x : Key → ℝ) : Integer.Sparse.eval row4714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4714, Integer.Sparse.eval_collectBalanced, rawRowCheck4714]

theorem rawRowCheck4715 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4715 := by decide +kernel

theorem rowCheck4715 : row4715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4715 := by decide +kernel

theorem rowEval4715 (x : Key → ℝ) : Integer.Sparse.eval row4715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4715, Integer.Sparse.eval_collectBalanced, rawRowCheck4715]

theorem rawRowCheck4716 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4716 := by decide +kernel

theorem rowCheck4716 : row4716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4716 := by decide +kernel

theorem rowEval4716 (x : Key → ℝ) : Integer.Sparse.eval row4716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4716, Integer.Sparse.eval_collectBalanced, rawRowCheck4716]

theorem rawRowCheck4717 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4717 := by decide +kernel

theorem rowCheck4717 : row4717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4717 := by decide +kernel

theorem rowEval4717 (x : Key → ℝ) : Integer.Sparse.eval row4717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4717, Integer.Sparse.eval_collectBalanced, rawRowCheck4717]

theorem rawRowCheck4718 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4718 := by decide +kernel

theorem rowCheck4718 : row4718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4718 := by decide +kernel

theorem rowEval4718 (x : Key → ℝ) : Integer.Sparse.eval row4718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4718, Integer.Sparse.eval_collectBalanced, rawRowCheck4718]

theorem rawRowCheck4719 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4719 := by decide +kernel

theorem rowCheck4719 : row4719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4719 := by decide +kernel

theorem rowEval4719 (x : Key → ℝ) : Integer.Sparse.eval row4719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4719, Integer.Sparse.eval_collectBalanced, rawRowCheck4719]

theorem rawRowCheck4720 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4720 := by decide +kernel

theorem rowCheck4720 : row4720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4720 := by decide +kernel

theorem rowEval4720 (x : Key → ℝ) : Integer.Sparse.eval row4720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4720, Integer.Sparse.eval_collectBalanced, rawRowCheck4720]

theorem rawRowCheck4721 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4721 := by decide +kernel

theorem rowCheck4721 : row4721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4721 := by decide +kernel

theorem rowEval4721 (x : Key → ℝ) : Integer.Sparse.eval row4721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4721, Integer.Sparse.eval_collectBalanced, rawRowCheck4721]

theorem rawRowCheck4722 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4722 := by decide +kernel

theorem rowCheck4722 : row4722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4722 := by decide +kernel

theorem rowEval4722 (x : Key → ℝ) : Integer.Sparse.eval row4722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4722, Integer.Sparse.eval_collectBalanced, rawRowCheck4722]

theorem rawRowCheck4723 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4723 := by decide +kernel

theorem rowCheck4723 : row4723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4723 := by decide +kernel

theorem rowEval4723 (x : Key → ℝ) : Integer.Sparse.eval row4723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4723, Integer.Sparse.eval_collectBalanced, rawRowCheck4723]

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

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4710 x
  · exact rowEval4711 x
  · exact rowEval4712 x
  · exact rowEval4713 x
  · exact rowEval4714 x
  · exact rowEval4715 x
  · exact rowEval4716 x
  · exact rowEval4717 x
  · exact rowEval4718 x
  · exact rowEval4719 x
  · exact rowEval4720 x
  · exact rowEval4721 x
  · exact rowEval4722 x
  · exact rowEval4723 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck4968 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4968 := by decide +kernel

theorem rowCheck4968 : row4968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4968 := by decide +kernel

theorem rowEval4968 (x : Key → ℝ) : Integer.Sparse.eval row4968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4968, Integer.Sparse.eval_collectBalanced, rawRowCheck4968]

theorem rawRowCheck4969 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4969 := by decide +kernel

theorem rowCheck4969 : row4969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4969 := by decide +kernel

theorem rowEval4969 (x : Key → ℝ) : Integer.Sparse.eval row4969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4969, Integer.Sparse.eval_collectBalanced, rawRowCheck4969]

theorem rawRowCheck4970 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4970 := by decide +kernel

theorem rowCheck4970 : row4970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4970 := by decide +kernel

theorem rowEval4970 (x : Key → ℝ) : Integer.Sparse.eval row4970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4970, Integer.Sparse.eval_collectBalanced, rawRowCheck4970]

theorem rawRowCheck4971 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4971 := by decide +kernel

theorem rowCheck4971 : row4971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4971 := by decide +kernel

theorem rowEval4971 (x : Key → ℝ) : Integer.Sparse.eval row4971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4971, Integer.Sparse.eval_collectBalanced, rawRowCheck4971]

theorem rawRowCheck4972 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4972 := by decide +kernel

theorem rowCheck4972 : row4972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4972 := by decide +kernel

theorem rowEval4972 (x : Key → ℝ) : Integer.Sparse.eval row4972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4972, Integer.Sparse.eval_collectBalanced, rawRowCheck4972]

theorem rawRowCheck4973 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4973 := by decide +kernel

theorem rowCheck4973 : row4973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4973 := by decide +kernel

theorem rowEval4973 (x : Key → ℝ) : Integer.Sparse.eval row4973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4973, Integer.Sparse.eval_collectBalanced, rawRowCheck4973]

theorem rawRowCheck4974 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11 = rawRow4974 := by decide +kernel

theorem rowCheck4974 : row4974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4974 := by decide +kernel

theorem rowEval4974 (x : Key → ℝ) : Integer.Sparse.eval row4974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4974, Integer.Sparse.eval_collectBalanced, rawRowCheck4974]

theorem rawRowCheck4975 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11 = rawRow4975 := by decide +kernel

theorem rowCheck4975 : row4975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4975 := by decide +kernel

theorem rowEval4975 (x : Key → ℝ) : Integer.Sparse.eval row4975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4975, Integer.Sparse.eval_collectBalanced, rawRowCheck4975]

theorem rawRowCheck4976 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11 = rawRow4976 := by decide +kernel

theorem rowCheck4976 : row4976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4976 := by decide +kernel

theorem rowEval4976 (x : Key → ℝ) : Integer.Sparse.eval row4976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4976, Integer.Sparse.eval_collectBalanced, rawRowCheck4976]

theorem rawRowCheck4977 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4977 := by decide +kernel

theorem rowCheck4977 : row4977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4977 := by decide +kernel

theorem rowEval4977 (x : Key → ℝ) : Integer.Sparse.eval row4977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4977, Integer.Sparse.eval_collectBalanced, rawRowCheck4977]

theorem rawRowCheck4978 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4978 := by decide +kernel

theorem rowCheck4978 : row4978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4978 := by decide +kernel

theorem rowEval4978 (x : Key → ℝ) : Integer.Sparse.eval row4978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4978, Integer.Sparse.eval_collectBalanced, rawRowCheck4978]

theorem rawRowCheck4979 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4979 := by decide +kernel

theorem rowCheck4979 : row4979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4979 := by decide +kernel

theorem rowEval4979 (x : Key → ℝ) : Integer.Sparse.eval row4979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4979, Integer.Sparse.eval_collectBalanced, rawRowCheck4979]

theorem rawRowCheck4980 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11 = rawRow4980 := by decide +kernel

theorem rowCheck4980 : row4980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4980 := by decide +kernel

theorem rowEval4980 (x : Key → ℝ) : Integer.Sparse.eval row4980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4980, Integer.Sparse.eval_collectBalanced, rawRowCheck4980]

theorem rawRowCheck4981 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11 = rawRow4981 := by decide +kernel

theorem rowCheck4981 : row4981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4981 := by decide +kernel

theorem rowEval4981 (x : Key → ℝ) : Integer.Sparse.eval row4981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4981, Integer.Sparse.eval_collectBalanced, rawRowCheck4981]

theorem rawRowCheck4982 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11 = rawRow4982 := by decide +kernel

theorem rowCheck4982 : row4982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4982 := by decide +kernel

theorem rowEval4982 (x : Key → ℝ) : Integer.Sparse.eval row4982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4982, Integer.Sparse.eval_collectBalanced, rawRowCheck4982]

theorem rawRowCheck4983 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11 = rawRow4983 := by decide +kernel

theorem rowCheck4983 : row4983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4983 := by decide +kernel

theorem rowEval4983 (x : Key → ℝ) : Integer.Sparse.eval row4983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4983, Integer.Sparse.eval_collectBalanced, rawRowCheck4983]

theorem rawRowCheck4984 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11 = rawRow4984 := by decide +kernel

theorem rowCheck4984 : row4984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4984 := by decide +kernel

theorem rowEval4984 (x : Key → ℝ) : Integer.Sparse.eval row4984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4984, Integer.Sparse.eval_collectBalanced, rawRowCheck4984]

theorem rawRowCheck4985 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11 = rawRow4985 := by decide +kernel

theorem rowCheck4985 : row4985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4985 := by decide +kernel

theorem rowEval4985 (x : Key → ℝ) : Integer.Sparse.eval row4985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4985, Integer.Sparse.eval_collectBalanced, rawRowCheck4985]

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

theorem entryCheck20_11 : entry20_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_11 k)) := by decide +kernel

theorem rowsSound20_11 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4968 x
  · exact rowEval4969 x
  · exact rowEval4970 x
  · exact rowEval4971 x
  · exact rowEval4972 x
  · exact rowEval4973 x
  · exact rowEval4974 x
  · exact rowEval4975 x
  · exact rowEval4976 x
  · exact rowEval4977 x
  · exact rowEval4978 x
  · exact rowEval4979 x
  · exact rowEval4980 x
  · exact rowEval4981 x
  · exact rowEval4982 x
  · exact rowEval4983 x
  · exact rowEval4984 x
  · exact rowEval4985 x

theorem entryEval20_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_11 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck20_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_11]

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

theorem entryEvalRow11_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 11).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval11_0 B hB
  · exact entryEval11_1 B hB
  · exact entryEval11_2 B hB
  · exact entryEval11_3 B hB
  · exact entryEval11_4 B hB
  · exact entryEval11_5 B hB
  · exact entryEval11_6 B hB
  · exact entryEval11_7 B hB
  · exact entryEval11_8 B hB
  · exact entryEval11_9 B hB
  · exact entryEval11_10 B hB
  · exact entryEval11_11 B hB
  · exact (entryEval12_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_11_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_11 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e_oai
