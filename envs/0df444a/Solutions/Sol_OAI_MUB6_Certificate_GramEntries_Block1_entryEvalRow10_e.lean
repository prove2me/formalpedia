-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:40:22.880018+00:00
-- url     : https://prove2.me/submissions/5932b0b6-2fe9-4455-875c-9b03efd303f3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E020
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_10_e

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

theorem rawRowCheck1764 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1764 := by decide +kernel

theorem rowCheck1764 : row1764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1764 := by decide +kernel

theorem rowEval1764 (x : Key → ℝ) : Integer.Sparse.eval row1764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1764, Integer.Sparse.eval_collectBalanced, rawRowCheck1764]

theorem rawRowCheck1765 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1765 := by decide +kernel

theorem rowCheck1765 : row1765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1765 := by decide +kernel

theorem rowEval1765 (x : Key → ℝ) : Integer.Sparse.eval row1765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1765, Integer.Sparse.eval_collectBalanced, rawRowCheck1765]

theorem rawRowCheck1766 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1766 := by decide +kernel

theorem rowCheck1766 : row1766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1766 := by decide +kernel

theorem rowEval1766 (x : Key → ℝ) : Integer.Sparse.eval row1766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1766, Integer.Sparse.eval_collectBalanced, rawRowCheck1766]

theorem rawRowCheck1767 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1767 := by decide +kernel

theorem rowCheck1767 : row1767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1767 := by decide +kernel

theorem rowEval1767 (x : Key → ℝ) : Integer.Sparse.eval row1767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1767, Integer.Sparse.eval_collectBalanced, rawRowCheck1767]

theorem rawRowCheck1768 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0 = rawRow1768 := by decide +kernel

theorem rowCheck1768 : row1768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1768 := by decide +kernel

theorem rowEval1768 (x : Key → ℝ) : Integer.Sparse.eval row1768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1768, Integer.Sparse.eval_collectBalanced, rawRowCheck1768]

theorem rawRowCheck1769 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0 = rawRow1769 := by decide +kernel

theorem rowCheck1769 : row1769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1769 := by decide +kernel

theorem rowEval1769 (x : Key → ℝ) : Integer.Sparse.eval row1769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1769, Integer.Sparse.eval_collectBalanced, rawRowCheck1769]

theorem rawRowCheck1770 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0 = rawRow1770 := by decide +kernel

theorem rowCheck1770 : row1770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1770 := by decide +kernel

theorem rowEval1770 (x : Key → ℝ) : Integer.Sparse.eval row1770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1770, Integer.Sparse.eval_collectBalanced, rawRowCheck1770]

theorem rawRowCheck1771 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1771 := by decide +kernel

theorem rowCheck1771 : row1771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1771 := by decide +kernel

theorem rowEval1771 (x : Key → ℝ) : Integer.Sparse.eval row1771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1771, Integer.Sparse.eval_collectBalanced, rawRowCheck1771]

theorem rawRowCheck1772 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1772 := by decide +kernel

theorem rowCheck1772 : row1772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1772 := by decide +kernel

theorem rowEval1772 (x : Key → ℝ) : Integer.Sparse.eval row1772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1772, Integer.Sparse.eval_collectBalanced, rawRowCheck1772]

theorem rawRowCheck1773 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1773 := by decide +kernel

theorem rowCheck1773 : row1773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1773 := by decide +kernel

theorem rowEval1773 (x : Key → ℝ) : Integer.Sparse.eval row1773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1773, Integer.Sparse.eval_collectBalanced, rawRowCheck1773]

theorem rawRowCheck1774 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1774 := by decide +kernel

theorem rowCheck1774 : row1774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1774 := by decide +kernel

theorem rowEval1774 (x : Key → ℝ) : Integer.Sparse.eval row1774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1774, Integer.Sparse.eval_collectBalanced, rawRowCheck1774]

theorem rawRowCheck1775 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1775 := by decide +kernel

theorem rowCheck1775 : row1775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1775 := by decide +kernel

theorem rowEval1775 (x : Key → ℝ) : Integer.Sparse.eval row1775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1775, Integer.Sparse.eval_collectBalanced, rawRowCheck1775]

theorem rawRowCheck1776 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1776 := by decide +kernel

theorem rowCheck1776 : row1776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1776 := by decide +kernel

theorem rowEval1776 (x : Key → ℝ) : Integer.Sparse.eval row1776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1776, Integer.Sparse.eval_collectBalanced, rawRowCheck1776]

theorem rawRowCheck1777 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1777 := by decide +kernel

theorem rowCheck1777 : row1777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1777 := by decide +kernel

theorem rowEval1777 (x : Key → ℝ) : Integer.Sparse.eval row1777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1777, Integer.Sparse.eval_collectBalanced, rawRowCheck1777]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1792 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1792 := by decide +kernel

theorem rowCheck1792 : row1792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1792 := by decide +kernel

theorem rowEval1792 (x : Key → ℝ) : Integer.Sparse.eval row1792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1792, Integer.Sparse.eval_collectBalanced, rawRowCheck1792]

theorem rawRowCheck1793 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1793 := by decide +kernel

theorem rowCheck1793 : row1793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1793 := by decide +kernel

theorem rowEval1793 (x : Key → ℝ) : Integer.Sparse.eval row1793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1793, Integer.Sparse.eval_collectBalanced, rawRowCheck1793]

theorem rawRowCheck1794 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1794 := by decide +kernel

theorem rowCheck1794 : row1794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1794 := by decide +kernel

theorem rowEval1794 (x : Key → ℝ) : Integer.Sparse.eval row1794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1794, Integer.Sparse.eval_collectBalanced, rawRowCheck1794]

theorem rawRowCheck1795 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1795 := by decide +kernel

theorem rowCheck1795 : row1795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1795 := by decide +kernel

theorem rowEval1795 (x : Key → ℝ) : Integer.Sparse.eval row1795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1795, Integer.Sparse.eval_collectBalanced, rawRowCheck1795]

theorem rawRowCheck1796 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2 = rawRow1796 := by decide +kernel

theorem rowCheck1796 : row1796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1796 := by decide +kernel

theorem rowEval1796 (x : Key → ℝ) : Integer.Sparse.eval row1796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1796, Integer.Sparse.eval_collectBalanced, rawRowCheck1796]

theorem rawRowCheck1797 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2 = rawRow1797 := by decide +kernel

theorem rowCheck1797 : row1797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1797 := by decide +kernel

theorem rowEval1797 (x : Key → ℝ) : Integer.Sparse.eval row1797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1797, Integer.Sparse.eval_collectBalanced, rawRowCheck1797]

theorem rawRowCheck1798 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2 = rawRow1798 := by decide +kernel

theorem rowCheck1798 : row1798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1798 := by decide +kernel

theorem rowEval1798 (x : Key → ℝ) : Integer.Sparse.eval row1798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1798, Integer.Sparse.eval_collectBalanced, rawRowCheck1798]

theorem rawRowCheck1799 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1799 := by decide +kernel

theorem rowCheck1799 : row1799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1799 := by decide +kernel

theorem rowEval1799 (x : Key → ℝ) : Integer.Sparse.eval row1799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1799, Integer.Sparse.eval_collectBalanced, rawRowCheck1799]

theorem rawRowCheck1800 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1800 := by decide +kernel

theorem rowCheck1800 : row1800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1800 := by decide +kernel

theorem rowEval1800 (x : Key → ℝ) : Integer.Sparse.eval row1800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1800, Integer.Sparse.eval_collectBalanced, rawRowCheck1800]

theorem rawRowCheck1801 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1801 := by decide +kernel

theorem rowCheck1801 : row1801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1801 := by decide +kernel

theorem rowEval1801 (x : Key → ℝ) : Integer.Sparse.eval row1801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1801, Integer.Sparse.eval_collectBalanced, rawRowCheck1801]

theorem rawRowCheck1802 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1802 := by decide +kernel

theorem rowCheck1802 : row1802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1802 := by decide +kernel

theorem rowEval1802 (x : Key → ℝ) : Integer.Sparse.eval row1802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1802, Integer.Sparse.eval_collectBalanced, rawRowCheck1802]

theorem rawRowCheck1803 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1803 := by decide +kernel

theorem rowCheck1803 : row1803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1803 := by decide +kernel

theorem rowEval1803 (x : Key → ℝ) : Integer.Sparse.eval row1803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1803, Integer.Sparse.eval_collectBalanced, rawRowCheck1803]

theorem rawRowCheck1804 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1804 := by decide +kernel

theorem rowCheck1804 : row1804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1804 := by decide +kernel

theorem rowEval1804 (x : Key → ℝ) : Integer.Sparse.eval row1804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1804, Integer.Sparse.eval_collectBalanced, rawRowCheck1804]

theorem rawRowCheck1805 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1805 := by decide +kernel

theorem rowCheck1805 : row1805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1805 := by decide +kernel

theorem rowEval1805 (x : Key → ℝ) : Integer.Sparse.eval row1805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1805, Integer.Sparse.eval_collectBalanced, rawRowCheck1805]

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

theorem rawRowCheck1834 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1834 := by decide +kernel

theorem rowCheck1834 : row1834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1834 := by decide +kernel

theorem rowEval1834 (x : Key → ℝ) : Integer.Sparse.eval row1834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1834, Integer.Sparse.eval_collectBalanced, rawRowCheck1834]

theorem rawRowCheck1835 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1835 := by decide +kernel

theorem rowCheck1835 : row1835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1835 := by decide +kernel

theorem rowEval1835 (x : Key → ℝ) : Integer.Sparse.eval row1835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1835, Integer.Sparse.eval_collectBalanced, rawRowCheck1835]

theorem rawRowCheck1836 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1836 := by decide +kernel

theorem rowCheck1836 : row1836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1836 := by decide +kernel

theorem rowEval1836 (x : Key → ℝ) : Integer.Sparse.eval row1836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1836, Integer.Sparse.eval_collectBalanced, rawRowCheck1836]

theorem rawRowCheck1837 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1837 := by decide +kernel

theorem rowCheck1837 : row1837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1837 := by decide +kernel

theorem rowEval1837 (x : Key → ℝ) : Integer.Sparse.eval row1837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1837, Integer.Sparse.eval_collectBalanced, rawRowCheck1837]

theorem rawRowCheck1838 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1838 := by decide +kernel

theorem rowCheck1838 : row1838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1838 := by decide +kernel

theorem rowEval1838 (x : Key → ℝ) : Integer.Sparse.eval row1838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1838, Integer.Sparse.eval_collectBalanced, rawRowCheck1838]

theorem rawRowCheck1839 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1839 := by decide +kernel

theorem rowCheck1839 : row1839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1839 := by decide +kernel

theorem rowEval1839 (x : Key → ℝ) : Integer.Sparse.eval row1839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1839, Integer.Sparse.eval_collectBalanced, rawRowCheck1839]

theorem rawRowCheck1840 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1840 := by decide +kernel

theorem rowCheck1840 : row1840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1840 := by decide +kernel

theorem rowEval1840 (x : Key → ℝ) : Integer.Sparse.eval row1840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1840, Integer.Sparse.eval_collectBalanced, rawRowCheck1840]

theorem rawRowCheck1841 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1841 := by decide +kernel

theorem rowCheck1841 : row1841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1841 := by decide +kernel

theorem rowEval1841 (x : Key → ℝ) : Integer.Sparse.eval row1841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1841, Integer.Sparse.eval_collectBalanced, rawRowCheck1841]

theorem rawRowCheck1842 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1842 := by decide +kernel

theorem rowCheck1842 : row1842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1842 := by decide +kernel

theorem rowEval1842 (x : Key → ℝ) : Integer.Sparse.eval row1842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1842, Integer.Sparse.eval_collectBalanced, rawRowCheck1842]

theorem rawRowCheck1843 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1843 := by decide +kernel

theorem rowCheck1843 : row1843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1843 := by decide +kernel

theorem rowEval1843 (x : Key → ℝ) : Integer.Sparse.eval row1843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1843, Integer.Sparse.eval_collectBalanced, rawRowCheck1843]

theorem rawRowCheck1844 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form5 = rawRow1844 := by decide +kernel

theorem rowCheck1844 : row1844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1844 := by decide +kernel

theorem rowEval1844 (x : Key → ℝ) : Integer.Sparse.eval row1844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1844, Integer.Sparse.eval_collectBalanced, rawRowCheck1844]

theorem rawRowCheck1845 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form5 = rawRow1845 := by decide +kernel

theorem rowCheck1845 : row1845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1845 := by decide +kernel

theorem rowEval1845 (x : Key → ℝ) : Integer.Sparse.eval row1845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1845, Integer.Sparse.eval_collectBalanced, rawRowCheck1845]

theorem rawRowCheck1846 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form5 = rawRow1846 := by decide +kernel

theorem rowCheck1846 : row1846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1846 := by decide +kernel

theorem rowEval1846 (x : Key → ℝ) : Integer.Sparse.eval row1846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1846, Integer.Sparse.eval_collectBalanced, rawRowCheck1846]

theorem rawRowCheck1847 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form5 = rawRow1847 := by decide +kernel

theorem rowCheck1847 : row1847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1847 := by decide +kernel

theorem rowEval1847 (x : Key → ℝ) : Integer.Sparse.eval row1847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form5) x := by
  rw [rowCheck1847, Integer.Sparse.eval_collectBalanced, rawRowCheck1847]

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

theorem rawRowCheck1904 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form10 = rawRow1904 := by decide +kernel

theorem rowCheck1904 : row1904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1904 := by decide +kernel

theorem rowEval1904 (x : Key → ℝ) : Integer.Sparse.eval row1904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck1904, Integer.Sparse.eval_collectBalanced, rawRowCheck1904]

theorem rawRowCheck1905 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form10 = rawRow1905 := by decide +kernel

theorem rowCheck1905 : row1905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1905 := by decide +kernel

theorem rowEval1905 (x : Key → ℝ) : Integer.Sparse.eval row1905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1905, Integer.Sparse.eval_collectBalanced, rawRowCheck1905]

theorem rawRowCheck1906 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form10 = rawRow1906 := by decide +kernel

theorem rowCheck1906 : row1906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1906 := by decide +kernel

theorem rowEval1906 (x : Key → ℝ) : Integer.Sparse.eval row1906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1906, Integer.Sparse.eval_collectBalanced, rawRowCheck1906]

theorem rawRowCheck1907 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow1907 := by decide +kernel

theorem rowCheck1907 : row1907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1907 := by decide +kernel

theorem rowEval1907 (x : Key → ℝ) : Integer.Sparse.eval row1907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1907, Integer.Sparse.eval_collectBalanced, rawRowCheck1907]

theorem rawRowCheck1908 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form10 = rawRow1908 := by decide +kernel

theorem rowCheck1908 : row1908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1908 := by decide +kernel

theorem rowEval1908 (x : Key → ℝ) : Integer.Sparse.eval row1908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck1908, Integer.Sparse.eval_collectBalanced, rawRowCheck1908]

theorem rawRowCheck1909 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form10 = rawRow1909 := by decide +kernel

theorem rowCheck1909 : row1909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1909 := by decide +kernel

theorem rowEval1909 (x : Key → ℝ) : Integer.Sparse.eval row1909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1909, Integer.Sparse.eval_collectBalanced, rawRowCheck1909]

theorem rawRowCheck1910 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form10 = rawRow1910 := by decide +kernel

theorem rowCheck1910 : row1910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1910 := by decide +kernel

theorem rowEval1910 (x : Key → ℝ) : Integer.Sparse.eval row1910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1910, Integer.Sparse.eval_collectBalanced, rawRowCheck1910]

theorem rawRowCheck1911 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form10 = rawRow1911 := by decide +kernel

theorem rowCheck1911 : row1911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1911 := by decide +kernel

theorem rowEval1911 (x : Key → ℝ) : Integer.Sparse.eval row1911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1911, Integer.Sparse.eval_collectBalanced, rawRowCheck1911]

theorem rawRowCheck1912 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form10 = rawRow1912 := by decide +kernel

theorem rowCheck1912 : row1912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1912 := by decide +kernel

theorem rowEval1912 (x : Key → ℝ) : Integer.Sparse.eval row1912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1912, Integer.Sparse.eval_collectBalanced, rawRowCheck1912]

theorem rawRowCheck1913 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form10 = rawRow1913 := by decide +kernel

theorem rowCheck1913 : row1913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1913 := by decide +kernel

theorem rowEval1913 (x : Key → ℝ) : Integer.Sparse.eval row1913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck1913, Integer.Sparse.eval_collectBalanced, rawRowCheck1913]

theorem rawRowCheck1914 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form10 = rawRow1914 := by decide +kernel

theorem rowCheck1914 : row1914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1914 := by decide +kernel

theorem rowEval1914 (x : Key → ℝ) : Integer.Sparse.eval row1914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1914, Integer.Sparse.eval_collectBalanced, rawRowCheck1914]

theorem rawRowCheck1915 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form10 = rawRow1915 := by decide +kernel

theorem rowCheck1915 : row1915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1915 := by decide +kernel

theorem rowEval1915 (x : Key → ℝ) : Integer.Sparse.eval row1915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1915, Integer.Sparse.eval_collectBalanced, rawRowCheck1915]

theorem rawRowCheck1916 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form10 = rawRow1916 := by decide +kernel

theorem rowCheck1916 : row1916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1916 := by decide +kernel

theorem rowEval1916 (x : Key → ℝ) : Integer.Sparse.eval row1916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck1916, Integer.Sparse.eval_collectBalanced, rawRowCheck1916]

theorem rawRowCheck1917 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form10 = rawRow1917 := by decide +kernel

theorem rowCheck1917 : row1917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1917 := by decide +kernel

theorem rowEval1917 (x : Key → ℝ) : Integer.Sparse.eval row1917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck1917, Integer.Sparse.eval_collectBalanced, rawRowCheck1917]

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

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1764 x
  · exact rowEval1765 x
  · exact rowEval1766 x
  · exact rowEval1767 x
  · exact rowEval1768 x
  · exact rowEval1769 x
  · exact rowEval1770 x
  · exact rowEval1771 x
  · exact rowEval1772 x
  · exact rowEval1773 x
  · exact rowEval1774 x
  · exact rowEval1775 x
  · exact rowEval1776 x
  · exact rowEval1777 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

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

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1792 x
  · exact rowEval1793 x
  · exact rowEval1794 x
  · exact rowEval1795 x
  · exact rowEval1796 x
  · exact rowEval1797 x
  · exact rowEval1798 x
  · exact rowEval1799 x
  · exact rowEval1800 x
  · exact rowEval1801 x
  · exact rowEval1802 x
  · exact rowEval1803 x
  · exact rowEval1804 x
  · exact rowEval1805 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

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

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1834 x
  · exact rowEval1835 x
  · exact rowEval1836 x
  · exact rowEval1837 x
  · exact rowEval1838 x
  · exact rowEval1839 x
  · exact rowEval1840 x
  · exact rowEval1841 x
  · exact rowEval1842 x
  · exact rowEval1843 x
  · exact rowEval1844 x
  · exact rowEval1845 x
  · exact rowEval1846 x
  · exact rowEval1847 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

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

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval1904 x
  · exact rowEval1905 x
  · exact rowEval1906 x
  · exact rowEval1907 x
  · exact rowEval1908 x
  · exact rowEval1909 x
  · exact rowEval1910 x
  · exact rowEval1911 x
  · exact rowEval1912 x
  · exact rowEval1913 x
  · exact rowEval1914 x
  · exact rowEval1915 x
  · exact rowEval1916 x
  · exact rowEval1917 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck2616 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form10 = rawRow2616 := by decide +kernel

theorem rowCheck2616 : row2616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2616 := by decide +kernel

theorem rowEval2616 (x : Key → ℝ) : Integer.Sparse.eval row2616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2616, Integer.Sparse.eval_collectBalanced, rawRowCheck2616]

theorem rawRowCheck2617 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form10 = rawRow2617 := by decide +kernel

theorem rowCheck2617 : row2617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2617 := by decide +kernel

theorem rowEval2617 (x : Key → ℝ) : Integer.Sparse.eval row2617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2617, Integer.Sparse.eval_collectBalanced, rawRowCheck2617]

theorem rawRowCheck2618 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form10 = rawRow2618 := by decide +kernel

theorem rowCheck2618 : row2618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2618 := by decide +kernel

theorem rowEval2618 (x : Key → ℝ) : Integer.Sparse.eval row2618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2618, Integer.Sparse.eval_collectBalanced, rawRowCheck2618]

theorem rawRowCheck2619 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2619 := by decide +kernel

theorem rowCheck2619 : row2619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2619 := by decide +kernel

theorem rowEval2619 (x : Key → ℝ) : Integer.Sparse.eval row2619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2619, Integer.Sparse.eval_collectBalanced, rawRowCheck2619]

theorem rawRowCheck2620 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form10 = rawRow2620 := by decide +kernel

theorem rowCheck2620 : row2620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2620 := by decide +kernel

theorem rowEval2620 (x : Key → ℝ) : Integer.Sparse.eval row2620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2620, Integer.Sparse.eval_collectBalanced, rawRowCheck2620]

theorem rawRowCheck2621 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form10 = rawRow2621 := by decide +kernel

theorem rowCheck2621 : row2621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2621 := by decide +kernel

theorem rowEval2621 (x : Key → ℝ) : Integer.Sparse.eval row2621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2621, Integer.Sparse.eval_collectBalanced, rawRowCheck2621]

theorem rawRowCheck2622 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form10 = rawRow2622 := by decide +kernel

theorem rowCheck2622 : row2622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2622 := by decide +kernel

theorem rowEval2622 (x : Key → ℝ) : Integer.Sparse.eval row2622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2622, Integer.Sparse.eval_collectBalanced, rawRowCheck2622]

theorem rawRowCheck2623 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form10 = rawRow2623 := by decide +kernel

theorem rowCheck2623 : row2623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2623 := by decide +kernel

theorem rowEval2623 (x : Key → ℝ) : Integer.Sparse.eval row2623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2623, Integer.Sparse.eval_collectBalanced, rawRowCheck2623]

theorem rawRowCheck2624 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form10 = rawRow2624 := by decide +kernel

theorem rowCheck2624 : row2624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2624 := by decide +kernel

theorem rowEval2624 (x : Key → ℝ) : Integer.Sparse.eval row2624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2624, Integer.Sparse.eval_collectBalanced, rawRowCheck2624]

theorem rawRowCheck2625 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form10 = rawRow2625 := by decide +kernel

theorem rowCheck2625 : row2625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2625 := by decide +kernel

theorem rowEval2625 (x : Key → ℝ) : Integer.Sparse.eval row2625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2625, Integer.Sparse.eval_collectBalanced, rawRowCheck2625]

theorem rawRowCheck2626 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2626 := by decide +kernel

theorem rowCheck2626 : row2626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2626 := by decide +kernel

theorem rowEval2626 (x : Key → ℝ) : Integer.Sparse.eval row2626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2626, Integer.Sparse.eval_collectBalanced, rawRowCheck2626]

theorem rawRowCheck2627 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form10 = rawRow2627 := by decide +kernel

theorem rowCheck2627 : row2627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2627 := by decide +kernel

theorem rowEval2627 (x : Key → ℝ) : Integer.Sparse.eval row2627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2627, Integer.Sparse.eval_collectBalanced, rawRowCheck2627]

theorem rawRowCheck2628 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form10 = rawRow2628 := by decide +kernel

theorem rowCheck2628 : row2628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2628 := by decide +kernel

theorem rowEval2628 (x : Key → ℝ) : Integer.Sparse.eval row2628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2628, Integer.Sparse.eval_collectBalanced, rawRowCheck2628]

theorem rawRowCheck2629 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form10 = rawRow2629 := by decide +kernel

theorem rowCheck2629 : row2629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2629 := by decide +kernel

theorem rowEval2629 (x : Key → ℝ) : Integer.Sparse.eval row2629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2629, Integer.Sparse.eval_collectBalanced, rawRowCheck2629]

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

theorem entryCheck13_10 : entry13_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_10 k)) := by decide +kernel

theorem rowsSound13_10 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2616 x
  · exact rowEval2617 x
  · exact rowEval2618 x
  · exact rowEval2619 x
  · exact rowEval2620 x
  · exact rowEval2621 x
  · exact rowEval2622 x
  · exact rowEval2623 x
  · exact rowEval2624 x
  · exact rowEval2625 x
  · exact rowEval2626 x
  · exact rowEval2627 x
  · exact rowEval2628 x
  · exact rowEval2629 x

theorem entryEval13_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_10 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck13_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_10]

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

theorem rawRowCheck2912 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form10 = rawRow2912 := by decide +kernel

theorem rowCheck2912 : row2912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2912 := by decide +kernel

theorem rowEval2912 (x : Key → ℝ) : Integer.Sparse.eval row2912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2912, Integer.Sparse.eval_collectBalanced, rawRowCheck2912]

theorem rawRowCheck2913 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form10 = rawRow2913 := by decide +kernel

theorem rowCheck2913 : row2913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2913 := by decide +kernel

theorem rowEval2913 (x : Key → ℝ) : Integer.Sparse.eval row2913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2913, Integer.Sparse.eval_collectBalanced, rawRowCheck2913]

theorem rawRowCheck2914 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form10 = rawRow2914 := by decide +kernel

theorem rowCheck2914 : row2914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2914 := by decide +kernel

theorem rowEval2914 (x : Key → ℝ) : Integer.Sparse.eval row2914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2914, Integer.Sparse.eval_collectBalanced, rawRowCheck2914]

theorem rawRowCheck2915 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2915 := by decide +kernel

theorem rowCheck2915 : row2915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2915 := by decide +kernel

theorem rowEval2915 (x : Key → ℝ) : Integer.Sparse.eval row2915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2915, Integer.Sparse.eval_collectBalanced, rawRowCheck2915]

theorem rawRowCheck2916 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2916 := by decide +kernel

theorem rowCheck2916 : row2916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2916 := by decide +kernel

theorem rowEval2916 (x : Key → ℝ) : Integer.Sparse.eval row2916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2916, Integer.Sparse.eval_collectBalanced, rawRowCheck2916]

theorem rawRowCheck2917 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2917 := by decide +kernel

theorem rowCheck2917 : row2917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2917 := by decide +kernel

theorem rowEval2917 (x : Key → ℝ) : Integer.Sparse.eval row2917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2917, Integer.Sparse.eval_collectBalanced, rawRowCheck2917]

theorem rawRowCheck2918 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form10 = rawRow2918 := by decide +kernel

theorem rowCheck2918 : row2918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2918 := by decide +kernel

theorem rowEval2918 (x : Key → ℝ) : Integer.Sparse.eval row2918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2918, Integer.Sparse.eval_collectBalanced, rawRowCheck2918]

theorem rawRowCheck2919 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form10 = rawRow2919 := by decide +kernel

theorem rowCheck2919 : row2919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2919 := by decide +kernel

theorem rowEval2919 (x : Key → ℝ) : Integer.Sparse.eval row2919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2919, Integer.Sparse.eval_collectBalanced, rawRowCheck2919]

theorem rawRowCheck2920 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form10 = rawRow2920 := by decide +kernel

theorem rowCheck2920 : row2920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2920 := by decide +kernel

theorem rowEval2920 (x : Key → ℝ) : Integer.Sparse.eval row2920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2920, Integer.Sparse.eval_collectBalanced, rawRowCheck2920]

theorem rawRowCheck2921 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form10 = rawRow2921 := by decide +kernel

theorem rowCheck2921 : row2921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2921 := by decide +kernel

theorem rowEval2921 (x : Key → ℝ) : Integer.Sparse.eval row2921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2921, Integer.Sparse.eval_collectBalanced, rawRowCheck2921]

theorem rawRowCheck2922 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form10 = rawRow2922 := by decide +kernel

theorem rowCheck2922 : row2922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2922 := by decide +kernel

theorem rowEval2922 (x : Key → ℝ) : Integer.Sparse.eval row2922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2922, Integer.Sparse.eval_collectBalanced, rawRowCheck2922]

theorem rawRowCheck2923 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form10 = rawRow2923 := by decide +kernel

theorem rowCheck2923 : row2923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2923 := by decide +kernel

theorem rowEval2923 (x : Key → ℝ) : Integer.Sparse.eval row2923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2923, Integer.Sparse.eval_collectBalanced, rawRowCheck2923]

theorem rawRowCheck2924 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form10 = rawRow2924 := by decide +kernel

theorem rowCheck2924 : row2924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2924 := by decide +kernel

theorem rowEval2924 (x : Key → ℝ) : Integer.Sparse.eval row2924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2924, Integer.Sparse.eval_collectBalanced, rawRowCheck2924]

theorem rawRowCheck2925 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form10 = rawRow2925 := by decide +kernel

theorem rowCheck2925 : row2925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2925 := by decide +kernel

theorem rowEval2925 (x : Key → ℝ) : Integer.Sparse.eval row2925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2925, Integer.Sparse.eval_collectBalanced, rawRowCheck2925]

theorem rawRowCheck2926 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form10 = rawRow2926 := by decide +kernel

theorem rowCheck2926 : row2926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2926 := by decide +kernel

theorem rowEval2926 (x : Key → ℝ) : Integer.Sparse.eval row2926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2926, Integer.Sparse.eval_collectBalanced, rawRowCheck2926]

theorem rawRowCheck2927 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2927 := by decide +kernel

theorem rowCheck2927 : row2927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2927 := by decide +kernel

theorem rowEval2927 (x : Key → ℝ) : Integer.Sparse.eval row2927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2927, Integer.Sparse.eval_collectBalanced, rawRowCheck2927]

theorem rawRowCheck2928 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2928 := by decide +kernel

theorem rowCheck2928 : row2928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2928 := by decide +kernel

theorem rowEval2928 (x : Key → ℝ) : Integer.Sparse.eval row2928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2928, Integer.Sparse.eval_collectBalanced, rawRowCheck2928]

theorem rawRowCheck2929 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2929 := by decide +kernel

theorem rowCheck2929 : row2929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2929 := by decide +kernel

theorem rowEval2929 (x : Key → ℝ) : Integer.Sparse.eval row2929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2929, Integer.Sparse.eval_collectBalanced, rawRowCheck2929]

theorem rawRowCheck2930 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form10 = rawRow2930 := by decide +kernel

theorem rowCheck2930 : row2930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2930 := by decide +kernel

theorem rowEval2930 (x : Key → ℝ) : Integer.Sparse.eval row2930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2930, Integer.Sparse.eval_collectBalanced, rawRowCheck2930]

theorem rawRowCheck2931 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form10 = rawRow2931 := by decide +kernel

theorem rowCheck2931 : row2931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2931 := by decide +kernel

theorem rowEval2931 (x : Key → ℝ) : Integer.Sparse.eval row2931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2931, Integer.Sparse.eval_collectBalanced, rawRowCheck2931]

theorem rawRowCheck2932 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form10 = rawRow2932 := by decide +kernel

theorem rowCheck2932 : row2932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2932 := by decide +kernel

theorem rowEval2932 (x : Key → ℝ) : Integer.Sparse.eval row2932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2932, Integer.Sparse.eval_collectBalanced, rawRowCheck2932]

theorem rawRowCheck2933 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form10 = rawRow2933 := by decide +kernel

theorem rowCheck2933 : row2933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2933 := by decide +kernel

theorem rowEval2933 (x : Key → ℝ) : Integer.Sparse.eval row2933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2933, Integer.Sparse.eval_collectBalanced, rawRowCheck2933]

theorem rawRowCheck2934 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form10 = rawRow2934 := by decide +kernel

theorem rowCheck2934 : row2934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2934 := by decide +kernel

theorem rowEval2934 (x : Key → ℝ) : Integer.Sparse.eval row2934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2934, Integer.Sparse.eval_collectBalanced, rawRowCheck2934]

theorem rawRowCheck2935 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form10 = rawRow2935 := by decide +kernel

theorem rowCheck2935 : row2935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2935 := by decide +kernel

theorem rowEval2935 (x : Key → ℝ) : Integer.Sparse.eval row2935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2935, Integer.Sparse.eval_collectBalanced, rawRowCheck2935]

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

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2912 x
  · exact rowEval2913 x
  · exact rowEval2914 x
  · exact rowEval2915 x
  · exact rowEval2916 x
  · exact rowEval2917 x
  · exact rowEval2918 x
  · exact rowEval2919 x
  · exact rowEval2920 x
  · exact rowEval2921 x
  · exact rowEval2922 x
  · exact rowEval2923 x
  · exact rowEval2924 x
  · exact rowEval2925 x
  · exact rowEval2926 x
  · exact rowEval2927 x
  · exact rowEval2928 x
  · exact rowEval2929 x
  · exact rowEval2930 x
  · exact rowEval2931 x
  · exact rowEval2932 x
  · exact rowEval2933 x
  · exact rowEval2934 x
  · exact rowEval2935 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

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

theorem rawRowCheck4696 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4696 := by decide +kernel

theorem rowCheck4696 : row4696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4696 := by decide +kernel

theorem rowEval4696 (x : Key → ℝ) : Integer.Sparse.eval row4696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4696, Integer.Sparse.eval_collectBalanced, rawRowCheck4696]

theorem rawRowCheck4697 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4697 := by decide +kernel

theorem rowCheck4697 : row4697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4697 := by decide +kernel

theorem rowEval4697 (x : Key → ℝ) : Integer.Sparse.eval row4697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4697, Integer.Sparse.eval_collectBalanced, rawRowCheck4697]

theorem rawRowCheck4698 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4698 := by decide +kernel

theorem rowCheck4698 : row4698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4698 := by decide +kernel

theorem rowEval4698 (x : Key → ℝ) : Integer.Sparse.eval row4698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4698, Integer.Sparse.eval_collectBalanced, rawRowCheck4698]

theorem rawRowCheck4699 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4699 := by decide +kernel

theorem rowCheck4699 : row4699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4699 := by decide +kernel

theorem rowEval4699 (x : Key → ℝ) : Integer.Sparse.eval row4699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4699, Integer.Sparse.eval_collectBalanced, rawRowCheck4699]

theorem rawRowCheck4700 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4700 := by decide +kernel

theorem rowCheck4700 : row4700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4700 := by decide +kernel

theorem rowEval4700 (x : Key → ℝ) : Integer.Sparse.eval row4700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4700, Integer.Sparse.eval_collectBalanced, rawRowCheck4700]

theorem rawRowCheck4701 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4701 := by decide +kernel

theorem rowCheck4701 : row4701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4701 := by decide +kernel

theorem rowEval4701 (x : Key → ℝ) : Integer.Sparse.eval row4701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4701, Integer.Sparse.eval_collectBalanced, rawRowCheck4701]

theorem rawRowCheck4702 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4702 := by decide +kernel

theorem rowCheck4702 : row4702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4702 := by decide +kernel

theorem rowEval4702 (x : Key → ℝ) : Integer.Sparse.eval row4702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4702, Integer.Sparse.eval_collectBalanced, rawRowCheck4702]

theorem rawRowCheck4703 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4703 := by decide +kernel

theorem rowCheck4703 : row4703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4703 := by decide +kernel

theorem rowEval4703 (x : Key → ℝ) : Integer.Sparse.eval row4703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4703, Integer.Sparse.eval_collectBalanced, rawRowCheck4703]

theorem rawRowCheck4704 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4704 := by decide +kernel

theorem rowCheck4704 : row4704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4704 := by decide +kernel

theorem rowEval4704 (x : Key → ℝ) : Integer.Sparse.eval row4704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4704, Integer.Sparse.eval_collectBalanced, rawRowCheck4704]

theorem rawRowCheck4705 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4705 := by decide +kernel

theorem rowCheck4705 : row4705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4705 := by decide +kernel

theorem rowEval4705 (x : Key → ℝ) : Integer.Sparse.eval row4705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4705, Integer.Sparse.eval_collectBalanced, rawRowCheck4705]

theorem rawRowCheck4706 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4706 := by decide +kernel

theorem rowCheck4706 : row4706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4706 := by decide +kernel

theorem rowEval4706 (x : Key → ℝ) : Integer.Sparse.eval row4706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4706, Integer.Sparse.eval_collectBalanced, rawRowCheck4706]

theorem rawRowCheck4707 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4707 := by decide +kernel

theorem rowCheck4707 : row4707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4707 := by decide +kernel

theorem rowEval4707 (x : Key → ℝ) : Integer.Sparse.eval row4707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4707, Integer.Sparse.eval_collectBalanced, rawRowCheck4707]

theorem rawRowCheck4708 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4708 := by decide +kernel

theorem rowCheck4708 : row4708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4708 := by decide +kernel

theorem rowEval4708 (x : Key → ℝ) : Integer.Sparse.eval row4708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4708, Integer.Sparse.eval_collectBalanced, rawRowCheck4708]

theorem rawRowCheck4709 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4709 := by decide +kernel

theorem rowCheck4709 : row4709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4709 := by decide +kernel

theorem rowEval4709 (x : Key → ℝ) : Integer.Sparse.eval row4709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4709, Integer.Sparse.eval_collectBalanced, rawRowCheck4709]

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

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4696 x
  · exact rowEval4697 x
  · exact rowEval4698 x
  · exact rowEval4699 x
  · exact rowEval4700 x
  · exact rowEval4701 x
  · exact rowEval4702 x
  · exact rowEval4703 x
  · exact rowEval4704 x
  · exact rowEval4705 x
  · exact rowEval4706 x
  · exact rowEval4707 x
  · exact rowEval4708 x
  · exact rowEval4709 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

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

theorem rawRowCheck4950 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4950 := by decide +kernel

theorem rowCheck4950 : row4950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4950 := by decide +kernel

theorem rowEval4950 (x : Key → ℝ) : Integer.Sparse.eval row4950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4950, Integer.Sparse.eval_collectBalanced, rawRowCheck4950]

theorem rawRowCheck4951 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4951 := by decide +kernel

theorem rowCheck4951 : row4951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4951 := by decide +kernel

theorem rowEval4951 (x : Key → ℝ) : Integer.Sparse.eval row4951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4951, Integer.Sparse.eval_collectBalanced, rawRowCheck4951]

theorem rawRowCheck4952 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4952 := by decide +kernel

theorem rowCheck4952 : row4952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4952 := by decide +kernel

theorem rowEval4952 (x : Key → ℝ) : Integer.Sparse.eval row4952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4952, Integer.Sparse.eval_collectBalanced, rawRowCheck4952]

theorem rawRowCheck4953 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4953 := by decide +kernel

theorem rowCheck4953 : row4953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4953 := by decide +kernel

theorem rowEval4953 (x : Key → ℝ) : Integer.Sparse.eval row4953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4953, Integer.Sparse.eval_collectBalanced, rawRowCheck4953]

theorem rawRowCheck4954 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4954 := by decide +kernel

theorem rowCheck4954 : row4954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4954 := by decide +kernel

theorem rowEval4954 (x : Key → ℝ) : Integer.Sparse.eval row4954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4954, Integer.Sparse.eval_collectBalanced, rawRowCheck4954]

theorem rawRowCheck4955 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4955 := by decide +kernel

theorem rowCheck4955 : row4955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4955 := by decide +kernel

theorem rowEval4955 (x : Key → ℝ) : Integer.Sparse.eval row4955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4955, Integer.Sparse.eval_collectBalanced, rawRowCheck4955]

theorem rawRowCheck4956 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10 = rawRow4956 := by decide +kernel

theorem rowCheck4956 : row4956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4956 := by decide +kernel

theorem rowEval4956 (x : Key → ℝ) : Integer.Sparse.eval row4956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4956, Integer.Sparse.eval_collectBalanced, rawRowCheck4956]

theorem rawRowCheck4957 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10 = rawRow4957 := by decide +kernel

theorem rowCheck4957 : row4957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4957 := by decide +kernel

theorem rowEval4957 (x : Key → ℝ) : Integer.Sparse.eval row4957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4957, Integer.Sparse.eval_collectBalanced, rawRowCheck4957]

theorem rawRowCheck4958 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10 = rawRow4958 := by decide +kernel

theorem rowCheck4958 : row4958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4958 := by decide +kernel

theorem rowEval4958 (x : Key → ℝ) : Integer.Sparse.eval row4958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4958, Integer.Sparse.eval_collectBalanced, rawRowCheck4958]

theorem rawRowCheck4959 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4959 := by decide +kernel

theorem rowCheck4959 : row4959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4959 := by decide +kernel

theorem rowEval4959 (x : Key → ℝ) : Integer.Sparse.eval row4959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4959, Integer.Sparse.eval_collectBalanced, rawRowCheck4959]

theorem rawRowCheck4960 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4960 := by decide +kernel

theorem rowCheck4960 : row4960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4960 := by decide +kernel

theorem rowEval4960 (x : Key → ℝ) : Integer.Sparse.eval row4960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4960, Integer.Sparse.eval_collectBalanced, rawRowCheck4960]

theorem rawRowCheck4961 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4961 := by decide +kernel

theorem rowCheck4961 : row4961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4961 := by decide +kernel

theorem rowEval4961 (x : Key → ℝ) : Integer.Sparse.eval row4961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4961, Integer.Sparse.eval_collectBalanced, rawRowCheck4961]

theorem rawRowCheck4962 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10 = rawRow4962 := by decide +kernel

theorem rowCheck4962 : row4962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4962 := by decide +kernel

theorem rowEval4962 (x : Key → ℝ) : Integer.Sparse.eval row4962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4962, Integer.Sparse.eval_collectBalanced, rawRowCheck4962]

theorem rawRowCheck4963 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10 = rawRow4963 := by decide +kernel

theorem rowCheck4963 : row4963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4963 := by decide +kernel

theorem rowEval4963 (x : Key → ℝ) : Integer.Sparse.eval row4963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4963, Integer.Sparse.eval_collectBalanced, rawRowCheck4963]

theorem rawRowCheck4964 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10 = rawRow4964 := by decide +kernel

theorem rowCheck4964 : row4964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4964 := by decide +kernel

theorem rowEval4964 (x : Key → ℝ) : Integer.Sparse.eval row4964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4964, Integer.Sparse.eval_collectBalanced, rawRowCheck4964]

theorem rawRowCheck4965 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10 = rawRow4965 := by decide +kernel

theorem rowCheck4965 : row4965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4965 := by decide +kernel

theorem rowEval4965 (x : Key → ℝ) : Integer.Sparse.eval row4965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4965, Integer.Sparse.eval_collectBalanced, rawRowCheck4965]

theorem rawRowCheck4966 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10 = rawRow4966 := by decide +kernel

theorem rowCheck4966 : row4966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4966 := by decide +kernel

theorem rowEval4966 (x : Key → ℝ) : Integer.Sparse.eval row4966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4966, Integer.Sparse.eval_collectBalanced, rawRowCheck4966]

theorem rawRowCheck4967 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10 = rawRow4967 := by decide +kernel

theorem rowCheck4967 : row4967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4967 := by decide +kernel

theorem rowEval4967 (x : Key → ℝ) : Integer.Sparse.eval row4967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4967, Integer.Sparse.eval_collectBalanced, rawRowCheck4967]

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

theorem entryCheck20_10 : entry20_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_10 k)) := by decide +kernel

theorem rowsSound20_10 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4950 x
  · exact rowEval4951 x
  · exact rowEval4952 x
  · exact rowEval4953 x
  · exact rowEval4954 x
  · exact rowEval4955 x
  · exact rowEval4956 x
  · exact rowEval4957 x
  · exact rowEval4958 x
  · exact rowEval4959 x
  · exact rowEval4960 x
  · exact rowEval4961 x
  · exact rowEval4962 x
  · exact rowEval4963 x
  · exact rowEval4964 x
  · exact rowEval4965 x
  · exact rowEval4966 x
  · exact rowEval4967 x

theorem entryEval20_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_10 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck20_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_10]

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

theorem entryEvalRow10_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 10).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval10_0 B hB
  · exact entryEval10_1 B hB
  · exact entryEval10_2 B hB
  · exact entryEval10_3 B hB
  · exact entryEval10_4 B hB
  · exact entryEval10_5 B hB
  · exact entryEval10_6 B hB
  · exact entryEval10_7 B hB
  · exact entryEval10_8 B hB
  · exact entryEval10_9 B hB
  · exact entryEval10_10 B hB
  · exact (entryEval11_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_10_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_10 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e_oai
