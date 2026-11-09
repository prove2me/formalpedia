-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:24:51.836977+00:00
-- url     : https://prove2.me/submissions/2dbb203e-5b60-4c0f-9a74-068ad7771fdc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E016
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_14_e

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

theorem rawRowCheck2984 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form13 = rawRow2984 := by decide +kernel

theorem rowCheck2984 : row2984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2984 := by decide +kernel

theorem rowEval2984 (x : Key → ℝ) : Integer.Sparse.eval row2984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2984, Integer.Sparse.eval_collectBalanced, rawRowCheck2984]

theorem rawRowCheck2985 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form13 = rawRow2985 := by decide +kernel

theorem rowCheck2985 : row2985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2985 := by decide +kernel

theorem rowEval2985 (x : Key → ℝ) : Integer.Sparse.eval row2985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2985, Integer.Sparse.eval_collectBalanced, rawRowCheck2985]

theorem rawRowCheck2986 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form13 = rawRow2986 := by decide +kernel

theorem rowCheck2986 : row2986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2986 := by decide +kernel

theorem rowEval2986 (x : Key → ℝ) : Integer.Sparse.eval row2986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2986, Integer.Sparse.eval_collectBalanced, rawRowCheck2986]

theorem rawRowCheck2987 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form13 = rawRow2987 := by decide +kernel

theorem rowCheck2987 : row2987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2987 := by decide +kernel

theorem rowEval2987 (x : Key → ℝ) : Integer.Sparse.eval row2987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2987, Integer.Sparse.eval_collectBalanced, rawRowCheck2987]

theorem rawRowCheck2988 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form13 = rawRow2988 := by decide +kernel

theorem rowCheck2988 : row2988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2988 := by decide +kernel

theorem rowEval2988 (x : Key → ℝ) : Integer.Sparse.eval row2988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2988, Integer.Sparse.eval_collectBalanced, rawRowCheck2988]

theorem rawRowCheck2989 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form13 = rawRow2989 := by decide +kernel

theorem rowCheck2989 : row2989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2989 := by decide +kernel

theorem rowEval2989 (x : Key → ℝ) : Integer.Sparse.eval row2989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2989, Integer.Sparse.eval_collectBalanced, rawRowCheck2989]

theorem rawRowCheck2990 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form13 = rawRow2990 := by decide +kernel

theorem rowCheck2990 : row2990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2990 := by decide +kernel

theorem rowEval2990 (x : Key → ℝ) : Integer.Sparse.eval row2990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2990, Integer.Sparse.eval_collectBalanced, rawRowCheck2990]

theorem rawRowCheck2991 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form13 = rawRow2991 := by decide +kernel

theorem rowCheck2991 : row2991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2991 := by decide +kernel

theorem rowEval2991 (x : Key → ℝ) : Integer.Sparse.eval row2991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2991, Integer.Sparse.eval_collectBalanced, rawRowCheck2991]

theorem rawRowCheck2992 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form13 = rawRow2992 := by decide +kernel

theorem rowCheck2992 : row2992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2992 := by decide +kernel

theorem rowEval2992 (x : Key → ℝ) : Integer.Sparse.eval row2992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2992, Integer.Sparse.eval_collectBalanced, rawRowCheck2992]

theorem rawRowCheck2993 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form13 = rawRow2993 := by decide +kernel

theorem rowCheck2993 : row2993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2993 := by decide +kernel

theorem rowEval2993 (x : Key → ℝ) : Integer.Sparse.eval row2993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2993, Integer.Sparse.eval_collectBalanced, rawRowCheck2993]

theorem rawRowCheck2994 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form13 = rawRow2994 := by decide +kernel

theorem rowCheck2994 : row2994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2994 := by decide +kernel

theorem rowEval2994 (x : Key → ℝ) : Integer.Sparse.eval row2994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2994, Integer.Sparse.eval_collectBalanced, rawRowCheck2994]

theorem rawRowCheck2995 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form13 = rawRow2995 := by decide +kernel

theorem rowCheck2995 : row2995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2995 := by decide +kernel

theorem rowEval2995 (x : Key → ℝ) : Integer.Sparse.eval row2995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2995, Integer.Sparse.eval_collectBalanced, rawRowCheck2995]

theorem rawRowCheck2996 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form13 = rawRow2996 := by decide +kernel

theorem rowCheck2996 : row2996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2996 := by decide +kernel

theorem rowEval2996 (x : Key → ℝ) : Integer.Sparse.eval row2996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck2996, Integer.Sparse.eval_collectBalanced, rawRowCheck2996]

theorem rawRowCheck2997 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form13 = rawRow2997 := by decide +kernel

theorem rowCheck2997 : row2997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2997 := by decide +kernel

theorem rowEval2997 (x : Key → ℝ) : Integer.Sparse.eval row2997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2997, Integer.Sparse.eval_collectBalanced, rawRowCheck2997]

theorem rawRowCheck2998 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form13 = rawRow2998 := by decide +kernel

theorem rowCheck2998 : row2998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2998 := by decide +kernel

theorem rowEval2998 (x : Key → ℝ) : Integer.Sparse.eval row2998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck2998, Integer.Sparse.eval_collectBalanced, rawRowCheck2998]

theorem rawRowCheck2999 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form13 = rawRow2999 := by decide +kernel

theorem rowCheck2999 : row2999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2999 := by decide +kernel

theorem rowEval2999 (x : Key → ℝ) : Integer.Sparse.eval row2999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2999, Integer.Sparse.eval_collectBalanced, rawRowCheck2999]

theorem rawRowCheck3000 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3000 := by decide +kernel

theorem rowCheck3000 : row3000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3000 := by decide +kernel

theorem rowEval3000 (x : Key → ℝ) : Integer.Sparse.eval row3000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3000, Integer.Sparse.eval_collectBalanced, rawRowCheck3000]

theorem rawRowCheck3001 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3001 := by decide +kernel

theorem rowCheck3001 : row3001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3001 := by decide +kernel

theorem rowEval3001 (x : Key → ℝ) : Integer.Sparse.eval row3001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3001, Integer.Sparse.eval_collectBalanced, rawRowCheck3001]

theorem rawRowCheck3002 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form13 = rawRow3002 := by decide +kernel

theorem rowCheck3002 : row3002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3002 := by decide +kernel

theorem rowEval3002 (x : Key → ℝ) : Integer.Sparse.eval row3002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3002, Integer.Sparse.eval_collectBalanced, rawRowCheck3002]

theorem rawRowCheck3003 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form13 = rawRow3003 := by decide +kernel

theorem rowCheck3003 : row3003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3003 := by decide +kernel

theorem rowEval3003 (x : Key → ℝ) : Integer.Sparse.eval row3003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3003, Integer.Sparse.eval_collectBalanced, rawRowCheck3003]

theorem rawRowCheck3004 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form13 = rawRow3004 := by decide +kernel

theorem rowCheck3004 : row3004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3004 := by decide +kernel

theorem rowEval3004 (x : Key → ℝ) : Integer.Sparse.eval row3004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3004, Integer.Sparse.eval_collectBalanced, rawRowCheck3004]

theorem rawRowCheck3005 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form13 = rawRow3005 := by decide +kernel

theorem rowCheck3005 : row3005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3005 := by decide +kernel

theorem rowEval3005 (x : Key → ℝ) : Integer.Sparse.eval row3005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck3005, Integer.Sparse.eval_collectBalanced, rawRowCheck3005]

theorem rawRowCheck3006 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form13 = rawRow3006 := by decide +kernel

theorem rowCheck3006 : row3006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3006 := by decide +kernel

theorem rowEval3006 (x : Key → ℝ) : Integer.Sparse.eval row3006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3006, Integer.Sparse.eval_collectBalanced, rawRowCheck3006]

theorem rawRowCheck3007 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form13 = rawRow3007 := by decide +kernel

theorem rowCheck3007 : row3007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3007 := by decide +kernel

theorem rowEval3007 (x : Key → ℝ) : Integer.Sparse.eval row3007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form13) x := by
  rw [rowCheck3007, Integer.Sparse.eval_collectBalanced, rawRowCheck3007]

theorem rawRowCheck3008 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form14 = rawRow3008 := by decide +kernel

theorem rowCheck3008 : row3008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3008 := by decide +kernel

theorem rowEval3008 (x : Key → ℝ) : Integer.Sparse.eval row3008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3008, Integer.Sparse.eval_collectBalanced, rawRowCheck3008]

theorem rawRowCheck3009 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form14 = rawRow3009 := by decide +kernel

theorem rowCheck3009 : row3009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3009 := by decide +kernel

theorem rowEval3009 (x : Key → ℝ) : Integer.Sparse.eval row3009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3009, Integer.Sparse.eval_collectBalanced, rawRowCheck3009]

theorem rawRowCheck3010 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form14 = rawRow3010 := by decide +kernel

theorem rowCheck3010 : row3010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3010 := by decide +kernel

theorem rowEval3010 (x : Key → ℝ) : Integer.Sparse.eval row3010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3010, Integer.Sparse.eval_collectBalanced, rawRowCheck3010]

theorem rawRowCheck3011 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3011 := by decide +kernel

theorem rowCheck3011 : row3011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3011 := by decide +kernel

theorem rowEval3011 (x : Key → ℝ) : Integer.Sparse.eval row3011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3011, Integer.Sparse.eval_collectBalanced, rawRowCheck3011]

theorem rawRowCheck3012 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3012 := by decide +kernel

theorem rowCheck3012 : row3012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3012 := by decide +kernel

theorem rowEval3012 (x : Key → ℝ) : Integer.Sparse.eval row3012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3012, Integer.Sparse.eval_collectBalanced, rawRowCheck3012]

theorem rawRowCheck3013 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3013 := by decide +kernel

theorem rowCheck3013 : row3013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3013 := by decide +kernel

theorem rowEval3013 (x : Key → ℝ) : Integer.Sparse.eval row3013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3013, Integer.Sparse.eval_collectBalanced, rawRowCheck3013]

theorem rawRowCheck3014 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form14 = rawRow3014 := by decide +kernel

theorem rowCheck3014 : row3014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3014 := by decide +kernel

theorem rowEval3014 (x : Key → ℝ) : Integer.Sparse.eval row3014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3014, Integer.Sparse.eval_collectBalanced, rawRowCheck3014]

theorem rawRowCheck3015 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form14 = rawRow3015 := by decide +kernel

theorem rowCheck3015 : row3015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3015 := by decide +kernel

theorem rowEval3015 (x : Key → ℝ) : Integer.Sparse.eval row3015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3015, Integer.Sparse.eval_collectBalanced, rawRowCheck3015]

theorem rawRowCheck3016 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form14 = rawRow3016 := by decide +kernel

theorem rowCheck3016 : row3016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3016 := by decide +kernel

theorem rowEval3016 (x : Key → ℝ) : Integer.Sparse.eval row3016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3016, Integer.Sparse.eval_collectBalanced, rawRowCheck3016]

theorem rawRowCheck3017 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form14 = rawRow3017 := by decide +kernel

theorem rowCheck3017 : row3017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3017 := by decide +kernel

theorem rowEval3017 (x : Key → ℝ) : Integer.Sparse.eval row3017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3017, Integer.Sparse.eval_collectBalanced, rawRowCheck3017]

theorem rawRowCheck3018 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form14 = rawRow3018 := by decide +kernel

theorem rowCheck3018 : row3018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3018 := by decide +kernel

theorem rowEval3018 (x : Key → ℝ) : Integer.Sparse.eval row3018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3018, Integer.Sparse.eval_collectBalanced, rawRowCheck3018]

theorem rawRowCheck3019 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form14 = rawRow3019 := by decide +kernel

theorem rowCheck3019 : row3019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3019 := by decide +kernel

theorem rowEval3019 (x : Key → ℝ) : Integer.Sparse.eval row3019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3019, Integer.Sparse.eval_collectBalanced, rawRowCheck3019]

theorem rawRowCheck3020 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form14 = rawRow3020 := by decide +kernel

theorem rowCheck3020 : row3020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3020 := by decide +kernel

theorem rowEval3020 (x : Key → ℝ) : Integer.Sparse.eval row3020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3020, Integer.Sparse.eval_collectBalanced, rawRowCheck3020]

theorem rawRowCheck3021 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form14 = rawRow3021 := by decide +kernel

theorem rowCheck3021 : row3021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3021 := by decide +kernel

theorem rowEval3021 (x : Key → ℝ) : Integer.Sparse.eval row3021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3021, Integer.Sparse.eval_collectBalanced, rawRowCheck3021]

theorem rawRowCheck3022 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form14 = rawRow3022 := by decide +kernel

theorem rowCheck3022 : row3022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3022 := by decide +kernel

theorem rowEval3022 (x : Key → ℝ) : Integer.Sparse.eval row3022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3022, Integer.Sparse.eval_collectBalanced, rawRowCheck3022]

theorem rawRowCheck3023 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3023 := by decide +kernel

theorem rowCheck3023 : row3023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3023 := by decide +kernel

theorem rowEval3023 (x : Key → ℝ) : Integer.Sparse.eval row3023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3023, Integer.Sparse.eval_collectBalanced, rawRowCheck3023]

theorem rawRowCheck3024 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3024 := by decide +kernel

theorem rowCheck3024 : row3024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3024 := by decide +kernel

theorem rowEval3024 (x : Key → ℝ) : Integer.Sparse.eval row3024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3024, Integer.Sparse.eval_collectBalanced, rawRowCheck3024]

theorem rawRowCheck3025 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3025 := by decide +kernel

theorem rowCheck3025 : row3025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3025 := by decide +kernel

theorem rowEval3025 (x : Key → ℝ) : Integer.Sparse.eval row3025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3025, Integer.Sparse.eval_collectBalanced, rawRowCheck3025]

theorem rawRowCheck3026 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form14 = rawRow3026 := by decide +kernel

theorem rowCheck3026 : row3026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3026 := by decide +kernel

theorem rowEval3026 (x : Key → ℝ) : Integer.Sparse.eval row3026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3026, Integer.Sparse.eval_collectBalanced, rawRowCheck3026]

theorem rawRowCheck3027 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form14 = rawRow3027 := by decide +kernel

theorem rowCheck3027 : row3027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3027 := by decide +kernel

theorem rowEval3027 (x : Key → ℝ) : Integer.Sparse.eval row3027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3027, Integer.Sparse.eval_collectBalanced, rawRowCheck3027]

theorem rawRowCheck3028 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form14 = rawRow3028 := by decide +kernel

theorem rowCheck3028 : row3028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3028 := by decide +kernel

theorem rowEval3028 (x : Key → ℝ) : Integer.Sparse.eval row3028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3028, Integer.Sparse.eval_collectBalanced, rawRowCheck3028]

theorem rawRowCheck3029 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form14 = rawRow3029 := by decide +kernel

theorem rowCheck3029 : row3029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3029 := by decide +kernel

theorem rowEval3029 (x : Key → ℝ) : Integer.Sparse.eval row3029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3029, Integer.Sparse.eval_collectBalanced, rawRowCheck3029]

theorem rawRowCheck3030 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form14 = rawRow3030 := by decide +kernel

theorem rowCheck3030 : row3030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3030 := by decide +kernel

theorem rowEval3030 (x : Key → ℝ) : Integer.Sparse.eval row3030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3030, Integer.Sparse.eval_collectBalanced, rawRowCheck3030]

theorem rawRowCheck3031 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form14 = rawRow3031 := by decide +kernel

theorem rowCheck3031 : row3031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3031 := by decide +kernel

theorem rowEval3031 (x : Key → ℝ) : Integer.Sparse.eval row3031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block1.form14) x := by
  rw [rowCheck3031, Integer.Sparse.eval_collectBalanced, rawRowCheck3031]

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

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval2984 x
  · exact rowEval2985 x
  · exact rowEval2986 x
  · exact rowEval2987 x
  · exact rowEval2988 x
  · exact rowEval2989 x
  · exact rowEval2990 x
  · exact rowEval2991 x
  · exact rowEval2992 x
  · exact rowEval2993 x
  · exact rowEval2994 x
  · exact rowEval2995 x
  · exact rowEval2996 x
  · exact rowEval2997 x
  · exact rowEval2998 x
  · exact rowEval2999 x
  · exact rowEval3000 x
  · exact rowEval3001 x
  · exact rowEval3002 x
  · exact rowEval3003 x
  · exact rowEval3004 x
  · exact rowEval3005 x
  · exact rowEval3006 x
  · exact rowEval3007 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

theorem entryCheck14_14 : entry14_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_14 k)) := by decide +kernel

theorem rowsSound14_14 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval3008 x
  · exact rowEval3009 x
  · exact rowEval3010 x
  · exact rowEval3011 x
  · exact rowEval3012 x
  · exact rowEval3013 x
  · exact rowEval3014 x
  · exact rowEval3015 x
  · exact rowEval3016 x
  · exact rowEval3017 x
  · exact rowEval3018 x
  · exact rowEval3019 x
  · exact rowEval3020 x
  · exact rowEval3021 x
  · exact rowEval3022 x
  · exact rowEval3023 x
  · exact rowEval3024 x
  · exact rowEval3025 x
  · exact rowEval3026 x
  · exact rowEval3027 x
  · exact rowEval3028 x
  · exact rowEval3029 x
  · exact rowEval3030 x
  · exact rowEval3031 x

theorem entryEval14_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_14 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck14_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_14]

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

theorem rawRowCheck4752 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4752 := by decide +kernel

theorem rowCheck4752 : row4752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4752 := by decide +kernel

theorem rowEval4752 (x : Key → ℝ) : Integer.Sparse.eval row4752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4752, Integer.Sparse.eval_collectBalanced, rawRowCheck4752]

theorem rawRowCheck4753 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4753 := by decide +kernel

theorem rowCheck4753 : row4753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4753 := by decide +kernel

theorem rowEval4753 (x : Key → ℝ) : Integer.Sparse.eval row4753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4753, Integer.Sparse.eval_collectBalanced, rawRowCheck4753]

theorem rawRowCheck4754 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4754 := by decide +kernel

theorem rowCheck4754 : row4754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4754 := by decide +kernel

theorem rowEval4754 (x : Key → ℝ) : Integer.Sparse.eval row4754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4754, Integer.Sparse.eval_collectBalanced, rawRowCheck4754]

theorem rawRowCheck4755 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4755 := by decide +kernel

theorem rowCheck4755 : row4755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4755 := by decide +kernel

theorem rowEval4755 (x : Key → ℝ) : Integer.Sparse.eval row4755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4755, Integer.Sparse.eval_collectBalanced, rawRowCheck4755]

theorem rawRowCheck4756 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4756 := by decide +kernel

theorem rowCheck4756 : row4756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4756 := by decide +kernel

theorem rowEval4756 (x : Key → ℝ) : Integer.Sparse.eval row4756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4756, Integer.Sparse.eval_collectBalanced, rawRowCheck4756]

theorem rawRowCheck4757 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4757 := by decide +kernel

theorem rowCheck4757 : row4757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4757 := by decide +kernel

theorem rowEval4757 (x : Key → ℝ) : Integer.Sparse.eval row4757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4757, Integer.Sparse.eval_collectBalanced, rawRowCheck4757]

theorem rawRowCheck4758 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4758 := by decide +kernel

theorem rowCheck4758 : row4758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4758 := by decide +kernel

theorem rowEval4758 (x : Key → ℝ) : Integer.Sparse.eval row4758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4758, Integer.Sparse.eval_collectBalanced, rawRowCheck4758]

theorem rawRowCheck4759 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4759 := by decide +kernel

theorem rowCheck4759 : row4759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4759 := by decide +kernel

theorem rowEval4759 (x : Key → ℝ) : Integer.Sparse.eval row4759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4759, Integer.Sparse.eval_collectBalanced, rawRowCheck4759]

theorem rawRowCheck4760 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4760 := by decide +kernel

theorem rowCheck4760 : row4760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4760 := by decide +kernel

theorem rowEval4760 (x : Key → ℝ) : Integer.Sparse.eval row4760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4760, Integer.Sparse.eval_collectBalanced, rawRowCheck4760]

theorem rawRowCheck4761 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4761 := by decide +kernel

theorem rowCheck4761 : row4761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4761 := by decide +kernel

theorem rowEval4761 (x : Key → ℝ) : Integer.Sparse.eval row4761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4761, Integer.Sparse.eval_collectBalanced, rawRowCheck4761]

theorem rawRowCheck4762 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4762 := by decide +kernel

theorem rowCheck4762 : row4762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4762 := by decide +kernel

theorem rowEval4762 (x : Key → ℝ) : Integer.Sparse.eval row4762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4762, Integer.Sparse.eval_collectBalanced, rawRowCheck4762]

theorem rawRowCheck4763 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4763 := by decide +kernel

theorem rowCheck4763 : row4763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4763 := by decide +kernel

theorem rowEval4763 (x : Key → ℝ) : Integer.Sparse.eval row4763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4763, Integer.Sparse.eval_collectBalanced, rawRowCheck4763]

theorem rawRowCheck4764 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4764 := by decide +kernel

theorem rowCheck4764 : row4764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4764 := by decide +kernel

theorem rowEval4764 (x : Key → ℝ) : Integer.Sparse.eval row4764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4764, Integer.Sparse.eval_collectBalanced, rawRowCheck4764]

theorem rawRowCheck4765 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4765 := by decide +kernel

theorem rowCheck4765 : row4765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4765 := by decide +kernel

theorem rowEval4765 (x : Key → ℝ) : Integer.Sparse.eval row4765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4765, Integer.Sparse.eval_collectBalanced, rawRowCheck4765]

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

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval4752 x
  · exact rowEval4753 x
  · exact rowEval4754 x
  · exact rowEval4755 x
  · exact rowEval4756 x
  · exact rowEval4757 x
  · exact rowEval4758 x
  · exact rowEval4759 x
  · exact rowEval4760 x
  · exact rowEval4761 x
  · exact rowEval4762 x
  · exact rowEval4763 x
  · exact rowEval4764 x
  · exact rowEval4765 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

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

theorem rawRowCheck5022 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5022 := by decide +kernel

theorem rowCheck5022 : row5022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5022 := by decide +kernel

theorem rowEval5022 (x : Key → ℝ) : Integer.Sparse.eval row5022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5022, Integer.Sparse.eval_collectBalanced, rawRowCheck5022]

theorem rawRowCheck5023 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5023 := by decide +kernel

theorem rowCheck5023 : row5023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5023 := by decide +kernel

theorem rowEval5023 (x : Key → ℝ) : Integer.Sparse.eval row5023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5023, Integer.Sparse.eval_collectBalanced, rawRowCheck5023]

theorem rawRowCheck5024 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5024 := by decide +kernel

theorem rowCheck5024 : row5024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5024 := by decide +kernel

theorem rowEval5024 (x : Key → ℝ) : Integer.Sparse.eval row5024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5024, Integer.Sparse.eval_collectBalanced, rawRowCheck5024]

theorem rawRowCheck5025 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5025 := by decide +kernel

theorem rowCheck5025 : row5025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5025 := by decide +kernel

theorem rowEval5025 (x : Key → ℝ) : Integer.Sparse.eval row5025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5025, Integer.Sparse.eval_collectBalanced, rawRowCheck5025]

theorem rawRowCheck5026 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5026 := by decide +kernel

theorem rowCheck5026 : row5026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5026 := by decide +kernel

theorem rowEval5026 (x : Key → ℝ) : Integer.Sparse.eval row5026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5026, Integer.Sparse.eval_collectBalanced, rawRowCheck5026]

theorem rawRowCheck5027 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5027 := by decide +kernel

theorem rowCheck5027 : row5027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5027 := by decide +kernel

theorem rowEval5027 (x : Key → ℝ) : Integer.Sparse.eval row5027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5027, Integer.Sparse.eval_collectBalanced, rawRowCheck5027]

theorem rawRowCheck5028 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5028 := by decide +kernel

theorem rowCheck5028 : row5028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5028 := by decide +kernel

theorem rowEval5028 (x : Key → ℝ) : Integer.Sparse.eval row5028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5028, Integer.Sparse.eval_collectBalanced, rawRowCheck5028]

theorem rawRowCheck5029 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5029 := by decide +kernel

theorem rowCheck5029 : row5029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5029 := by decide +kernel

theorem rowEval5029 (x : Key → ℝ) : Integer.Sparse.eval row5029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5029, Integer.Sparse.eval_collectBalanced, rawRowCheck5029]

theorem rawRowCheck5030 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5030 := by decide +kernel

theorem rowCheck5030 : row5030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5030 := by decide +kernel

theorem rowEval5030 (x : Key → ℝ) : Integer.Sparse.eval row5030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5030, Integer.Sparse.eval_collectBalanced, rawRowCheck5030]

theorem rawRowCheck5031 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5031 := by decide +kernel

theorem rowCheck5031 : row5031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5031 := by decide +kernel

theorem rowEval5031 (x : Key → ℝ) : Integer.Sparse.eval row5031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5031, Integer.Sparse.eval_collectBalanced, rawRowCheck5031]

theorem rawRowCheck5032 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5032 := by decide +kernel

theorem rowCheck5032 : row5032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5032 := by decide +kernel

theorem rowEval5032 (x : Key → ℝ) : Integer.Sparse.eval row5032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5032, Integer.Sparse.eval_collectBalanced, rawRowCheck5032]

theorem rawRowCheck5033 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5033 := by decide +kernel

theorem rowCheck5033 : row5033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5033 := by decide +kernel

theorem rowEval5033 (x : Key → ℝ) : Integer.Sparse.eval row5033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5033, Integer.Sparse.eval_collectBalanced, rawRowCheck5033]

theorem rawRowCheck5034 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5034 := by decide +kernel

theorem rowCheck5034 : row5034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5034 := by decide +kernel

theorem rowEval5034 (x : Key → ℝ) : Integer.Sparse.eval row5034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5034, Integer.Sparse.eval_collectBalanced, rawRowCheck5034]

theorem rawRowCheck5035 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5035 := by decide +kernel

theorem rowCheck5035 : row5035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5035 := by decide +kernel

theorem rowEval5035 (x : Key → ℝ) : Integer.Sparse.eval row5035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5035, Integer.Sparse.eval_collectBalanced, rawRowCheck5035]

theorem rawRowCheck5036 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5036 := by decide +kernel

theorem rowCheck5036 : row5036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5036 := by decide +kernel

theorem rowEval5036 (x : Key → ℝ) : Integer.Sparse.eval row5036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5036, Integer.Sparse.eval_collectBalanced, rawRowCheck5036]

theorem rawRowCheck5037 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5037 := by decide +kernel

theorem rowCheck5037 : row5037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5037 := by decide +kernel

theorem rowEval5037 (x : Key → ℝ) : Integer.Sparse.eval row5037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5037, Integer.Sparse.eval_collectBalanced, rawRowCheck5037]

theorem rawRowCheck5038 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5038 := by decide +kernel

theorem rowCheck5038 : row5038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5038 := by decide +kernel

theorem rowEval5038 (x : Key → ℝ) : Integer.Sparse.eval row5038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5038, Integer.Sparse.eval_collectBalanced, rawRowCheck5038]

theorem rawRowCheck5039 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5039 := by decide +kernel

theorem rowCheck5039 : row5039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5039 := by decide +kernel

theorem rowEval5039 (x : Key → ℝ) : Integer.Sparse.eval row5039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5039, Integer.Sparse.eval_collectBalanced, rawRowCheck5039]

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

theorem entryCheck20_14 : entry20_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_14 k)) := by decide +kernel

theorem rowsSound20_14 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval5022 x
  · exact rowEval5023 x
  · exact rowEval5024 x
  · exact rowEval5025 x
  · exact rowEval5026 x
  · exact rowEval5027 x
  · exact rowEval5028 x
  · exact rowEval5029 x
  · exact rowEval5030 x
  · exact rowEval5031 x
  · exact rowEval5032 x
  · exact rowEval5033 x
  · exact rowEval5034 x
  · exact rowEval5035 x
  · exact rowEval5036 x
  · exact rowEval5037 x
  · exact rowEval5038 x
  · exact rowEval5039 x

theorem entryEval20_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_14 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck20_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_14]

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

theorem entryEvalRow14_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 14 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 14).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval14_0_e B hB
  · exact entryEval14_1 B hB
  · exact entryEval14_2_e B hB
  · exact entryEval14_3 B hB
  · exact entryEval14_4 B hB
  · exact entryEval14_5_e B hB
  · exact entryEval14_6 B hB
  · exact entryEval14_7_e B hB
  · exact entryEval14_8 B hB
  · exact entryEval14_9_e B hB
  · exact entryEval14_10 B hB
  · exact entryEval14_11 B hB
  · exact entryEval14_12_e B hB
  · exact entryEval14_13 B hB
  · exact entryEval14_14 B hB
  · exact (entryEval15_14_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_14_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_14_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_14 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e_oai
