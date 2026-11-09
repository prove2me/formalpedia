-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:24:49.014106+00:00
-- url     : https://prove2.me/submissions/f02b1139-d0cd-4aa9-9088-4bbde6d59a6d

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_12_e

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

theorem rawRowCheck2239 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form5 = rawRow2239 := by decide +kernel

theorem rowCheck2239 : row2239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2239 := by decide +kernel

theorem rowEval2239 (x : Key → ℝ) : Integer.Sparse.eval row2239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2239, Integer.Sparse.eval_collectBalanced, rawRowCheck2239]

theorem rawRowCheck2240 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form5 = rawRow2240 := by decide +kernel

theorem rowCheck2240 : row2240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2240 := by decide +kernel

theorem rowEval2240 (x : Key → ℝ) : Integer.Sparse.eval row2240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2240, Integer.Sparse.eval_collectBalanced, rawRowCheck2240]

theorem rawRowCheck2241 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form5 = rawRow2241 := by decide +kernel

theorem rowCheck2241 : row2241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2241 := by decide +kernel

theorem rowEval2241 (x : Key → ℝ) : Integer.Sparse.eval row2241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2241, Integer.Sparse.eval_collectBalanced, rawRowCheck2241]

theorem rawRowCheck2242 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form5 = rawRow2242 := by decide +kernel

theorem rowCheck2242 : row2242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2242 := by decide +kernel

theorem rowEval2242 (x : Key → ℝ) : Integer.Sparse.eval row2242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2242, Integer.Sparse.eval_collectBalanced, rawRowCheck2242]

theorem rawRowCheck2243 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form5 = rawRow2243 := by decide +kernel

theorem rowCheck2243 : row2243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2243 := by decide +kernel

theorem rowEval2243 (x : Key → ℝ) : Integer.Sparse.eval row2243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2243, Integer.Sparse.eval_collectBalanced, rawRowCheck2243]

theorem rawRowCheck2244 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form5 = rawRow2244 := by decide +kernel

theorem rowCheck2244 : row2244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2244 := by decide +kernel

theorem rowEval2244 (x : Key → ℝ) : Integer.Sparse.eval row2244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2244, Integer.Sparse.eval_collectBalanced, rawRowCheck2244]

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

theorem rawRowCheck2248 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5 = rawRow2248 := by decide +kernel

theorem rowCheck2248 : row2248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2248 := by decide +kernel

theorem rowEval2248 (x : Key → ℝ) : Integer.Sparse.eval row2248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2248, Integer.Sparse.eval_collectBalanced, rawRowCheck2248]

theorem rawRowCheck2249 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5 = rawRow2249 := by decide +kernel

theorem rowCheck2249 : row2249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2249 := by decide +kernel

theorem rowEval2249 (x : Key → ℝ) : Integer.Sparse.eval row2249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2249, Integer.Sparse.eval_collectBalanced, rawRowCheck2249]

theorem rawRowCheck2250 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5 = rawRow2250 := by decide +kernel

theorem rowCheck2250 : row2250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2250 := by decide +kernel

theorem rowEval2250 (x : Key → ℝ) : Integer.Sparse.eval row2250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2250, Integer.Sparse.eval_collectBalanced, rawRowCheck2250]

theorem rawRowCheck2251 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5 = rawRow2251 := by decide +kernel

theorem rowCheck2251 : row2251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2251 := by decide +kernel

theorem rowEval2251 (x : Key → ℝ) : Integer.Sparse.eval row2251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2251, Integer.Sparse.eval_collectBalanced, rawRowCheck2251]

theorem rawRowCheck2252 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5 = rawRow2252 := by decide +kernel

theorem rowCheck2252 : row2252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2252 := by decide +kernel

theorem rowEval2252 (x : Key → ℝ) : Integer.Sparse.eval row2252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2252, Integer.Sparse.eval_collectBalanced, rawRowCheck2252]

theorem rawRowCheck2253 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5 = rawRow2253 := by decide +kernel

theorem rowCheck2253 : row2253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2253 := by decide +kernel

theorem rowEval2253 (x : Key → ℝ) : Integer.Sparse.eval row2253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2253, Integer.Sparse.eval_collectBalanced, rawRowCheck2253]

theorem rawRowCheck2254 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form5 = rawRow2254 := by decide +kernel

theorem rowCheck2254 : row2254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2254 := by decide +kernel

theorem rowEval2254 (x : Key → ℝ) : Integer.Sparse.eval row2254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2254, Integer.Sparse.eval_collectBalanced, rawRowCheck2254]

theorem rawRowCheck2255 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form5 = rawRow2255 := by decide +kernel

theorem rowCheck2255 : row2255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2255 := by decide +kernel

theorem rowEval2255 (x : Key → ℝ) : Integer.Sparse.eval row2255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2255, Integer.Sparse.eval_collectBalanced, rawRowCheck2255]

theorem rawRowCheck2256 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form5 = rawRow2256 := by decide +kernel

theorem rowCheck2256 : row2256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2256 := by decide +kernel

theorem rowEval2256 (x : Key → ℝ) : Integer.Sparse.eval row2256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2256, Integer.Sparse.eval_collectBalanced, rawRowCheck2256]

theorem rawRowCheck2257 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form5 = rawRow2257 := by decide +kernel

theorem rowCheck2257 : row2257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2257 := by decide +kernel

theorem rowEval2257 (x : Key → ℝ) : Integer.Sparse.eval row2257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2257, Integer.Sparse.eval_collectBalanced, rawRowCheck2257]

theorem rawRowCheck2258 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form5 = rawRow2258 := by decide +kernel

theorem rowCheck2258 : row2258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2258 := by decide +kernel

theorem rowEval2258 (x : Key → ℝ) : Integer.Sparse.eval row2258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2258, Integer.Sparse.eval_collectBalanced, rawRowCheck2258]

theorem rawRowCheck2259 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form5 = rawRow2259 := by decide +kernel

theorem rowCheck2259 : row2259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2259 := by decide +kernel

theorem rowEval2259 (x : Key → ℝ) : Integer.Sparse.eval row2259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2259, Integer.Sparse.eval_collectBalanced, rawRowCheck2259]

theorem rawRowCheck2260 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5 = rawRow2260 := by decide +kernel

theorem rowCheck2260 : row2260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2260 := by decide +kernel

theorem rowEval2260 (x : Key → ℝ) : Integer.Sparse.eval row2260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2260, Integer.Sparse.eval_collectBalanced, rawRowCheck2260]

theorem rawRowCheck2261 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5 = rawRow2261 := by decide +kernel

theorem rowCheck2261 : row2261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2261 := by decide +kernel

theorem rowEval2261 (x : Key → ℝ) : Integer.Sparse.eval row2261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2261, Integer.Sparse.eval_collectBalanced, rawRowCheck2261]

theorem rawRowCheck2262 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5 = rawRow2262 := by decide +kernel

theorem rowCheck2262 : row2262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2262 := by decide +kernel

theorem rowEval2262 (x : Key → ℝ) : Integer.Sparse.eval row2262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2262, Integer.Sparse.eval_collectBalanced, rawRowCheck2262]

theorem rawRowCheck2263 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5 = rawRow2263 := by decide +kernel

theorem rowCheck2263 : row2263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2263 := by decide +kernel

theorem rowEval2263 (x : Key → ℝ) : Integer.Sparse.eval row2263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2263, Integer.Sparse.eval_collectBalanced, rawRowCheck2263]

theorem rawRowCheck2264 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5 = rawRow2264 := by decide +kernel

theorem rowCheck2264 : row2264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2264 := by decide +kernel

theorem rowEval2264 (x : Key → ℝ) : Integer.Sparse.eval row2264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2264, Integer.Sparse.eval_collectBalanced, rawRowCheck2264]

theorem rawRowCheck2265 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5 = rawRow2265 := by decide +kernel

theorem rowCheck2265 : row2265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2265 := by decide +kernel

theorem rowEval2265 (x : Key → ℝ) : Integer.Sparse.eval row2265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2265, Integer.Sparse.eval_collectBalanced, rawRowCheck2265]

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

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2236 x
  · exact rowEval2237 x
  · exact rowEval2238 x
  · exact rowEval2239 x
  · exact rowEval2240 x
  · exact rowEval2241 x
  · exact rowEval2242 x
  · exact rowEval2243 x
  · exact rowEval2244 x
  · exact rowEval2245 x
  · exact rowEval2246 x
  · exact rowEval2247 x
  · exact rowEval2248 x
  · exact rowEval2249 x
  · exact rowEval2250 x
  · exact rowEval2251 x
  · exact rowEval2252 x
  · exact rowEval2253 x
  · exact rowEval2254 x
  · exact rowEval2255 x
  · exact rowEval2256 x
  · exact rowEval2257 x
  · exact rowEval2258 x
  · exact rowEval2259 x
  · exact rowEval2260 x
  · exact rowEval2261 x
  · exact rowEval2262 x
  · exact rowEval2263 x
  · exact rowEval2264 x
  · exact rowEval2265 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

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

theorem rawRowCheck2644 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form12 = rawRow2644 := by decide +kernel

theorem rowCheck2644 : row2644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2644 := by decide +kernel

theorem rowEval2644 (x : Key → ℝ) : Integer.Sparse.eval row2644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2644, Integer.Sparse.eval_collectBalanced, rawRowCheck2644]

theorem rawRowCheck2645 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form12 = rawRow2645 := by decide +kernel

theorem rowCheck2645 : row2645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2645 := by decide +kernel

theorem rowEval2645 (x : Key → ℝ) : Integer.Sparse.eval row2645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2645, Integer.Sparse.eval_collectBalanced, rawRowCheck2645]

theorem rawRowCheck2646 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form12 = rawRow2646 := by decide +kernel

theorem rowCheck2646 : row2646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2646 := by decide +kernel

theorem rowEval2646 (x : Key → ℝ) : Integer.Sparse.eval row2646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2646, Integer.Sparse.eval_collectBalanced, rawRowCheck2646]

theorem rawRowCheck2647 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form12 = rawRow2647 := by decide +kernel

theorem rowCheck2647 : row2647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2647 := by decide +kernel

theorem rowEval2647 (x : Key → ℝ) : Integer.Sparse.eval row2647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2647, Integer.Sparse.eval_collectBalanced, rawRowCheck2647]

theorem rawRowCheck2648 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form12 = rawRow2648 := by decide +kernel

theorem rowCheck2648 : row2648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2648 := by decide +kernel

theorem rowEval2648 (x : Key → ℝ) : Integer.Sparse.eval row2648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form12) x := by
  rw [rowCheck2648, Integer.Sparse.eval_collectBalanced, rawRowCheck2648]

theorem rawRowCheck2649 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form12 = rawRow2649 := by decide +kernel

theorem rowCheck2649 : row2649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2649 := by decide +kernel

theorem rowEval2649 (x : Key → ℝ) : Integer.Sparse.eval row2649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2649, Integer.Sparse.eval_collectBalanced, rawRowCheck2649]

theorem rawRowCheck2650 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form12 = rawRow2650 := by decide +kernel

theorem rowCheck2650 : row2650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2650 := by decide +kernel

theorem rowEval2650 (x : Key → ℝ) : Integer.Sparse.eval row2650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2650, Integer.Sparse.eval_collectBalanced, rawRowCheck2650]

theorem rawRowCheck2651 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form12 = rawRow2651 := by decide +kernel

theorem rowCheck2651 : row2651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2651 := by decide +kernel

theorem rowEval2651 (x : Key → ℝ) : Integer.Sparse.eval row2651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2651, Integer.Sparse.eval_collectBalanced, rawRowCheck2651]

theorem rawRowCheck2652 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form12 = rawRow2652 := by decide +kernel

theorem rowCheck2652 : row2652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2652 := by decide +kernel

theorem rowEval2652 (x : Key → ℝ) : Integer.Sparse.eval row2652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2652, Integer.Sparse.eval_collectBalanced, rawRowCheck2652]

theorem rawRowCheck2653 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form12 = rawRow2653 := by decide +kernel

theorem rowCheck2653 : row2653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2653 := by decide +kernel

theorem rowEval2653 (x : Key → ℝ) : Integer.Sparse.eval row2653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2653, Integer.Sparse.eval_collectBalanced, rawRowCheck2653]

theorem rawRowCheck2654 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form12 = rawRow2654 := by decide +kernel

theorem rowCheck2654 : row2654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2654 := by decide +kernel

theorem rowEval2654 (x : Key → ℝ) : Integer.Sparse.eval row2654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2654, Integer.Sparse.eval_collectBalanced, rawRowCheck2654]

theorem rawRowCheck2655 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form12 = rawRow2655 := by decide +kernel

theorem rowCheck2655 : row2655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2655 := by decide +kernel

theorem rowEval2655 (x : Key → ℝ) : Integer.Sparse.eval row2655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2655, Integer.Sparse.eval_collectBalanced, rawRowCheck2655]

theorem rawRowCheck2656 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form12 = rawRow2656 := by decide +kernel

theorem rowCheck2656 : row2656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2656 := by decide +kernel

theorem rowEval2656 (x : Key → ℝ) : Integer.Sparse.eval row2656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck2656, Integer.Sparse.eval_collectBalanced, rawRowCheck2656]

theorem rawRowCheck2657 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form12 = rawRow2657 := by decide +kernel

theorem rowCheck2657 : row2657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2657 := by decide +kernel

theorem rowEval2657 (x : Key → ℝ) : Integer.Sparse.eval row2657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck2657, Integer.Sparse.eval_collectBalanced, rawRowCheck2657]

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

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2644 x
  · exact rowEval2645 x
  · exact rowEval2646 x
  · exact rowEval2647 x
  · exact rowEval2648 x
  · exact rowEval2649 x
  · exact rowEval2650 x
  · exact rowEval2651 x
  · exact rowEval2652 x
  · exact rowEval2653 x
  · exact rowEval2654 x
  · exact rowEval2655 x
  · exact rowEval2656 x
  · exact rowEval2657 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

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

theorem rawRowCheck4724 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4724 := by decide +kernel

theorem rowCheck4724 : row4724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4724 := by decide +kernel

theorem rowEval4724 (x : Key → ℝ) : Integer.Sparse.eval row4724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4724, Integer.Sparse.eval_collectBalanced, rawRowCheck4724]

theorem rawRowCheck4725 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4725 := by decide +kernel

theorem rowCheck4725 : row4725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4725 := by decide +kernel

theorem rowEval4725 (x : Key → ℝ) : Integer.Sparse.eval row4725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4725, Integer.Sparse.eval_collectBalanced, rawRowCheck4725]

theorem rawRowCheck4726 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4726 := by decide +kernel

theorem rowCheck4726 : row4726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4726 := by decide +kernel

theorem rowEval4726 (x : Key → ℝ) : Integer.Sparse.eval row4726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4726, Integer.Sparse.eval_collectBalanced, rawRowCheck4726]

theorem rawRowCheck4727 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4727 := by decide +kernel

theorem rowCheck4727 : row4727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4727 := by decide +kernel

theorem rowEval4727 (x : Key → ℝ) : Integer.Sparse.eval row4727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4727, Integer.Sparse.eval_collectBalanced, rawRowCheck4727]

theorem rawRowCheck4728 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4728 := by decide +kernel

theorem rowCheck4728 : row4728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4728 := by decide +kernel

theorem rowEval4728 (x : Key → ℝ) : Integer.Sparse.eval row4728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4728, Integer.Sparse.eval_collectBalanced, rawRowCheck4728]

theorem rawRowCheck4729 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4729 := by decide +kernel

theorem rowCheck4729 : row4729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4729 := by decide +kernel

theorem rowEval4729 (x : Key → ℝ) : Integer.Sparse.eval row4729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4729, Integer.Sparse.eval_collectBalanced, rawRowCheck4729]

theorem rawRowCheck4730 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4730 := by decide +kernel

theorem rowCheck4730 : row4730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4730 := by decide +kernel

theorem rowEval4730 (x : Key → ℝ) : Integer.Sparse.eval row4730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4730, Integer.Sparse.eval_collectBalanced, rawRowCheck4730]

theorem rawRowCheck4731 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4731 := by decide +kernel

theorem rowCheck4731 : row4731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4731 := by decide +kernel

theorem rowEval4731 (x : Key → ℝ) : Integer.Sparse.eval row4731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4731, Integer.Sparse.eval_collectBalanced, rawRowCheck4731]

theorem rawRowCheck4732 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4732 := by decide +kernel

theorem rowCheck4732 : row4732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4732 := by decide +kernel

theorem rowEval4732 (x : Key → ℝ) : Integer.Sparse.eval row4732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4732, Integer.Sparse.eval_collectBalanced, rawRowCheck4732]

theorem rawRowCheck4733 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4733 := by decide +kernel

theorem rowCheck4733 : row4733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4733 := by decide +kernel

theorem rowEval4733 (x : Key → ℝ) : Integer.Sparse.eval row4733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4733, Integer.Sparse.eval_collectBalanced, rawRowCheck4733]

theorem rawRowCheck4734 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4734 := by decide +kernel

theorem rowCheck4734 : row4734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4734 := by decide +kernel

theorem rowEval4734 (x : Key → ℝ) : Integer.Sparse.eval row4734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4734, Integer.Sparse.eval_collectBalanced, rawRowCheck4734]

theorem rawRowCheck4735 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4735 := by decide +kernel

theorem rowCheck4735 : row4735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4735 := by decide +kernel

theorem rowEval4735 (x : Key → ℝ) : Integer.Sparse.eval row4735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4735, Integer.Sparse.eval_collectBalanced, rawRowCheck4735]

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

theorem rawRowCheck4736 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4736 := by decide +kernel

theorem rowCheck4736 : row4736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4736 := by decide +kernel

theorem rowEval4736 (x : Key → ℝ) : Integer.Sparse.eval row4736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4736, Integer.Sparse.eval_collectBalanced, rawRowCheck4736]

theorem rawRowCheck4737 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4737 := by decide +kernel

theorem rowCheck4737 : row4737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4737 := by decide +kernel

theorem rowEval4737 (x : Key → ℝ) : Integer.Sparse.eval row4737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4737, Integer.Sparse.eval_collectBalanced, rawRowCheck4737]

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

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4724 x
  · exact rowEval4725 x
  · exact rowEval4726 x
  · exact rowEval4727 x
  · exact rowEval4728 x
  · exact rowEval4729 x
  · exact rowEval4730 x
  · exact rowEval4731 x
  · exact rowEval4732 x
  · exact rowEval4733 x
  · exact rowEval4734 x
  · exact rowEval4735 x
  · exact rowEval4736 x
  · exact rowEval4737 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

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

theorem rawRowCheck4986 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4986 := by decide +kernel

theorem rowCheck4986 : row4986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4986 := by decide +kernel

theorem rowEval4986 (x : Key → ℝ) : Integer.Sparse.eval row4986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4986, Integer.Sparse.eval_collectBalanced, rawRowCheck4986]

theorem rawRowCheck4987 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4987 := by decide +kernel

theorem rowCheck4987 : row4987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4987 := by decide +kernel

theorem rowEval4987 (x : Key → ℝ) : Integer.Sparse.eval row4987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4987, Integer.Sparse.eval_collectBalanced, rawRowCheck4987]

theorem rawRowCheck4988 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4988 := by decide +kernel

theorem rowCheck4988 : row4988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4988 := by decide +kernel

theorem rowEval4988 (x : Key → ℝ) : Integer.Sparse.eval row4988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4988, Integer.Sparse.eval_collectBalanced, rawRowCheck4988]

theorem rawRowCheck4989 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4989 := by decide +kernel

theorem rowCheck4989 : row4989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4989 := by decide +kernel

theorem rowEval4989 (x : Key → ℝ) : Integer.Sparse.eval row4989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4989, Integer.Sparse.eval_collectBalanced, rawRowCheck4989]

theorem rawRowCheck4990 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4990 := by decide +kernel

theorem rowCheck4990 : row4990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4990 := by decide +kernel

theorem rowEval4990 (x : Key → ℝ) : Integer.Sparse.eval row4990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4990, Integer.Sparse.eval_collectBalanced, rawRowCheck4990]

theorem rawRowCheck4991 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12 = rawRow4991 := by decide +kernel

theorem rowCheck4991 : row4991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4991 := by decide +kernel

theorem rowEval4991 (x : Key → ℝ) : Integer.Sparse.eval row4991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4991, Integer.Sparse.eval_collectBalanced, rawRowCheck4991]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck4992 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4992 := by decide +kernel

theorem rowCheck4992 : row4992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4992 := by decide +kernel

theorem rowEval4992 (x : Key → ℝ) : Integer.Sparse.eval row4992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4992, Integer.Sparse.eval_collectBalanced, rawRowCheck4992]

theorem rawRowCheck4993 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4993 := by decide +kernel

theorem rowCheck4993 : row4993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4993 := by decide +kernel

theorem rowEval4993 (x : Key → ℝ) : Integer.Sparse.eval row4993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4993, Integer.Sparse.eval_collectBalanced, rawRowCheck4993]

theorem rawRowCheck4994 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4994 := by decide +kernel

theorem rowCheck4994 : row4994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4994 := by decide +kernel

theorem rowEval4994 (x : Key → ℝ) : Integer.Sparse.eval row4994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4994, Integer.Sparse.eval_collectBalanced, rawRowCheck4994]

theorem rawRowCheck4995 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12 = rawRow4995 := by decide +kernel

theorem rowCheck4995 : row4995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4995 := by decide +kernel

theorem rowEval4995 (x : Key → ℝ) : Integer.Sparse.eval row4995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4995, Integer.Sparse.eval_collectBalanced, rawRowCheck4995]

theorem rawRowCheck4996 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12 = rawRow4996 := by decide +kernel

theorem rowCheck4996 : row4996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4996 := by decide +kernel

theorem rowEval4996 (x : Key → ℝ) : Integer.Sparse.eval row4996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4996, Integer.Sparse.eval_collectBalanced, rawRowCheck4996]

theorem rawRowCheck4997 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12 = rawRow4997 := by decide +kernel

theorem rowCheck4997 : row4997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4997 := by decide +kernel

theorem rowEval4997 (x : Key → ℝ) : Integer.Sparse.eval row4997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4997, Integer.Sparse.eval_collectBalanced, rawRowCheck4997]

theorem rawRowCheck4998 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4998 := by decide +kernel

theorem rowCheck4998 : row4998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4998 := by decide +kernel

theorem rowEval4998 (x : Key → ℝ) : Integer.Sparse.eval row4998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4998, Integer.Sparse.eval_collectBalanced, rawRowCheck4998]

theorem rawRowCheck4999 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4999 := by decide +kernel

theorem rowCheck4999 : row4999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4999 := by decide +kernel

theorem rowEval4999 (x : Key → ℝ) : Integer.Sparse.eval row4999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4999, Integer.Sparse.eval_collectBalanced, rawRowCheck4999]

theorem rawRowCheck5000 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12 = rawRow5000 := by decide +kernel

theorem rowCheck5000 : row5000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5000 := by decide +kernel

theorem rowEval5000 (x : Key → ℝ) : Integer.Sparse.eval row5000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5000, Integer.Sparse.eval_collectBalanced, rawRowCheck5000]

theorem rawRowCheck5001 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12 = rawRow5001 := by decide +kernel

theorem rowCheck5001 : row5001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5001 := by decide +kernel

theorem rowEval5001 (x : Key → ℝ) : Integer.Sparse.eval row5001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5001, Integer.Sparse.eval_collectBalanced, rawRowCheck5001]

theorem rawRowCheck5002 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12 = rawRow5002 := by decide +kernel

theorem rowCheck5002 : row5002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5002 := by decide +kernel

theorem rowEval5002 (x : Key → ℝ) : Integer.Sparse.eval row5002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5002, Integer.Sparse.eval_collectBalanced, rawRowCheck5002]

theorem rawRowCheck5003 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12 = rawRow5003 := by decide +kernel

theorem rowCheck5003 : row5003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5003 := by decide +kernel

theorem rowEval5003 (x : Key → ℝ) : Integer.Sparse.eval row5003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck5003, Integer.Sparse.eval_collectBalanced, rawRowCheck5003]

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

theorem entryCheck20_12 : entry20_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_12 k)) := by decide +kernel

theorem rowsSound20_12 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4986 x
  · exact rowEval4987 x
  · exact rowEval4988 x
  · exact rowEval4989 x
  · exact rowEval4990 x
  · exact rowEval4991 x
  · exact rowEval4992 x
  · exact rowEval4993 x
  · exact rowEval4994 x
  · exact rowEval4995 x
  · exact rowEval4996 x
  · exact rowEval4997 x
  · exact rowEval4998 x
  · exact rowEval4999 x
  · exact rowEval5000 x
  · exact rowEval5001 x
  · exact rowEval5002 x
  · exact rowEval5003 x

theorem entryEval20_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_12 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck20_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_12]

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

theorem entryEvalRow12_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 12 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 12).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval12_0_e B hB
  · exact entryEval12_1_e B hB
  · exact entryEval12_2_e B hB
  · exact entryEval12_3_e B hB
  · exact entryEval12_4 B hB
  · exact entryEval12_5 B hB
  · exact entryEval12_6 B hB
  · exact entryEval12_7_e B hB
  · exact entryEval12_8 B hB
  · exact entryEval12_9_e B hB
  · exact entryEval12_10_e B hB
  · exact entryEval12_11_e B hB
  · exact entryEval12_12_e B hB
  · exact (entryEval13_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_12_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_12 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e_oai
