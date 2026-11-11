-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:46:36.62734+00:00
-- url     : https://prove2.me/submissions/2f26c218-3041-4493-b01c-1049e2235cff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval10_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_5_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

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

theorem rawRowCheck2546 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form5 = rawRow2546 := by decide +kernel

theorem rowCheck2546 : row2546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2546 := by decide +kernel

theorem rowEval2546 (x : Key → ℝ) : Integer.Sparse.eval row2546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2546, Integer.Sparse.eval_collectBalanced, rawRowCheck2546]

theorem rawRowCheck2547 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form5 = rawRow2547 := by decide +kernel

theorem rowCheck2547 : row2547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2547 := by decide +kernel

theorem rowEval2547 (x : Key → ℝ) : Integer.Sparse.eval row2547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2547, Integer.Sparse.eval_collectBalanced, rawRowCheck2547]

theorem rawRowCheck2548 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form5 = rawRow2548 := by decide +kernel

theorem rowCheck2548 : row2548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2548 := by decide +kernel

theorem rowEval2548 (x : Key → ℝ) : Integer.Sparse.eval row2548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2548, Integer.Sparse.eval_collectBalanced, rawRowCheck2548]

theorem rawRowCheck2549 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow2549 := by decide +kernel

theorem rowCheck2549 : row2549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2549 := by decide +kernel

theorem rowEval2549 (x : Key → ℝ) : Integer.Sparse.eval row2549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2549, Integer.Sparse.eval_collectBalanced, rawRowCheck2549]

theorem rawRowCheck2550 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form5 = rawRow2550 := by decide +kernel

theorem rowCheck2550 : row2550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2550 := by decide +kernel

theorem rowEval2550 (x : Key → ℝ) : Integer.Sparse.eval row2550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck2550, Integer.Sparse.eval_collectBalanced, rawRowCheck2550]

theorem rawRowCheck2551 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form5 = rawRow2551 := by decide +kernel

theorem rowCheck2551 : row2551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2551 := by decide +kernel

theorem rowEval2551 (x : Key → ℝ) : Integer.Sparse.eval row2551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2551, Integer.Sparse.eval_collectBalanced, rawRowCheck2551]

theorem rawRowCheck2552 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form5 = rawRow2552 := by decide +kernel

theorem rowCheck2552 : row2552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2552 := by decide +kernel

theorem rowEval2552 (x : Key → ℝ) : Integer.Sparse.eval row2552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2552, Integer.Sparse.eval_collectBalanced, rawRowCheck2552]

theorem rawRowCheck2553 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form5 = rawRow2553 := by decide +kernel

theorem rowCheck2553 : row2553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2553 := by decide +kernel

theorem rowEval2553 (x : Key → ℝ) : Integer.Sparse.eval row2553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2553, Integer.Sparse.eval_collectBalanced, rawRowCheck2553]

theorem rawRowCheck2554 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form5 = rawRow2554 := by decide +kernel

theorem rowCheck2554 : row2554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2554 := by decide +kernel

theorem rowEval2554 (x : Key → ℝ) : Integer.Sparse.eval row2554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2554, Integer.Sparse.eval_collectBalanced, rawRowCheck2554]

theorem rawRowCheck2555 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form5 = rawRow2555 := by decide +kernel

theorem rowCheck2555 : row2555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2555 := by decide +kernel

theorem rowEval2555 (x : Key → ℝ) : Integer.Sparse.eval row2555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2555, Integer.Sparse.eval_collectBalanced, rawRowCheck2555]

theorem rawRowCheck2556 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow2556 := by decide +kernel

theorem rowCheck2556 : row2556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2556 := by decide +kernel

theorem rowEval2556 (x : Key → ℝ) : Integer.Sparse.eval row2556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2556, Integer.Sparse.eval_collectBalanced, rawRowCheck2556]

theorem rawRowCheck2557 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form5 = rawRow2557 := by decide +kernel

theorem rowCheck2557 : row2557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2557 := by decide +kernel

theorem rowEval2557 (x : Key → ℝ) : Integer.Sparse.eval row2557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2557, Integer.Sparse.eval_collectBalanced, rawRowCheck2557]

theorem rawRowCheck2558 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form5 = rawRow2558 := by decide +kernel

theorem rowCheck2558 : row2558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2558 := by decide +kernel

theorem rowEval2558 (x : Key → ℝ) : Integer.Sparse.eval row2558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck2558, Integer.Sparse.eval_collectBalanced, rawRowCheck2558]

theorem rawRowCheck2559 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form5 = rawRow2559 := by decide +kernel

theorem rowCheck2559 : row2559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2559 := by decide +kernel

theorem rowEval2559 (x : Key → ℝ) : Integer.Sparse.eval row2559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck2559, Integer.Sparse.eval_collectBalanced, rawRowCheck2559]

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

theorem entryCheck13_5 : entry13_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_5 k)) := by decide +kernel

theorem rowsSound13_5 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2546 x
  · exact rowEval2547 x
  · exact rowEval2548 x
  · exact rowEval2549 x
  · exact rowEval2550 x
  · exact rowEval2551 x
  · exact rowEval2552 x
  · exact rowEval2553 x
  · exact rowEval2554 x
  · exact rowEval2555 x
  · exact rowEval2556 x
  · exact rowEval2557 x
  · exact rowEval2558 x
  · exact rowEval2559 x

theorem entryEval13_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_5 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck13_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_5]

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

theorem rawRowCheck4626 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4626 := by decide +kernel

theorem rowCheck4626 : row4626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4626 := by decide +kernel

theorem rowEval4626 (x : Key → ℝ) : Integer.Sparse.eval row4626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4626, Integer.Sparse.eval_collectBalanced, rawRowCheck4626]

theorem rawRowCheck4627 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4627 := by decide +kernel

theorem rowCheck4627 : row4627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4627 := by decide +kernel

theorem rowEval4627 (x : Key → ℝ) : Integer.Sparse.eval row4627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4627, Integer.Sparse.eval_collectBalanced, rawRowCheck4627]

theorem rawRowCheck4628 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4628 := by decide +kernel

theorem rowCheck4628 : row4628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4628 := by decide +kernel

theorem rowEval4628 (x : Key → ℝ) : Integer.Sparse.eval row4628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4628, Integer.Sparse.eval_collectBalanced, rawRowCheck4628]

theorem rawRowCheck4629 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4629 := by decide +kernel

theorem rowCheck4629 : row4629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4629 := by decide +kernel

theorem rowEval4629 (x : Key → ℝ) : Integer.Sparse.eval row4629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4629, Integer.Sparse.eval_collectBalanced, rawRowCheck4629]

theorem rawRowCheck4630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4630 := by decide +kernel

theorem rowCheck4630 : row4630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4630 := by decide +kernel

theorem rowEval4630 (x : Key → ℝ) : Integer.Sparse.eval row4630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4630, Integer.Sparse.eval_collectBalanced, rawRowCheck4630]

theorem rawRowCheck4631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4631 := by decide +kernel

theorem rowCheck4631 : row4631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4631 := by decide +kernel

theorem rowEval4631 (x : Key → ℝ) : Integer.Sparse.eval row4631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4631, Integer.Sparse.eval_collectBalanced, rawRowCheck4631]

theorem rawRowCheck4632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4632 := by decide +kernel

theorem rowCheck4632 : row4632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4632 := by decide +kernel

theorem rowEval4632 (x : Key → ℝ) : Integer.Sparse.eval row4632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4632, Integer.Sparse.eval_collectBalanced, rawRowCheck4632]

theorem rawRowCheck4633 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4633 := by decide +kernel

theorem rowCheck4633 : row4633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4633 := by decide +kernel

theorem rowEval4633 (x : Key → ℝ) : Integer.Sparse.eval row4633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4633, Integer.Sparse.eval_collectBalanced, rawRowCheck4633]

theorem rawRowCheck4634 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4634 := by decide +kernel

theorem rowCheck4634 : row4634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4634 := by decide +kernel

theorem rowEval4634 (x : Key → ℝ) : Integer.Sparse.eval row4634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4634, Integer.Sparse.eval_collectBalanced, rawRowCheck4634]

theorem rawRowCheck4635 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4635 := by decide +kernel

theorem rowCheck4635 : row4635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4635 := by decide +kernel

theorem rowEval4635 (x : Key → ℝ) : Integer.Sparse.eval row4635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4635, Integer.Sparse.eval_collectBalanced, rawRowCheck4635]

theorem rawRowCheck4636 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4636 := by decide +kernel

theorem rowCheck4636 : row4636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4636 := by decide +kernel

theorem rowEval4636 (x : Key → ℝ) : Integer.Sparse.eval row4636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4636, Integer.Sparse.eval_collectBalanced, rawRowCheck4636]

theorem rawRowCheck4637 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4637 := by decide +kernel

theorem rowCheck4637 : row4637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4637 := by decide +kernel

theorem rowEval4637 (x : Key → ℝ) : Integer.Sparse.eval row4637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4637, Integer.Sparse.eval_collectBalanced, rawRowCheck4637]

theorem rawRowCheck4638 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4638 := by decide +kernel

theorem rowCheck4638 : row4638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4638 := by decide +kernel

theorem rowEval4638 (x : Key → ℝ) : Integer.Sparse.eval row4638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4638, Integer.Sparse.eval_collectBalanced, rawRowCheck4638]

theorem rawRowCheck4639 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4639 := by decide +kernel

theorem rowCheck4639 : row4639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4639 := by decide +kernel

theorem rowEval4639 (x : Key → ℝ) : Integer.Sparse.eval row4639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4639, Integer.Sparse.eval_collectBalanced, rawRowCheck4639]

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

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval4626 x
  · exact rowEval4627 x
  · exact rowEval4628 x
  · exact rowEval4629 x
  · exact rowEval4630 x
  · exact rowEval4631 x
  · exact rowEval4632 x
  · exact rowEval4633 x
  · exact rowEval4634 x
  · exact rowEval4635 x
  · exact rowEval4636 x
  · exact rowEval4637 x
  · exact rowEval4638 x
  · exact rowEval4639 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

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

theorem entryEvalRow5_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 5).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval5_0_e B hB
  · exact entryEval5_1_e B hB
  · exact entryEval5_2_e B hB
  · exact entryEval5_3_e B hB
  · exact entryEval5_4_e B hB
  · exact entryEval5_5_e B hB
  · exact (entryEval6_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e_oai
