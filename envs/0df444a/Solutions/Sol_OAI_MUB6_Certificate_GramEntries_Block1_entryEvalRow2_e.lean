-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:35:25.503287+00:00
-- url     : https://prove2.me/submissions/e0271272-228f-41c1-9c3f-57f172d37719

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval19_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval2_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_2_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck688 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0 = rawRow688 := by decide +kernel

theorem rowCheck688 : row688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow688 := by decide +kernel

theorem rowEval688 (x : Key → ℝ) : Integer.Sparse.eval row688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck688, Integer.Sparse.eval_collectBalanced, rawRowCheck688]

theorem rawRowCheck689 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0 = rawRow689 := by decide +kernel

theorem rowCheck689 : row689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow689 := by decide +kernel

theorem rowEval689 (x : Key → ℝ) : Integer.Sparse.eval row689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck689, Integer.Sparse.eval_collectBalanced, rawRowCheck689]

theorem rawRowCheck690 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0 = rawRow690 := by decide +kernel

theorem rowCheck690 : row690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow690 := by decide +kernel

theorem rowEval690 (x : Key → ℝ) : Integer.Sparse.eval row690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck690, Integer.Sparse.eval_collectBalanced, rawRowCheck690]

theorem rawRowCheck691 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0 = rawRow691 := by decide +kernel

theorem rowCheck691 : row691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow691 := by decide +kernel

theorem rowEval691 (x : Key → ℝ) : Integer.Sparse.eval row691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck691, Integer.Sparse.eval_collectBalanced, rawRowCheck691]

theorem rawRowCheck692 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0 = rawRow692 := by decide +kernel

theorem rowCheck692 : row692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow692 := by decide +kernel

theorem rowEval692 (x : Key → ℝ) : Integer.Sparse.eval row692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck692, Integer.Sparse.eval_collectBalanced, rawRowCheck692]

theorem rawRowCheck693 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0 = rawRow693 := by decide +kernel

theorem rowCheck693 : row693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow693 := by decide +kernel

theorem rowEval693 (x : Key → ℝ) : Integer.Sparse.eval row693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck693, Integer.Sparse.eval_collectBalanced, rawRowCheck693]

theorem rawRowCheck694 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0 = rawRow694 := by decide +kernel

theorem rowCheck694 : row694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow694 := by decide +kernel

theorem rowEval694 (x : Key → ℝ) : Integer.Sparse.eval row694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck694, Integer.Sparse.eval_collectBalanced, rawRowCheck694]

theorem rawRowCheck695 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0 = rawRow695 := by decide +kernel

theorem rowCheck695 : row695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow695 := by decide +kernel

theorem rowEval695 (x : Key → ℝ) : Integer.Sparse.eval row695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck695, Integer.Sparse.eval_collectBalanced, rawRowCheck695]

theorem rawRowCheck696 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0 = rawRow696 := by decide +kernel

theorem rowCheck696 : row696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow696 := by decide +kernel

theorem rowEval696 (x : Key → ℝ) : Integer.Sparse.eval row696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck696, Integer.Sparse.eval_collectBalanced, rawRowCheck696]

theorem rawRowCheck697 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0 = rawRow697 := by decide +kernel

theorem rowCheck697 : row697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow697 := by decide +kernel

theorem rowEval697 (x : Key → ℝ) : Integer.Sparse.eval row697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck697, Integer.Sparse.eval_collectBalanced, rawRowCheck697]

theorem rawRowCheck698 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0 = rawRow698 := by decide +kernel

theorem rowCheck698 : row698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow698 := by decide +kernel

theorem rowEval698 (x : Key → ℝ) : Integer.Sparse.eval row698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck698, Integer.Sparse.eval_collectBalanced, rawRowCheck698]

theorem rawRowCheck699 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0 = rawRow699 := by decide +kernel

theorem rowCheck699 : row699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow699 := by decide +kernel

theorem rowEval699 (x : Key → ℝ) : Integer.Sparse.eval row699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck699, Integer.Sparse.eval_collectBalanced, rawRowCheck699]

theorem rawRowCheck700 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0 = rawRow700 := by decide +kernel

theorem rowCheck700 : row700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow700 := by decide +kernel

theorem rowEval700 (x : Key → ℝ) : Integer.Sparse.eval row700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck700, Integer.Sparse.eval_collectBalanced, rawRowCheck700]

theorem rawRowCheck701 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0 = rawRow701 := by decide +kernel

theorem rowCheck701 : row701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow701 := by decide +kernel

theorem rowEval701 (x : Key → ℝ) : Integer.Sparse.eval row701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck701, Integer.Sparse.eval_collectBalanced, rawRowCheck701]

theorem rawRowCheck702 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0 = rawRow702 := by decide +kernel

theorem rowCheck702 : row702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow702 := by decide +kernel

theorem rowEval702 (x : Key → ℝ) : Integer.Sparse.eval row702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck702, Integer.Sparse.eval_collectBalanced, rawRowCheck702]

theorem rawRowCheck703 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0 = rawRow703 := by decide +kernel

theorem rowCheck703 : row703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow703 := by decide +kernel

theorem rowEval703 (x : Key → ℝ) : Integer.Sparse.eval row703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck703, Integer.Sparse.eval_collectBalanced, rawRowCheck703]

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

theorem rawRowCheck2504 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form2 = rawRow2504 := by decide +kernel

theorem rowCheck2504 : row2504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2504 := by decide +kernel

theorem rowEval2504 (x : Key → ℝ) : Integer.Sparse.eval row2504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2504, Integer.Sparse.eval_collectBalanced, rawRowCheck2504]

theorem rawRowCheck2505 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form2 = rawRow2505 := by decide +kernel

theorem rowCheck2505 : row2505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2505 := by decide +kernel

theorem rowEval2505 (x : Key → ℝ) : Integer.Sparse.eval row2505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2505, Integer.Sparse.eval_collectBalanced, rawRowCheck2505]

theorem rawRowCheck2506 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form2 = rawRow2506 := by decide +kernel

theorem rowCheck2506 : row2506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2506 := by decide +kernel

theorem rowEval2506 (x : Key → ℝ) : Integer.Sparse.eval row2506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2506, Integer.Sparse.eval_collectBalanced, rawRowCheck2506]

theorem rawRowCheck2507 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow2507 := by decide +kernel

theorem rowCheck2507 : row2507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2507 := by decide +kernel

theorem rowEval2507 (x : Key → ℝ) : Integer.Sparse.eval row2507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2507, Integer.Sparse.eval_collectBalanced, rawRowCheck2507]

theorem rawRowCheck2508 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form2 = rawRow2508 := by decide +kernel

theorem rowCheck2508 : row2508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2508 := by decide +kernel

theorem rowEval2508 (x : Key → ℝ) : Integer.Sparse.eval row2508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2508, Integer.Sparse.eval_collectBalanced, rawRowCheck2508]

theorem rawRowCheck2509 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form2 = rawRow2509 := by decide +kernel

theorem rowCheck2509 : row2509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2509 := by decide +kernel

theorem rowEval2509 (x : Key → ℝ) : Integer.Sparse.eval row2509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2509, Integer.Sparse.eval_collectBalanced, rawRowCheck2509]

theorem rawRowCheck2510 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form2 = rawRow2510 := by decide +kernel

theorem rowCheck2510 : row2510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2510 := by decide +kernel

theorem rowEval2510 (x : Key → ℝ) : Integer.Sparse.eval row2510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2510, Integer.Sparse.eval_collectBalanced, rawRowCheck2510]

theorem rawRowCheck2511 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow2511 := by decide +kernel

theorem rowCheck2511 : row2511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2511 := by decide +kernel

theorem rowEval2511 (x : Key → ℝ) : Integer.Sparse.eval row2511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2511, Integer.Sparse.eval_collectBalanced, rawRowCheck2511]

theorem rawRowCheck2512 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow2512 := by decide +kernel

theorem rowCheck2512 : row2512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2512 := by decide +kernel

theorem rowEval2512 (x : Key → ℝ) : Integer.Sparse.eval row2512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2512, Integer.Sparse.eval_collectBalanced, rawRowCheck2512]

theorem rawRowCheck2513 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow2513 := by decide +kernel

theorem rowCheck2513 : row2513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2513 := by decide +kernel

theorem rowEval2513 (x : Key → ℝ) : Integer.Sparse.eval row2513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2513, Integer.Sparse.eval_collectBalanced, rawRowCheck2513]

theorem rawRowCheck2514 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow2514 := by decide +kernel

theorem rowCheck2514 : row2514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2514 := by decide +kernel

theorem rowEval2514 (x : Key → ℝ) : Integer.Sparse.eval row2514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2514, Integer.Sparse.eval_collectBalanced, rawRowCheck2514]

theorem rawRowCheck2515 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form2 = rawRow2515 := by decide +kernel

theorem rowCheck2515 : row2515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2515 := by decide +kernel

theorem rowEval2515 (x : Key → ℝ) : Integer.Sparse.eval row2515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2515, Integer.Sparse.eval_collectBalanced, rawRowCheck2515]

theorem rawRowCheck2516 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form2 = rawRow2516 := by decide +kernel

theorem rowCheck2516 : row2516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2516 := by decide +kernel

theorem rowEval2516 (x : Key → ℝ) : Integer.Sparse.eval row2516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2516, Integer.Sparse.eval_collectBalanced, rawRowCheck2516]

theorem rawRowCheck2517 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form2 = rawRow2517 := by decide +kernel

theorem rowCheck2517 : row2517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2517 := by decide +kernel

theorem rowEval2517 (x : Key → ℝ) : Integer.Sparse.eval row2517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2517, Integer.Sparse.eval_collectBalanced, rawRowCheck2517]

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

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2504 x
  · exact rowEval2505 x
  · exact rowEval2506 x
  · exact rowEval2507 x
  · exact rowEval2508 x
  · exact rowEval2509 x
  · exact rowEval2510 x
  · exact rowEval2511 x
  · exact rowEval2512 x
  · exact rowEval2513 x
  · exact rowEval2514 x
  · exact rowEval2515 x
  · exact rowEval2516 x
  · exact rowEval2517 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck704 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0 = rawRow704 := by decide +kernel

theorem rowCheck704 : row704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow704 := by decide +kernel

theorem rowEval704 (x : Key → ℝ) : Integer.Sparse.eval row704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck704, Integer.Sparse.eval_collectBalanced, rawRowCheck704]

theorem rawRowCheck705 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0 = rawRow705 := by decide +kernel

theorem rowCheck705 : row705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow705 := by decide +kernel

theorem rowEval705 (x : Key → ℝ) : Integer.Sparse.eval row705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck705, Integer.Sparse.eval_collectBalanced, rawRowCheck705]

theorem rawRowCheck706 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0 = rawRow706 := by decide +kernel

theorem rowCheck706 : row706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow706 := by decide +kernel

theorem rowEval706 (x : Key → ℝ) : Integer.Sparse.eval row706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck706, Integer.Sparse.eval_collectBalanced, rawRowCheck706]

theorem rawRowCheck707 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0 = rawRow707 := by decide +kernel

theorem rowCheck707 : row707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow707 := by decide +kernel

theorem rowEval707 (x : Key → ℝ) : Integer.Sparse.eval row707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck707, Integer.Sparse.eval_collectBalanced, rawRowCheck707]

theorem rawRowCheck708 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0 = rawRow708 := by decide +kernel

theorem rowCheck708 : row708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow708 := by decide +kernel

theorem rowEval708 (x : Key → ℝ) : Integer.Sparse.eval row708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck708, Integer.Sparse.eval_collectBalanced, rawRowCheck708]

theorem rawRowCheck709 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0 = rawRow709 := by decide +kernel

theorem rowCheck709 : row709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow709 := by decide +kernel

theorem rowEval709 (x : Key → ℝ) : Integer.Sparse.eval row709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck709, Integer.Sparse.eval_collectBalanced, rawRowCheck709]

theorem rawRowCheck710 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0 = rawRow710 := by decide +kernel

theorem rowCheck710 : row710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow710 := by decide +kernel

theorem rowEval710 (x : Key → ℝ) : Integer.Sparse.eval row710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck710, Integer.Sparse.eval_collectBalanced, rawRowCheck710]

theorem rawRowCheck711 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0 = rawRow711 := by decide +kernel

theorem rowCheck711 : row711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow711 := by decide +kernel

theorem rowEval711 (x : Key → ℝ) : Integer.Sparse.eval row711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck711, Integer.Sparse.eval_collectBalanced, rawRowCheck711]

theorem rawRowCheck712 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0 = rawRow712 := by decide +kernel

theorem rowCheck712 : row712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow712 := by decide +kernel

theorem rowEval712 (x : Key → ℝ) : Integer.Sparse.eval row712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck712, Integer.Sparse.eval_collectBalanced, rawRowCheck712]

theorem rawRowCheck713 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0 = rawRow713 := by decide +kernel

theorem rowCheck713 : row713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow713 := by decide +kernel

theorem rowEval713 (x : Key → ℝ) : Integer.Sparse.eval row713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck713, Integer.Sparse.eval_collectBalanced, rawRowCheck713]

theorem rawRowCheck714 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0 = rawRow714 := by decide +kernel

theorem rowCheck714 : row714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow714 := by decide +kernel

theorem rowEval714 (x : Key → ℝ) : Integer.Sparse.eval row714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck714, Integer.Sparse.eval_collectBalanced, rawRowCheck714]

theorem rawRowCheck715 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0 = rawRow715 := by decide +kernel

theorem rowCheck715 : row715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow715 := by decide +kernel

theorem rowEval715 (x : Key → ℝ) : Integer.Sparse.eval row715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck715, Integer.Sparse.eval_collectBalanced, rawRowCheck715]

theorem rawRowCheck716 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0 = rawRow716 := by decide +kernel

theorem rowCheck716 : row716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow716 := by decide +kernel

theorem rowEval716 (x : Key → ℝ) : Integer.Sparse.eval row716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck716, Integer.Sparse.eval_collectBalanced, rawRowCheck716]

theorem rawRowCheck717 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0 = rawRow717 := by decide +kernel

theorem rowCheck717 : row717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow717 := by decide +kernel

theorem rowEval717 (x : Key → ℝ) : Integer.Sparse.eval row717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck717, Integer.Sparse.eval_collectBalanced, rawRowCheck717]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck748 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2 = rawRow748 := by decide +kernel

theorem rowCheck748 : row748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow748 := by decide +kernel

theorem rowEval748 (x : Key → ℝ) : Integer.Sparse.eval row748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck748, Integer.Sparse.eval_collectBalanced, rawRowCheck748]

theorem rawRowCheck749 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2 = rawRow749 := by decide +kernel

theorem rowCheck749 : row749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow749 := by decide +kernel

theorem rowEval749 (x : Key → ℝ) : Integer.Sparse.eval row749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck749, Integer.Sparse.eval_collectBalanced, rawRowCheck749]

theorem rawRowCheck750 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2 = rawRow750 := by decide +kernel

theorem rowCheck750 : row750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow750 := by decide +kernel

theorem rowEval750 (x : Key → ℝ) : Integer.Sparse.eval row750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck750, Integer.Sparse.eval_collectBalanced, rawRowCheck750]

theorem rawRowCheck751 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2 = rawRow751 := by decide +kernel

theorem rowCheck751 : row751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow751 := by decide +kernel

theorem rowEval751 (x : Key → ℝ) : Integer.Sparse.eval row751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck751, Integer.Sparse.eval_collectBalanced, rawRowCheck751]

theorem rawRowCheck752 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2 = rawRow752 := by decide +kernel

theorem rowCheck752 : row752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow752 := by decide +kernel

theorem rowEval752 (x : Key → ℝ) : Integer.Sparse.eval row752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck752, Integer.Sparse.eval_collectBalanced, rawRowCheck752]

theorem rawRowCheck753 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2 = rawRow753 := by decide +kernel

theorem rowCheck753 : row753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow753 := by decide +kernel

theorem rowEval753 (x : Key → ℝ) : Integer.Sparse.eval row753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck753, Integer.Sparse.eval_collectBalanced, rawRowCheck753]

theorem rawRowCheck754 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2 = rawRow754 := by decide +kernel

theorem rowCheck754 : row754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow754 := by decide +kernel

theorem rowEval754 (x : Key → ℝ) : Integer.Sparse.eval row754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck754, Integer.Sparse.eval_collectBalanced, rawRowCheck754]

theorem rawRowCheck755 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2 = rawRow755 := by decide +kernel

theorem rowCheck755 : row755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow755 := by decide +kernel

theorem rowEval755 (x : Key → ℝ) : Integer.Sparse.eval row755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck755, Integer.Sparse.eval_collectBalanced, rawRowCheck755]

theorem rawRowCheck756 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2 = rawRow756 := by decide +kernel

theorem rowCheck756 : row756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow756 := by decide +kernel

theorem rowEval756 (x : Key → ℝ) : Integer.Sparse.eval row756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck756, Integer.Sparse.eval_collectBalanced, rawRowCheck756]

theorem rawRowCheck757 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2 = rawRow757 := by decide +kernel

theorem rowCheck757 : row757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow757 := by decide +kernel

theorem rowEval757 (x : Key → ℝ) : Integer.Sparse.eval row757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck757, Integer.Sparse.eval_collectBalanced, rawRowCheck757]

theorem rawRowCheck758 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2 = rawRow758 := by decide +kernel

theorem rowCheck758 : row758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow758 := by decide +kernel

theorem rowEval758 (x : Key → ℝ) : Integer.Sparse.eval row758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck758, Integer.Sparse.eval_collectBalanced, rawRowCheck758]

theorem rawRowCheck759 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2 = rawRow759 := by decide +kernel

theorem rowCheck759 : row759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow759 := by decide +kernel

theorem rowEval759 (x : Key → ℝ) : Integer.Sparse.eval row759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck759, Integer.Sparse.eval_collectBalanced, rawRowCheck759]

theorem rawRowCheck760 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2 = rawRow760 := by decide +kernel

theorem rowCheck760 : row760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow760 := by decide +kernel

theorem rowEval760 (x : Key → ℝ) : Integer.Sparse.eval row760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck760, Integer.Sparse.eval_collectBalanced, rawRowCheck760]

theorem rawRowCheck761 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2 = rawRow761 := by decide +kernel

theorem rowCheck761 : row761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow761 := by decide +kernel

theorem rowEval761 (x : Key → ℝ) : Integer.Sparse.eval row761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck761, Integer.Sparse.eval_collectBalanced, rawRowCheck761]

theorem rawRowCheck762 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2 = rawRow762 := by decide +kernel

theorem rowCheck762 : row762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow762 := by decide +kernel

theorem rowEval762 (x : Key → ℝ) : Integer.Sparse.eval row762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck762, Integer.Sparse.eval_collectBalanced, rawRowCheck762]

theorem rawRowCheck763 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2 = rawRow763 := by decide +kernel

theorem rowCheck763 : row763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow763 := by decide +kernel

theorem rowEval763 (x : Key → ℝ) : Integer.Sparse.eval row763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck763, Integer.Sparse.eval_collectBalanced, rawRowCheck763]

theorem rawRowCheck764 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2 = rawRow764 := by decide +kernel

theorem rowCheck764 : row764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow764 := by decide +kernel

theorem rowEval764 (x : Key → ℝ) : Integer.Sparse.eval row764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck764, Integer.Sparse.eval_collectBalanced, rawRowCheck764]

theorem rawRowCheck765 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2 = rawRow765 := by decide +kernel

theorem rowCheck765 : row765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow765 := by decide +kernel

theorem rowEval765 (x : Key → ℝ) : Integer.Sparse.eval row765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck765, Integer.Sparse.eval_collectBalanced, rawRowCheck765]

theorem rawRowCheck766 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2 = rawRow766 := by decide +kernel

theorem rowCheck766 : row766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow766 := by decide +kernel

theorem rowEval766 (x : Key → ℝ) : Integer.Sparse.eval row766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck766, Integer.Sparse.eval_collectBalanced, rawRowCheck766]

theorem rawRowCheck767 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2 = rawRow767 := by decide +kernel

theorem rowCheck767 : row767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow767 := by decide +kernel

theorem rowEval767 (x : Key → ℝ) : Integer.Sparse.eval row767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck767, Integer.Sparse.eval_collectBalanced, rawRowCheck767]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck768 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2 = rawRow768 := by decide +kernel

theorem rowCheck768 : row768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow768 := by decide +kernel

theorem rowEval768 (x : Key → ℝ) : Integer.Sparse.eval row768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck768, Integer.Sparse.eval_collectBalanced, rawRowCheck768]

theorem rawRowCheck769 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2 = rawRow769 := by decide +kernel

theorem rowCheck769 : row769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow769 := by decide +kernel

theorem rowEval769 (x : Key → ℝ) : Integer.Sparse.eval row769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck769, Integer.Sparse.eval_collectBalanced, rawRowCheck769]

theorem rawRowCheck770 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2 = rawRow770 := by decide +kernel

theorem rowCheck770 : row770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow770 := by decide +kernel

theorem rowEval770 (x : Key → ℝ) : Integer.Sparse.eval row770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck770, Integer.Sparse.eval_collectBalanced, rawRowCheck770]

theorem rawRowCheck771 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2 = rawRow771 := by decide +kernel

theorem rowCheck771 : row771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow771 := by decide +kernel

theorem rowEval771 (x : Key → ℝ) : Integer.Sparse.eval row771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck771, Integer.Sparse.eval_collectBalanced, rawRowCheck771]

theorem rawRowCheck772 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2 = rawRow772 := by decide +kernel

theorem rowCheck772 : row772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow772 := by decide +kernel

theorem rowEval772 (x : Key → ℝ) : Integer.Sparse.eval row772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck772, Integer.Sparse.eval_collectBalanced, rawRowCheck772]

theorem rawRowCheck773 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2 = rawRow773 := by decide +kernel

theorem rowCheck773 : row773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow773 := by decide +kernel

theorem rowEval773 (x : Key → ℝ) : Integer.Sparse.eval row773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck773, Integer.Sparse.eval_collectBalanced, rawRowCheck773]

theorem rawRowCheck774 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2 = rawRow774 := by decide +kernel

theorem rowCheck774 : row774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow774 := by decide +kernel

theorem rowEval774 (x : Key → ℝ) : Integer.Sparse.eval row774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck774, Integer.Sparse.eval_collectBalanced, rawRowCheck774]

theorem rawRowCheck775 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2 = rawRow775 := by decide +kernel

theorem rowCheck775 : row775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow775 := by decide +kernel

theorem rowEval775 (x : Key → ℝ) : Integer.Sparse.eval row775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck775, Integer.Sparse.eval_collectBalanced, rawRowCheck775]

theorem rawRowCheck776 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2 = rawRow776 := by decide +kernel

theorem rowCheck776 : row776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow776 := by decide +kernel

theorem rowEval776 (x : Key → ℝ) : Integer.Sparse.eval row776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck776, Integer.Sparse.eval_collectBalanced, rawRowCheck776]

theorem rawRowCheck777 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2 = rawRow777 := by decide +kernel

theorem rowCheck777 : row777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow777 := by decide +kernel

theorem rowEval777 (x : Key → ℝ) : Integer.Sparse.eval row777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck777, Integer.Sparse.eval_collectBalanced, rawRowCheck777]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck3764 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2 = rawRow3764 := by decide +kernel

theorem rowCheck3764 : row3764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3764 := by decide +kernel

theorem rowEval3764 (x : Key → ℝ) : Integer.Sparse.eval row3764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3764, Integer.Sparse.eval_collectBalanced, rawRowCheck3764]

theorem rawRowCheck3765 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2 = rawRow3765 := by decide +kernel

theorem rowCheck3765 : row3765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3765 := by decide +kernel

theorem rowEval3765 (x : Key → ℝ) : Integer.Sparse.eval row3765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3765, Integer.Sparse.eval_collectBalanced, rawRowCheck3765]

theorem rawRowCheck3766 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2 = rawRow3766 := by decide +kernel

theorem rowCheck3766 : row3766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3766 := by decide +kernel

theorem rowEval3766 (x : Key → ℝ) : Integer.Sparse.eval row3766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3766, Integer.Sparse.eval_collectBalanced, rawRowCheck3766]

theorem rawRowCheck3767 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2 = rawRow3767 := by decide +kernel

theorem rowCheck3767 : row3767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3767 := by decide +kernel

theorem rowEval3767 (x : Key → ℝ) : Integer.Sparse.eval row3767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3767, Integer.Sparse.eval_collectBalanced, rawRowCheck3767]

theorem rawRowCheck3768 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2 = rawRow3768 := by decide +kernel

theorem rowCheck3768 : row3768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3768 := by decide +kernel

theorem rowEval3768 (x : Key → ℝ) : Integer.Sparse.eval row3768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3768, Integer.Sparse.eval_collectBalanced, rawRowCheck3768]

theorem rawRowCheck3769 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2 = rawRow3769 := by decide +kernel

theorem rowCheck3769 : row3769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3769 := by decide +kernel

theorem rowEval3769 (x : Key → ℝ) : Integer.Sparse.eval row3769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3769, Integer.Sparse.eval_collectBalanced, rawRowCheck3769]

theorem rawRowCheck3770 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3770 := by decide +kernel

theorem rowCheck3770 : row3770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3770 := by decide +kernel

theorem rowEval3770 (x : Key → ℝ) : Integer.Sparse.eval row3770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3770, Integer.Sparse.eval_collectBalanced, rawRowCheck3770]

theorem rawRowCheck3771 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3771 := by decide +kernel

theorem rowCheck3771 : row3771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3771 := by decide +kernel

theorem rowEval3771 (x : Key → ℝ) : Integer.Sparse.eval row3771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3771, Integer.Sparse.eval_collectBalanced, rawRowCheck3771]

theorem rawRowCheck3772 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3772 := by decide +kernel

theorem rowCheck3772 : row3772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3772 := by decide +kernel

theorem rowEval3772 (x : Key → ℝ) : Integer.Sparse.eval row3772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3772, Integer.Sparse.eval_collectBalanced, rawRowCheck3772]

theorem rawRowCheck3773 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2 = rawRow3773 := by decide +kernel

theorem rowCheck3773 : row3773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3773 := by decide +kernel

theorem rowEval3773 (x : Key → ℝ) : Integer.Sparse.eval row3773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3773, Integer.Sparse.eval_collectBalanced, rawRowCheck3773]

theorem rawRowCheck3774 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2 = rawRow3774 := by decide +kernel

theorem rowCheck3774 : row3774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3774 := by decide +kernel

theorem rowEval3774 (x : Key → ℝ) : Integer.Sparse.eval row3774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3774, Integer.Sparse.eval_collectBalanced, rawRowCheck3774]

theorem rawRowCheck3775 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2 = rawRow3775 := by decide +kernel

theorem rowCheck3775 : row3775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3775 := by decide +kernel

theorem rowEval3775 (x : Key → ℝ) : Integer.Sparse.eval row3775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3775, Integer.Sparse.eval_collectBalanced, rawRowCheck3775]

theorem rawRowCheck3776 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2 = rawRow3776 := by decide +kernel

theorem rowCheck3776 : row3776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3776 := by decide +kernel

theorem rowEval3776 (x : Key → ℝ) : Integer.Sparse.eval row3776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3776, Integer.Sparse.eval_collectBalanced, rawRowCheck3776]

theorem rawRowCheck3777 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2 = rawRow3777 := by decide +kernel

theorem rowCheck3777 : row3777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3777 := by decide +kernel

theorem rowEval3777 (x : Key → ℝ) : Integer.Sparse.eval row3777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3777, Integer.Sparse.eval_collectBalanced, rawRowCheck3777]

theorem rawRowCheck3778 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2 = rawRow3778 := by decide +kernel

theorem rowCheck3778 : row3778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3778 := by decide +kernel

theorem rowEval3778 (x : Key → ℝ) : Integer.Sparse.eval row3778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3778, Integer.Sparse.eval_collectBalanced, rawRowCheck3778]

theorem rawRowCheck3779 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3779 := by decide +kernel

theorem rowCheck3779 : row3779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3779 := by decide +kernel

theorem rowEval3779 (x : Key → ℝ) : Integer.Sparse.eval row3779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3779, Integer.Sparse.eval_collectBalanced, rawRowCheck3779]

theorem rawRowCheck3780 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3780 := by decide +kernel

theorem rowCheck3780 : row3780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3780 := by decide +kernel

theorem rowEval3780 (x : Key → ℝ) : Integer.Sparse.eval row3780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3780, Integer.Sparse.eval_collectBalanced, rawRowCheck3780]

theorem rawRowCheck3781 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3781 := by decide +kernel

theorem rowCheck3781 : row3781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3781 := by decide +kernel

theorem rowEval3781 (x : Key → ℝ) : Integer.Sparse.eval row3781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3781, Integer.Sparse.eval_collectBalanced, rawRowCheck3781]

theorem rawRowCheck3782 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3782 := by decide +kernel

theorem rowCheck3782 : row3782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3782 := by decide +kernel

theorem rowEval3782 (x : Key → ℝ) : Integer.Sparse.eval row3782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3782, Integer.Sparse.eval_collectBalanced, rawRowCheck3782]

theorem rawRowCheck3783 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3783 := by decide +kernel

theorem rowCheck3783 : row3783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3783 := by decide +kernel

theorem rowEval3783 (x : Key → ℝ) : Integer.Sparse.eval row3783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3783, Integer.Sparse.eval_collectBalanced, rawRowCheck3783]

theorem rawRowCheck3784 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3784 := by decide +kernel

theorem rowCheck3784 : row3784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3784 := by decide +kernel

theorem rowEval3784 (x : Key → ℝ) : Integer.Sparse.eval row3784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3784, Integer.Sparse.eval_collectBalanced, rawRowCheck3784]

theorem rawRowCheck3785 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow3785 := by decide +kernel

theorem rowCheck3785 : row3785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3785 := by decide +kernel

theorem rowEval3785 (x : Key → ℝ) : Integer.Sparse.eval row3785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3785, Integer.Sparse.eval_collectBalanced, rawRowCheck3785]

theorem rawRowCheck3786 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow3786 := by decide +kernel

theorem rowCheck3786 : row3786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3786 := by decide +kernel

theorem rowEval3786 (x : Key → ℝ) : Integer.Sparse.eval row3786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3786, Integer.Sparse.eval_collectBalanced, rawRowCheck3786]

theorem rawRowCheck3787 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow3787 := by decide +kernel

theorem rowCheck3787 : row3787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3787 := by decide +kernel

theorem rowEval3787 (x : Key → ℝ) : Integer.Sparse.eval row3787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3787, Integer.Sparse.eval_collectBalanced, rawRowCheck3787]

theorem rawRowCheck3788 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2 = rawRow3788 := by decide +kernel

theorem rowCheck3788 : row3788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3788 := by decide +kernel

theorem rowEval3788 (x : Key → ℝ) : Integer.Sparse.eval row3788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3788, Integer.Sparse.eval_collectBalanced, rawRowCheck3788]

theorem rawRowCheck3789 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2 = rawRow3789 := by decide +kernel

theorem rowCheck3789 : row3789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3789 := by decide +kernel

theorem rowEval3789 (x : Key → ℝ) : Integer.Sparse.eval row3789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3789, Integer.Sparse.eval_collectBalanced, rawRowCheck3789]

theorem rawRowCheck3790 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2 = rawRow3790 := by decide +kernel

theorem rowCheck3790 : row3790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3790 := by decide +kernel

theorem rowEval3790 (x : Key → ℝ) : Integer.Sparse.eval row3790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck3790, Integer.Sparse.eval_collectBalanced, rawRowCheck3790]

theorem rawRowCheck3791 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2 = rawRow3791 := by decide +kernel

theorem rowCheck3791 : row3791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3791 := by decide +kernel

theorem rowEval3791 (x : Key → ℝ) : Integer.Sparse.eval row3791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3791, Integer.Sparse.eval_collectBalanced, rawRowCheck3791]

theorem rawRowCheck3792 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2 = rawRow3792 := by decide +kernel

theorem rowCheck3792 : row3792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3792 := by decide +kernel

theorem rowEval3792 (x : Key → ℝ) : Integer.Sparse.eval row3792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck3792, Integer.Sparse.eval_collectBalanced, rawRowCheck3792]

theorem rawRowCheck3793 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2 = rawRow3793 := by decide +kernel

theorem rowCheck3793 : row3793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3793 := by decide +kernel

theorem rowEval3793 (x : Key → ℝ) : Integer.Sparse.eval row3793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck3793, Integer.Sparse.eval_collectBalanced, rawRowCheck3793]

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

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval3764 x
  · exact rowEval3765 x
  · exact rowEval3766 x
  · exact rowEval3767 x
  · exact rowEval3768 x
  · exact rowEval3769 x
  · exact rowEval3770 x
  · exact rowEval3771 x
  · exact rowEval3772 x
  · exact rowEval3773 x
  · exact rowEval3774 x
  · exact rowEval3775 x
  · exact rowEval3776 x
  · exact rowEval3777 x
  · exact rowEval3778 x
  · exact rowEval3779 x
  · exact rowEval3780 x
  · exact rowEval3781 x
  · exact rowEval3782 x
  · exact rowEval3783 x
  · exact rowEval3784 x
  · exact rowEval3785 x
  · exact rowEval3786 x
  · exact rowEval3787 x
  · exact rowEval3788 x
  · exact rowEval3789 x
  · exact rowEval3790 x
  · exact rowEval3791 x
  · exact rowEval3792 x
  · exact rowEval3793 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block1.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form2.terms k).tag (GramFunctions.Block1.form2.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval688 x
  · exact rowEval689 x
  · exact rowEval690 x
  · exact rowEval691 x
  · exact rowEval692 x
  · exact rowEval693 x
  · exact rowEval694 x
  · exact rowEval695 x
  · exact rowEval696 x
  · exact rowEval697 x
  · exact rowEval698 x
  · exact rowEval699 x
  · exact rowEval700 x
  · exact rowEval701 x
  · exact rowEval702 x
  · exact rowEval703 x
  · exact rowEval704 x
  · exact rowEval705 x
  · exact rowEval706 x
  · exact rowEval707 x
  · exact rowEval708 x
  · exact rowEval709 x
  · exact rowEval710 x
  · exact rowEval711 x
  · exact rowEval712 x
  · exact rowEval713 x
  · exact rowEval714 x
  · exact rowEval715 x
  · exact rowEval716 x
  · exact rowEval717 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block1.form2.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form2 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block1.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form2.terms k).tag (GramFunctions.Block1.form2.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval748 x
  · exact rowEval749 x
  · exact rowEval750 x
  · exact rowEval751 x
  · exact rowEval752 x
  · exact rowEval753 x
  · exact rowEval754 x
  · exact rowEval755 x
  · exact rowEval756 x
  · exact rowEval757 x
  · exact rowEval758 x
  · exact rowEval759 x
  · exact rowEval760 x
  · exact rowEval761 x
  · exact rowEval762 x
  · exact rowEval763 x
  · exact rowEval764 x
  · exact rowEval765 x
  · exact rowEval766 x
  · exact rowEval767 x
  · exact rowEval768 x
  · exact rowEval769 x
  · exact rowEval770 x
  · exact rowEval771 x
  · exact rowEval772 x
  · exact rowEval773 x
  · exact rowEval774 x
  · exact rowEval775 x
  · exact rowEval776 x
  · exact rowEval777 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block1.form2.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form2 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

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

theorem rawRowCheck862 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow862 := by decide +kernel

theorem rowCheck862 : row862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow862 := by decide +kernel

theorem rowEval862 (x : Key → ℝ) : Integer.Sparse.eval row862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck862, Integer.Sparse.eval_collectBalanced, rawRowCheck862]

theorem rawRowCheck863 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2 = rawRow863 := by decide +kernel

theorem rowCheck863 : row863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow863 := by decide +kernel

theorem rowEval863 (x : Key → ℝ) : Integer.Sparse.eval row863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck863, Integer.Sparse.eval_collectBalanced, rawRowCheck863]

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

theorem rawRowCheck864 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2 = rawRow864 := by decide +kernel

theorem rowCheck864 : row864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow864 := by decide +kernel

theorem rowEval864 (x : Key → ℝ) : Integer.Sparse.eval row864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck864, Integer.Sparse.eval_collectBalanced, rawRowCheck864]

theorem rawRowCheck865 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2 = rawRow865 := by decide +kernel

theorem rowCheck865 : row865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow865 := by decide +kernel

theorem rowEval865 (x : Key → ℝ) : Integer.Sparse.eval row865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck865, Integer.Sparse.eval_collectBalanced, rawRowCheck865]

theorem rawRowCheck866 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow866 := by decide +kernel

theorem rowCheck866 : row866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow866 := by decide +kernel

theorem rowEval866 (x : Key → ℝ) : Integer.Sparse.eval row866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck866, Integer.Sparse.eval_collectBalanced, rawRowCheck866]

theorem rawRowCheck867 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2 = rawRow867 := by decide +kernel

theorem rowCheck867 : row867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow867 := by decide +kernel

theorem rowEval867 (x : Key → ℝ) : Integer.Sparse.eval row867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck867, Integer.Sparse.eval_collectBalanced, rawRowCheck867]

theorem rawRowCheck868 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2 = rawRow868 := by decide +kernel

theorem rowCheck868 : row868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow868 := by decide +kernel

theorem rowEval868 (x : Key → ℝ) : Integer.Sparse.eval row868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck868, Integer.Sparse.eval_collectBalanced, rawRowCheck868]

theorem rawRowCheck869 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2 = rawRow869 := by decide +kernel

theorem rowCheck869 : row869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow869 := by decide +kernel

theorem rowEval869 (x : Key → ℝ) : Integer.Sparse.eval row869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck869, Integer.Sparse.eval_collectBalanced, rawRowCheck869]

theorem rawRowCheck870 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2 = rawRow870 := by decide +kernel

theorem rowCheck870 : row870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow870 := by decide +kernel

theorem rowEval870 (x : Key → ℝ) : Integer.Sparse.eval row870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck870, Integer.Sparse.eval_collectBalanced, rawRowCheck870]

theorem rawRowCheck871 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2 = rawRow871 := by decide +kernel

theorem rowCheck871 : row871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow871 := by decide +kernel

theorem rowEval871 (x : Key → ℝ) : Integer.Sparse.eval row871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck871, Integer.Sparse.eval_collectBalanced, rawRowCheck871]

theorem rawRowCheck872 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2 = rawRow872 := by decide +kernel

theorem rowCheck872 : row872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow872 := by decide +kernel

theorem rowEval872 (x : Key → ℝ) : Integer.Sparse.eval row872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck872, Integer.Sparse.eval_collectBalanced, rawRowCheck872]

theorem rawRowCheck873 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow873 := by decide +kernel

theorem rowCheck873 : row873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow873 := by decide +kernel

theorem rowEval873 (x : Key → ℝ) : Integer.Sparse.eval row873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck873, Integer.Sparse.eval_collectBalanced, rawRowCheck873]

theorem rawRowCheck874 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow874 := by decide +kernel

theorem rowCheck874 : row874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow874 := by decide +kernel

theorem rowEval874 (x : Key → ℝ) : Integer.Sparse.eval row874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck874, Integer.Sparse.eval_collectBalanced, rawRowCheck874]

theorem rawRowCheck875 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow875 := by decide +kernel

theorem rowCheck875 : row875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow875 := by decide +kernel

theorem rowEval875 (x : Key → ℝ) : Integer.Sparse.eval row875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck875, Integer.Sparse.eval_collectBalanced, rawRowCheck875]

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

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval862 x
  · exact rowEval863 x
  · exact rowEval864 x
  · exact rowEval865 x
  · exact rowEval866 x
  · exact rowEval867 x
  · exact rowEval868 x
  · exact rowEval869 x
  · exact rowEval870 x
  · exact rowEval871 x
  · exact rowEval872 x
  · exact rowEval873 x
  · exact rowEval874 x
  · exact rowEval875 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

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

theorem entryEvalRow2_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 2).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1_e B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e_oai
