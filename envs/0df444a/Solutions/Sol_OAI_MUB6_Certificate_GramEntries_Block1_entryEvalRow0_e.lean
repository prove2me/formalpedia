-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:23:47.219067+00:00
-- url     : https://prove2.me/submissions/86b75f64-a5d8-4228-a136-a0f502e2252f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval0_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval12_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval14_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval16_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval5_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval7_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval9_0_e

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

theorem rawRowCheck2476 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form0 = rawRow2476 := by decide +kernel

theorem rowCheck2476 : row2476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2476 := by decide +kernel

theorem rowEval2476 (x : Key → ℝ) : Integer.Sparse.eval row2476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2476, Integer.Sparse.eval_collectBalanced, rawRowCheck2476]

theorem rawRowCheck2477 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form0 = rawRow2477 := by decide +kernel

theorem rowCheck2477 : row2477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2477 := by decide +kernel

theorem rowEval2477 (x : Key → ℝ) : Integer.Sparse.eval row2477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2477, Integer.Sparse.eval_collectBalanced, rawRowCheck2477]

theorem rawRowCheck2478 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form0 = rawRow2478 := by decide +kernel

theorem rowCheck2478 : row2478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2478 := by decide +kernel

theorem rowEval2478 (x : Key → ℝ) : Integer.Sparse.eval row2478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2478, Integer.Sparse.eval_collectBalanced, rawRowCheck2478]

theorem rawRowCheck2479 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow2479 := by decide +kernel

theorem rowCheck2479 : row2479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2479 := by decide +kernel

theorem rowEval2479 (x : Key → ℝ) : Integer.Sparse.eval row2479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2479, Integer.Sparse.eval_collectBalanced, rawRowCheck2479]

theorem rawRowCheck2480 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form0 = rawRow2480 := by decide +kernel

theorem rowCheck2480 : row2480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2480 := by decide +kernel

theorem rowEval2480 (x : Key → ℝ) : Integer.Sparse.eval row2480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2480, Integer.Sparse.eval_collectBalanced, rawRowCheck2480]

theorem rawRowCheck2481 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form0 = rawRow2481 := by decide +kernel

theorem rowCheck2481 : row2481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2481 := by decide +kernel

theorem rowEval2481 (x : Key → ℝ) : Integer.Sparse.eval row2481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2481, Integer.Sparse.eval_collectBalanced, rawRowCheck2481]

theorem rawRowCheck2482 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form0 = rawRow2482 := by decide +kernel

theorem rowCheck2482 : row2482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2482 := by decide +kernel

theorem rowEval2482 (x : Key → ℝ) : Integer.Sparse.eval row2482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2482, Integer.Sparse.eval_collectBalanced, rawRowCheck2482]

theorem rawRowCheck2483 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow2483 := by decide +kernel

theorem rowCheck2483 : row2483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2483 := by decide +kernel

theorem rowEval2483 (x : Key → ℝ) : Integer.Sparse.eval row2483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2483, Integer.Sparse.eval_collectBalanced, rawRowCheck2483]

theorem rawRowCheck2484 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow2484 := by decide +kernel

theorem rowCheck2484 : row2484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2484 := by decide +kernel

theorem rowEval2484 (x : Key → ℝ) : Integer.Sparse.eval row2484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2484, Integer.Sparse.eval_collectBalanced, rawRowCheck2484]

theorem rawRowCheck2485 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow2485 := by decide +kernel

theorem rowCheck2485 : row2485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2485 := by decide +kernel

theorem rowEval2485 (x : Key → ℝ) : Integer.Sparse.eval row2485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2485, Integer.Sparse.eval_collectBalanced, rawRowCheck2485]

theorem rawRowCheck2486 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow2486 := by decide +kernel

theorem rowCheck2486 : row2486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2486 := by decide +kernel

theorem rowEval2486 (x : Key → ℝ) : Integer.Sparse.eval row2486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2486, Integer.Sparse.eval_collectBalanced, rawRowCheck2486]

theorem rawRowCheck2487 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow2487 := by decide +kernel

theorem rowCheck2487 : row2487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2487 := by decide +kernel

theorem rowEval2487 (x : Key → ℝ) : Integer.Sparse.eval row2487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2487, Integer.Sparse.eval_collectBalanced, rawRowCheck2487]

theorem rawRowCheck2488 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow2488 := by decide +kernel

theorem rowCheck2488 : row2488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2488 := by decide +kernel

theorem rowEval2488 (x : Key → ℝ) : Integer.Sparse.eval row2488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2488, Integer.Sparse.eval_collectBalanced, rawRowCheck2488]

theorem rawRowCheck2489 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow2489 := by decide +kernel

theorem rowCheck2489 : row2489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2489 := by decide +kernel

theorem rowEval2489 (x : Key → ℝ) : Integer.Sparse.eval row2489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2489, Integer.Sparse.eval_collectBalanced, rawRowCheck2489]

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

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2476 x
  · exact rowEval2477 x
  · exact rowEval2478 x
  · exact rowEval2479 x
  · exact rowEval2480 x
  · exact rowEval2481 x
  · exact rowEval2482 x
  · exact rowEval2483 x
  · exact rowEval2484 x
  · exact rowEval2485 x
  · exact rowEval2486 x
  · exact rowEval2487 x
  · exact rowEval2488 x
  · exact rowEval2489 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

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

end MUB6.Certificate.GramRows

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

theorem rawRowCheck4556 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow4556 := by decide +kernel

theorem rowCheck4556 : row4556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4556 := by decide +kernel

theorem rowEval4556 (x : Key → ℝ) : Integer.Sparse.eval row4556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4556, Integer.Sparse.eval_collectBalanced, rawRowCheck4556]

theorem rawRowCheck4557 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow4557 := by decide +kernel

theorem rowCheck4557 : row4557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4557 := by decide +kernel

theorem rowEval4557 (x : Key → ℝ) : Integer.Sparse.eval row4557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4557, Integer.Sparse.eval_collectBalanced, rawRowCheck4557]

theorem rawRowCheck4558 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow4558 := by decide +kernel

theorem rowCheck4558 : row4558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4558 := by decide +kernel

theorem rowEval4558 (x : Key → ℝ) : Integer.Sparse.eval row4558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4558, Integer.Sparse.eval_collectBalanced, rawRowCheck4558]

theorem rawRowCheck4559 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow4559 := by decide +kernel

theorem rowCheck4559 : row4559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4559 := by decide +kernel

theorem rowEval4559 (x : Key → ℝ) : Integer.Sparse.eval row4559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4559, Integer.Sparse.eval_collectBalanced, rawRowCheck4559]

theorem rawRowCheck4560 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form0 = rawRow4560 := by decide +kernel

theorem rowCheck4560 : row4560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4560 := by decide +kernel

theorem rowEval4560 (x : Key → ℝ) : Integer.Sparse.eval row4560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4560, Integer.Sparse.eval_collectBalanced, rawRowCheck4560]

theorem rawRowCheck4561 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form0 = rawRow4561 := by decide +kernel

theorem rowCheck4561 : row4561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4561 := by decide +kernel

theorem rowEval4561 (x : Key → ℝ) : Integer.Sparse.eval row4561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4561, Integer.Sparse.eval_collectBalanced, rawRowCheck4561]

theorem rawRowCheck4562 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form0 = rawRow4562 := by decide +kernel

theorem rowCheck4562 : row4562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4562 := by decide +kernel

theorem rowEval4562 (x : Key → ℝ) : Integer.Sparse.eval row4562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4562, Integer.Sparse.eval_collectBalanced, rawRowCheck4562]

theorem rawRowCheck4563 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow4563 := by decide +kernel

theorem rowCheck4563 : row4563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4563 := by decide +kernel

theorem rowEval4563 (x : Key → ℝ) : Integer.Sparse.eval row4563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4563, Integer.Sparse.eval_collectBalanced, rawRowCheck4563]

theorem rawRowCheck4564 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow4564 := by decide +kernel

theorem rowCheck4564 : row4564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4564 := by decide +kernel

theorem rowEval4564 (x : Key → ℝ) : Integer.Sparse.eval row4564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4564, Integer.Sparse.eval_collectBalanced, rawRowCheck4564]

theorem rawRowCheck4565 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow4565 := by decide +kernel

theorem rowCheck4565 : row4565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4565 := by decide +kernel

theorem rowEval4565 (x : Key → ℝ) : Integer.Sparse.eval row4565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4565, Integer.Sparse.eval_collectBalanced, rawRowCheck4565]

theorem rawRowCheck4566 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow4566 := by decide +kernel

theorem rowCheck4566 : row4566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4566 := by decide +kernel

theorem rowEval4566 (x : Key → ℝ) : Integer.Sparse.eval row4566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4566, Integer.Sparse.eval_collectBalanced, rawRowCheck4566]

theorem rawRowCheck4567 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow4567 := by decide +kernel

theorem rowCheck4567 : row4567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4567 := by decide +kernel

theorem rowEval4567 (x : Key → ℝ) : Integer.Sparse.eval row4567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4567, Integer.Sparse.eval_collectBalanced, rawRowCheck4567]

theorem rawRowCheck4568 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow4568 := by decide +kernel

theorem rowCheck4568 : row4568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4568 := by decide +kernel

theorem rowEval4568 (x : Key → ℝ) : Integer.Sparse.eval row4568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4568, Integer.Sparse.eval_collectBalanced, rawRowCheck4568]

theorem rawRowCheck4569 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow4569 := by decide +kernel

theorem rowCheck4569 : row4569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4569 := by decide +kernel

theorem rowEval4569 (x : Key → ℝ) : Integer.Sparse.eval row4569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4569, Integer.Sparse.eval_collectBalanced, rawRowCheck4569]

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

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval4556 x
  · exact rowEval4557 x
  · exact rowEval4558 x
  · exact rowEval4559 x
  · exact rowEval4560 x
  · exact rowEval4561 x
  · exact rowEval4562 x
  · exact rowEval4563 x
  · exact rowEval4564 x
  · exact rowEval4565 x
  · exact rowEval4566 x
  · exact rowEval4567 x
  · exact rowEval4568 x
  · exact rowEval4569 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

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

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck834 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow834 := by decide +kernel

theorem rowCheck834 : row834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow834 := by decide +kernel

theorem rowEval834 (x : Key → ℝ) : Integer.Sparse.eval row834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck834, Integer.Sparse.eval_collectBalanced, rawRowCheck834]

theorem rawRowCheck835 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow835 := by decide +kernel

theorem rowCheck835 : row835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow835 := by decide +kernel

theorem rowEval835 (x : Key → ℝ) : Integer.Sparse.eval row835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck835, Integer.Sparse.eval_collectBalanced, rawRowCheck835]

theorem rawRowCheck836 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow836 := by decide +kernel

theorem rowCheck836 : row836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow836 := by decide +kernel

theorem rowEval836 (x : Key → ℝ) : Integer.Sparse.eval row836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck836, Integer.Sparse.eval_collectBalanced, rawRowCheck836]

theorem rawRowCheck837 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow837 := by decide +kernel

theorem rowCheck837 : row837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow837 := by decide +kernel

theorem rowEval837 (x : Key → ℝ) : Integer.Sparse.eval row837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck837, Integer.Sparse.eval_collectBalanced, rawRowCheck837]

theorem rawRowCheck838 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow838 := by decide +kernel

theorem rowCheck838 : row838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow838 := by decide +kernel

theorem rowEval838 (x : Key → ℝ) : Integer.Sparse.eval row838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck838, Integer.Sparse.eval_collectBalanced, rawRowCheck838]

theorem rawRowCheck839 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow839 := by decide +kernel

theorem rowCheck839 : row839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow839 := by decide +kernel

theorem rowEval839 (x : Key → ℝ) : Integer.Sparse.eval row839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck839, Integer.Sparse.eval_collectBalanced, rawRowCheck839]

theorem rawRowCheck840 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow840 := by decide +kernel

theorem rowCheck840 : row840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow840 := by decide +kernel

theorem rowEval840 (x : Key → ℝ) : Integer.Sparse.eval row840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck840, Integer.Sparse.eval_collectBalanced, rawRowCheck840]

theorem rawRowCheck841 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow841 := by decide +kernel

theorem rowCheck841 : row841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow841 := by decide +kernel

theorem rowEval841 (x : Key → ℝ) : Integer.Sparse.eval row841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck841, Integer.Sparse.eval_collectBalanced, rawRowCheck841]

theorem rawRowCheck842 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow842 := by decide +kernel

theorem rowCheck842 : row842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow842 := by decide +kernel

theorem rowEval842 (x : Key → ℝ) : Integer.Sparse.eval row842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck842, Integer.Sparse.eval_collectBalanced, rawRowCheck842]

theorem rawRowCheck843 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow843 := by decide +kernel

theorem rowCheck843 : row843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow843 := by decide +kernel

theorem rowEval843 (x : Key → ℝ) : Integer.Sparse.eval row843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck843, Integer.Sparse.eval_collectBalanced, rawRowCheck843]

theorem rawRowCheck844 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow844 := by decide +kernel

theorem rowCheck844 : row844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow844 := by decide +kernel

theorem rowEval844 (x : Key → ℝ) : Integer.Sparse.eval row844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck844, Integer.Sparse.eval_collectBalanced, rawRowCheck844]

theorem rawRowCheck845 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow845 := by decide +kernel

theorem rowCheck845 : row845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow845 := by decide +kernel

theorem rowEval845 (x : Key → ℝ) : Integer.Sparse.eval row845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck845, Integer.Sparse.eval_collectBalanced, rawRowCheck845]

theorem rawRowCheck846 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow846 := by decide +kernel

theorem rowCheck846 : row846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow846 := by decide +kernel

theorem rowEval846 (x : Key → ℝ) : Integer.Sparse.eval row846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck846, Integer.Sparse.eval_collectBalanced, rawRowCheck846]

theorem rawRowCheck847 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow847 := by decide +kernel

theorem rowCheck847 : row847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow847 := by decide +kernel

theorem rowEval847 (x : Key → ℝ) : Integer.Sparse.eval row847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck847, Integer.Sparse.eval_collectBalanced, rawRowCheck847]

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

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block1.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form4.terms k).tag (GramFunctions.Block1.form4.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval834 x
  · exact rowEval835 x
  · exact rowEval836 x
  · exact rowEval837 x
  · exact rowEval838 x
  · exact rowEval839 x
  · exact rowEval840 x
  · exact rowEval841 x
  · exact rowEval842 x
  · exact rowEval843 x
  · exact rowEval844 x
  · exact rowEval845 x
  · exact rowEval846 x
  · exact rowEval847 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block1.form4.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form4 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck1084 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1084 := by decide +kernel

theorem rowCheck1084 : row1084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1084 := by decide +kernel

theorem rowEval1084 (x : Key → ℝ) : Integer.Sparse.eval row1084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1084, Integer.Sparse.eval_collectBalanced, rawRowCheck1084]

theorem rawRowCheck1085 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1085 := by decide +kernel

theorem rowCheck1085 : row1085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1085 := by decide +kernel

theorem rowEval1085 (x : Key → ℝ) : Integer.Sparse.eval row1085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1085, Integer.Sparse.eval_collectBalanced, rawRowCheck1085]

theorem rawRowCheck1086 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1086 := by decide +kernel

theorem rowCheck1086 : row1086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1086 := by decide +kernel

theorem rowEval1086 (x : Key → ℝ) : Integer.Sparse.eval row1086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1086, Integer.Sparse.eval_collectBalanced, rawRowCheck1086]

theorem rawRowCheck1087 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1087 := by decide +kernel

theorem rowCheck1087 : row1087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1087 := by decide +kernel

theorem rowEval1087 (x : Key → ℝ) : Integer.Sparse.eval row1087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1087, Integer.Sparse.eval_collectBalanced, rawRowCheck1087]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck1088 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1088 := by decide +kernel

theorem rowCheck1088 : row1088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1088 := by decide +kernel

theorem rowEval1088 (x : Key → ℝ) : Integer.Sparse.eval row1088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1088, Integer.Sparse.eval_collectBalanced, rawRowCheck1088]

theorem rawRowCheck1089 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1089 := by decide +kernel

theorem rowCheck1089 : row1089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1089 := by decide +kernel

theorem rowEval1089 (x : Key → ℝ) : Integer.Sparse.eval row1089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1089, Integer.Sparse.eval_collectBalanced, rawRowCheck1089]

theorem rawRowCheck1090 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1090 := by decide +kernel

theorem rowCheck1090 : row1090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1090 := by decide +kernel

theorem rowEval1090 (x : Key → ℝ) : Integer.Sparse.eval row1090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1090, Integer.Sparse.eval_collectBalanced, rawRowCheck1090]

theorem rawRowCheck1091 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1091 := by decide +kernel

theorem rowCheck1091 : row1091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1091 := by decide +kernel

theorem rowEval1091 (x : Key → ℝ) : Integer.Sparse.eval row1091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1091, Integer.Sparse.eval_collectBalanced, rawRowCheck1091]

theorem rawRowCheck1092 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1092 := by decide +kernel

theorem rowCheck1092 : row1092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1092 := by decide +kernel

theorem rowEval1092 (x : Key → ℝ) : Integer.Sparse.eval row1092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1092, Integer.Sparse.eval_collectBalanced, rawRowCheck1092]

theorem rawRowCheck1093 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1093 := by decide +kernel

theorem rowCheck1093 : row1093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1093 := by decide +kernel

theorem rowEval1093 (x : Key → ℝ) : Integer.Sparse.eval row1093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1093, Integer.Sparse.eval_collectBalanced, rawRowCheck1093]

theorem rawRowCheck1094 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1094 := by decide +kernel

theorem rowCheck1094 : row1094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1094 := by decide +kernel

theorem rowEval1094 (x : Key → ℝ) : Integer.Sparse.eval row1094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1094, Integer.Sparse.eval_collectBalanced, rawRowCheck1094]

theorem rawRowCheck1095 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0 = rawRow1095 := by decide +kernel

theorem rowCheck1095 : row1095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1095 := by decide +kernel

theorem rowEval1095 (x : Key → ℝ) : Integer.Sparse.eval row1095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1095, Integer.Sparse.eval_collectBalanced, rawRowCheck1095]

theorem rawRowCheck1096 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0 = rawRow1096 := by decide +kernel

theorem rowCheck1096 : row1096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1096 := by decide +kernel

theorem rowEval1096 (x : Key → ℝ) : Integer.Sparse.eval row1096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1096, Integer.Sparse.eval_collectBalanced, rawRowCheck1096]

theorem rawRowCheck1097 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0 = rawRow1097 := by decide +kernel

theorem rowCheck1097 : row1097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1097 := by decide +kernel

theorem rowEval1097 (x : Key → ℝ) : Integer.Sparse.eval row1097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1097, Integer.Sparse.eval_collectBalanced, rawRowCheck1097]

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

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block1.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form6.terms k).tag (GramFunctions.Block1.form6.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1084 x
  · exact rowEval1085 x
  · exact rowEval1086 x
  · exact rowEval1087 x
  · exact rowEval1088 x
  · exact rowEval1089 x
  · exact rowEval1090 x
  · exact rowEval1091 x
  · exact rowEval1092 x
  · exact rowEval1093 x
  · exact rowEval1094 x
  · exact rowEval1095 x
  · exact rowEval1096 x
  · exact rowEval1097 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block1.form6.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form6 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

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

theorem entryEvalRow0_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 0).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval0_0_e B hB
  · exact (entryEval1_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval2_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e_oai
