-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:38:45.734501+00:00
-- url     : https://prove2.me/submissions/2a48fd16-3094-4661-902d-4450d780ae13

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E012
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E040
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEvalRow9_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_0_0 :
    Integer.Sparse.reindex key entry_0_0 = GramEntries.Block5.entries 0 0 := by
  decide +kernel

theorem entry_reindex_0_1 :
    Integer.Sparse.reindex key entry_0_1 = GramEntries.Block5.entries 0 1 := by
  decide +kernel

theorem entry_reindex_0_2 :
    Integer.Sparse.reindex key entry_0_2 = GramEntries.Block5.entries 0 2 := by
  decide +kernel

theorem entry_reindex_0_3 :
    Integer.Sparse.reindex key entry_0_3 = GramEntries.Block5.entries 0 3 := by
  decide +kernel

theorem entry_reindex_0_4 :
    Integer.Sparse.reindex key entry_0_4 = GramEntries.Block5.entries 0 4 := by
  decide +kernel

theorem entry_reindex_0_5 :
    Integer.Sparse.reindex key entry_0_5 = GramEntries.Block5.entries 0 5 := by
  decide +kernel

theorem entry_reindex_0_6 :
    Integer.Sparse.reindex key entry_0_6 = GramEntries.Block5.entries 0 6 := by
  decide +kernel

theorem entry_reindex_0_7 :
    Integer.Sparse.reindex key entry_0_7 = GramEntries.Block5.entries 0 7 := by
  decide +kernel

theorem entry_reindex_0_8 :
    Integer.Sparse.reindex key entry_0_8 = GramEntries.Block5.entries 0 8 := by
  decide +kernel

theorem entry_reindex_0_9 :
    Integer.Sparse.reindex key entry_0_9 = GramEntries.Block5.entries 0 9 := by
  decide +kernel

theorem entry_reindex_0_10 :
    Integer.Sparse.reindex key entry_0_10 = GramEntries.Block5.entries 0 10 := by
  decide +kernel

theorem entry_reindex_0_11 :
    Integer.Sparse.reindex key entry_0_11 = GramEntries.Block5.entries 0 11 := by
  decide +kernel

theorem entries_reindex_0 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 0 j) = GramEntries.Block5.entries 0 j := by
  fin_cases j
  · exact entry_reindex_0_0
  · exact entry_reindex_0_1
  · exact entry_reindex_0_2
  · exact entry_reindex_0_3
  · exact entry_reindex_0_4
  · exact entry_reindex_0_5
  · exact entry_reindex_0_6
  · exact entry_reindex_0_7
  · exact entry_reindex_0_8
  · exact entry_reindex_0_9
  · exact entry_reindex_0_10
  · exact entry_reindex_0_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_1_0 :
    Integer.Sparse.reindex key entry_1_0 = GramEntries.Block5.entries 1 0 := by
  decide +kernel

theorem entry_reindex_1_1 :
    Integer.Sparse.reindex key entry_1_1 = GramEntries.Block5.entries 1 1 := by
  decide +kernel

theorem entry_reindex_1_2 :
    Integer.Sparse.reindex key entry_1_2 = GramEntries.Block5.entries 1 2 := by
  decide +kernel

theorem entry_reindex_1_3 :
    Integer.Sparse.reindex key entry_1_3 = GramEntries.Block5.entries 1 3 := by
  decide +kernel

theorem entry_reindex_1_4 :
    Integer.Sparse.reindex key entry_1_4 = GramEntries.Block5.entries 1 4 := by
  decide +kernel

theorem entry_reindex_1_5 :
    Integer.Sparse.reindex key entry_1_5 = GramEntries.Block5.entries 1 5 := by
  decide +kernel

theorem entry_reindex_1_6 :
    Integer.Sparse.reindex key entry_1_6 = GramEntries.Block5.entries 1 6 := by
  decide +kernel

theorem entry_reindex_1_7 :
    Integer.Sparse.reindex key entry_1_7 = GramEntries.Block5.entries 1 7 := by
  decide +kernel

theorem entry_reindex_1_8 :
    Integer.Sparse.reindex key entry_1_8 = GramEntries.Block5.entries 1 8 := by
  decide +kernel

theorem entry_reindex_1_9 :
    Integer.Sparse.reindex key entry_1_9 = GramEntries.Block5.entries 1 9 := by
  decide +kernel

theorem entry_reindex_1_10 :
    Integer.Sparse.reindex key entry_1_10 = GramEntries.Block5.entries 1 10 := by
  decide +kernel

theorem entry_reindex_1_11 :
    Integer.Sparse.reindex key entry_1_11 = GramEntries.Block5.entries 1 11 := by
  decide +kernel

theorem entries_reindex_1 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block5.entries 1 j := by
  fin_cases j
  · exact entry_reindex_1_0
  · exact entry_reindex_1_1
  · exact entry_reindex_1_2
  · exact entry_reindex_1_3
  · exact entry_reindex_1_4
  · exact entry_reindex_1_5
  · exact entry_reindex_1_6
  · exact entry_reindex_1_7
  · exact entry_reindex_1_8
  · exact entry_reindex_1_9
  · exact entry_reindex_1_10
  · exact entry_reindex_1_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_10_0 :
    Integer.Sparse.reindex key entry_10_0 = GramEntries.Block5.entries 10 0 := by
  decide +kernel

theorem entry_reindex_10_1 :
    Integer.Sparse.reindex key entry_10_1 = GramEntries.Block5.entries 10 1 := by
  decide +kernel

theorem entry_reindex_10_2 :
    Integer.Sparse.reindex key entry_10_2 = GramEntries.Block5.entries 10 2 := by
  decide +kernel

theorem entry_reindex_10_3 :
    Integer.Sparse.reindex key entry_10_3 = GramEntries.Block5.entries 10 3 := by
  decide +kernel

theorem entry_reindex_10_4 :
    Integer.Sparse.reindex key entry_10_4 = GramEntries.Block5.entries 10 4 := by
  decide +kernel

theorem entry_reindex_10_5 :
    Integer.Sparse.reindex key entry_10_5 = GramEntries.Block5.entries 10 5 := by
  decide +kernel

theorem entry_reindex_10_6 :
    Integer.Sparse.reindex key entry_10_6 = GramEntries.Block5.entries 10 6 := by
  decide +kernel

theorem entry_reindex_10_7 :
    Integer.Sparse.reindex key entry_10_7 = GramEntries.Block5.entries 10 7 := by
  decide +kernel

theorem entry_reindex_10_8 :
    Integer.Sparse.reindex key entry_10_8 = GramEntries.Block5.entries 10 8 := by
  decide +kernel

theorem entry_reindex_10_9 :
    Integer.Sparse.reindex key entry_10_9 = GramEntries.Block5.entries 10 9 := by
  decide +kernel

theorem entry_reindex_10_10 :
    Integer.Sparse.reindex key entry_10_10 = GramEntries.Block5.entries 10 10 := by
  decide +kernel

theorem entry_reindex_10_11 :
    Integer.Sparse.reindex key entry_10_11 = GramEntries.Block5.entries 10 11 := by
  decide +kernel

theorem entries_reindex_10 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 10 j) = GramEntries.Block5.entries 10 j := by
  fin_cases j
  · exact entry_reindex_10_0
  · exact entry_reindex_10_1
  · exact entry_reindex_10_2
  · exact entry_reindex_10_3
  · exact entry_reindex_10_4
  · exact entry_reindex_10_5
  · exact entry_reindex_10_6
  · exact entry_reindex_10_7
  · exact entry_reindex_10_8
  · exact entry_reindex_10_9
  · exact entry_reindex_10_10
  · exact entry_reindex_10_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_11_0 :
    Integer.Sparse.reindex key entry_11_0 = GramEntries.Block5.entries 11 0 := by
  decide +kernel

theorem entry_reindex_11_1 :
    Integer.Sparse.reindex key entry_11_1 = GramEntries.Block5.entries 11 1 := by
  decide +kernel

theorem entry_reindex_11_2 :
    Integer.Sparse.reindex key entry_11_2 = GramEntries.Block5.entries 11 2 := by
  decide +kernel

theorem entry_reindex_11_3 :
    Integer.Sparse.reindex key entry_11_3 = GramEntries.Block5.entries 11 3 := by
  decide +kernel

theorem entry_reindex_11_4 :
    Integer.Sparse.reindex key entry_11_4 = GramEntries.Block5.entries 11 4 := by
  decide +kernel

theorem entry_reindex_11_5 :
    Integer.Sparse.reindex key entry_11_5 = GramEntries.Block5.entries 11 5 := by
  decide +kernel

theorem entry_reindex_11_6 :
    Integer.Sparse.reindex key entry_11_6 = GramEntries.Block5.entries 11 6 := by
  decide +kernel

theorem entry_reindex_11_7 :
    Integer.Sparse.reindex key entry_11_7 = GramEntries.Block5.entries 11 7 := by
  decide +kernel

theorem entry_reindex_11_8 :
    Integer.Sparse.reindex key entry_11_8 = GramEntries.Block5.entries 11 8 := by
  decide +kernel

theorem entry_reindex_11_9 :
    Integer.Sparse.reindex key entry_11_9 = GramEntries.Block5.entries 11 9 := by
  decide +kernel

theorem entry_reindex_11_10 :
    Integer.Sparse.reindex key entry_11_10 = GramEntries.Block5.entries 11 10 := by
  decide +kernel

theorem entry_reindex_11_11 :
    Integer.Sparse.reindex key entry_11_11 = GramEntries.Block5.entries 11 11 := by
  decide +kernel

theorem entries_reindex_11 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 11 j) = GramEntries.Block5.entries 11 j := by
  fin_cases j
  · exact entry_reindex_11_0
  · exact entry_reindex_11_1
  · exact entry_reindex_11_2
  · exact entry_reindex_11_3
  · exact entry_reindex_11_4
  · exact entry_reindex_11_5
  · exact entry_reindex_11_6
  · exact entry_reindex_11_7
  · exact entry_reindex_11_8
  · exact entry_reindex_11_9
  · exact entry_reindex_11_10
  · exact entry_reindex_11_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block5.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block5.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block5.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block5.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block5.entries 2 4 := by
  decide +kernel

theorem entry_reindex_2_5 :
    Integer.Sparse.reindex key entry_2_5 = GramEntries.Block5.entries 2 5 := by
  decide +kernel

theorem entry_reindex_2_6 :
    Integer.Sparse.reindex key entry_2_6 = GramEntries.Block5.entries 2 6 := by
  decide +kernel

theorem entry_reindex_2_7 :
    Integer.Sparse.reindex key entry_2_7 = GramEntries.Block5.entries 2 7 := by
  decide +kernel

theorem entry_reindex_2_8 :
    Integer.Sparse.reindex key entry_2_8 = GramEntries.Block5.entries 2 8 := by
  decide +kernel

theorem entry_reindex_2_9 :
    Integer.Sparse.reindex key entry_2_9 = GramEntries.Block5.entries 2 9 := by
  decide +kernel

theorem entry_reindex_2_10 :
    Integer.Sparse.reindex key entry_2_10 = GramEntries.Block5.entries 2 10 := by
  decide +kernel

theorem entry_reindex_2_11 :
    Integer.Sparse.reindex key entry_2_11 = GramEntries.Block5.entries 2 11 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block5.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4
  · exact entry_reindex_2_5
  · exact entry_reindex_2_6
  · exact entry_reindex_2_7
  · exact entry_reindex_2_8
  · exact entry_reindex_2_9
  · exact entry_reindex_2_10
  · exact entry_reindex_2_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block5.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block5.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block5.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block5.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block5.entries 3 4 := by
  decide +kernel

theorem entry_reindex_3_5 :
    Integer.Sparse.reindex key entry_3_5 = GramEntries.Block5.entries 3 5 := by
  decide +kernel

theorem entry_reindex_3_6 :
    Integer.Sparse.reindex key entry_3_6 = GramEntries.Block5.entries 3 6 := by
  decide +kernel

theorem entry_reindex_3_7 :
    Integer.Sparse.reindex key entry_3_7 = GramEntries.Block5.entries 3 7 := by
  decide +kernel

theorem entry_reindex_3_8 :
    Integer.Sparse.reindex key entry_3_8 = GramEntries.Block5.entries 3 8 := by
  decide +kernel

theorem entry_reindex_3_9 :
    Integer.Sparse.reindex key entry_3_9 = GramEntries.Block5.entries 3 9 := by
  decide +kernel

theorem entry_reindex_3_10 :
    Integer.Sparse.reindex key entry_3_10 = GramEntries.Block5.entries 3 10 := by
  decide +kernel

theorem entry_reindex_3_11 :
    Integer.Sparse.reindex key entry_3_11 = GramEntries.Block5.entries 3 11 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block5.entries 3 j := by
  fin_cases j
  · exact entry_reindex_3_0
  · exact entry_reindex_3_1
  · exact entry_reindex_3_2
  · exact entry_reindex_3_3
  · exact entry_reindex_3_4
  · exact entry_reindex_3_5
  · exact entry_reindex_3_6
  · exact entry_reindex_3_7
  · exact entry_reindex_3_8
  · exact entry_reindex_3_9
  · exact entry_reindex_3_10
  · exact entry_reindex_3_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_4_0 :
    Integer.Sparse.reindex key entry_4_0 = GramEntries.Block5.entries 4 0 := by
  decide +kernel

theorem entry_reindex_4_1 :
    Integer.Sparse.reindex key entry_4_1 = GramEntries.Block5.entries 4 1 := by
  decide +kernel

theorem entry_reindex_4_2 :
    Integer.Sparse.reindex key entry_4_2 = GramEntries.Block5.entries 4 2 := by
  decide +kernel

theorem entry_reindex_4_3 :
    Integer.Sparse.reindex key entry_4_3 = GramEntries.Block5.entries 4 3 := by
  decide +kernel

theorem entry_reindex_4_4 :
    Integer.Sparse.reindex key entry_4_4 = GramEntries.Block5.entries 4 4 := by
  decide +kernel

theorem entry_reindex_4_5 :
    Integer.Sparse.reindex key entry_4_5 = GramEntries.Block5.entries 4 5 := by
  decide +kernel

theorem entry_reindex_4_6 :
    Integer.Sparse.reindex key entry_4_6 = GramEntries.Block5.entries 4 6 := by
  decide +kernel

theorem entry_reindex_4_7 :
    Integer.Sparse.reindex key entry_4_7 = GramEntries.Block5.entries 4 7 := by
  decide +kernel

theorem entry_reindex_4_8 :
    Integer.Sparse.reindex key entry_4_8 = GramEntries.Block5.entries 4 8 := by
  decide +kernel

theorem entry_reindex_4_9 :
    Integer.Sparse.reindex key entry_4_9 = GramEntries.Block5.entries 4 9 := by
  decide +kernel

theorem entry_reindex_4_10 :
    Integer.Sparse.reindex key entry_4_10 = GramEntries.Block5.entries 4 10 := by
  decide +kernel

theorem entry_reindex_4_11 :
    Integer.Sparse.reindex key entry_4_11 = GramEntries.Block5.entries 4 11 := by
  decide +kernel

theorem entries_reindex_4 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 4 j) = GramEntries.Block5.entries 4 j := by
  fin_cases j
  · exact entry_reindex_4_0
  · exact entry_reindex_4_1
  · exact entry_reindex_4_2
  · exact entry_reindex_4_3
  · exact entry_reindex_4_4
  · exact entry_reindex_4_5
  · exact entry_reindex_4_6
  · exact entry_reindex_4_7
  · exact entry_reindex_4_8
  · exact entry_reindex_4_9
  · exact entry_reindex_4_10
  · exact entry_reindex_4_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_5_0 :
    Integer.Sparse.reindex key entry_5_0 = GramEntries.Block5.entries 5 0 := by
  decide +kernel

theorem entry_reindex_5_1 :
    Integer.Sparse.reindex key entry_5_1 = GramEntries.Block5.entries 5 1 := by
  decide +kernel

theorem entry_reindex_5_2 :
    Integer.Sparse.reindex key entry_5_2 = GramEntries.Block5.entries 5 2 := by
  decide +kernel

theorem entry_reindex_5_3 :
    Integer.Sparse.reindex key entry_5_3 = GramEntries.Block5.entries 5 3 := by
  decide +kernel

theorem entry_reindex_5_4 :
    Integer.Sparse.reindex key entry_5_4 = GramEntries.Block5.entries 5 4 := by
  decide +kernel

theorem entry_reindex_5_5 :
    Integer.Sparse.reindex key entry_5_5 = GramEntries.Block5.entries 5 5 := by
  decide +kernel

theorem entry_reindex_5_6 :
    Integer.Sparse.reindex key entry_5_6 = GramEntries.Block5.entries 5 6 := by
  decide +kernel

theorem entry_reindex_5_7 :
    Integer.Sparse.reindex key entry_5_7 = GramEntries.Block5.entries 5 7 := by
  decide +kernel

theorem entry_reindex_5_8 :
    Integer.Sparse.reindex key entry_5_8 = GramEntries.Block5.entries 5 8 := by
  decide +kernel

theorem entry_reindex_5_9 :
    Integer.Sparse.reindex key entry_5_9 = GramEntries.Block5.entries 5 9 := by
  decide +kernel

theorem entry_reindex_5_10 :
    Integer.Sparse.reindex key entry_5_10 = GramEntries.Block5.entries 5 10 := by
  decide +kernel

theorem entry_reindex_5_11 :
    Integer.Sparse.reindex key entry_5_11 = GramEntries.Block5.entries 5 11 := by
  decide +kernel

theorem entries_reindex_5 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 5 j) = GramEntries.Block5.entries 5 j := by
  fin_cases j
  · exact entry_reindex_5_0
  · exact entry_reindex_5_1
  · exact entry_reindex_5_2
  · exact entry_reindex_5_3
  · exact entry_reindex_5_4
  · exact entry_reindex_5_5
  · exact entry_reindex_5_6
  · exact entry_reindex_5_7
  · exact entry_reindex_5_8
  · exact entry_reindex_5_9
  · exact entry_reindex_5_10
  · exact entry_reindex_5_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_6_0 :
    Integer.Sparse.reindex key entry_6_0 = GramEntries.Block5.entries 6 0 := by
  decide +kernel

theorem entry_reindex_6_1 :
    Integer.Sparse.reindex key entry_6_1 = GramEntries.Block5.entries 6 1 := by
  decide +kernel

theorem entry_reindex_6_2 :
    Integer.Sparse.reindex key entry_6_2 = GramEntries.Block5.entries 6 2 := by
  decide +kernel

theorem entry_reindex_6_3 :
    Integer.Sparse.reindex key entry_6_3 = GramEntries.Block5.entries 6 3 := by
  decide +kernel

theorem entry_reindex_6_4 :
    Integer.Sparse.reindex key entry_6_4 = GramEntries.Block5.entries 6 4 := by
  decide +kernel

theorem entry_reindex_6_5 :
    Integer.Sparse.reindex key entry_6_5 = GramEntries.Block5.entries 6 5 := by
  decide +kernel

theorem entry_reindex_6_6 :
    Integer.Sparse.reindex key entry_6_6 = GramEntries.Block5.entries 6 6 := by
  decide +kernel

theorem entry_reindex_6_7 :
    Integer.Sparse.reindex key entry_6_7 = GramEntries.Block5.entries 6 7 := by
  decide +kernel

theorem entry_reindex_6_8 :
    Integer.Sparse.reindex key entry_6_8 = GramEntries.Block5.entries 6 8 := by
  decide +kernel

theorem entry_reindex_6_9 :
    Integer.Sparse.reindex key entry_6_9 = GramEntries.Block5.entries 6 9 := by
  decide +kernel

theorem entry_reindex_6_10 :
    Integer.Sparse.reindex key entry_6_10 = GramEntries.Block5.entries 6 10 := by
  decide +kernel

theorem entry_reindex_6_11 :
    Integer.Sparse.reindex key entry_6_11 = GramEntries.Block5.entries 6 11 := by
  decide +kernel

theorem entries_reindex_6 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 6 j) = GramEntries.Block5.entries 6 j := by
  fin_cases j
  · exact entry_reindex_6_0
  · exact entry_reindex_6_1
  · exact entry_reindex_6_2
  · exact entry_reindex_6_3
  · exact entry_reindex_6_4
  · exact entry_reindex_6_5
  · exact entry_reindex_6_6
  · exact entry_reindex_6_7
  · exact entry_reindex_6_8
  · exact entry_reindex_6_9
  · exact entry_reindex_6_10
  · exact entry_reindex_6_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_7_0 :
    Integer.Sparse.reindex key entry_7_0 = GramEntries.Block5.entries 7 0 := by
  decide +kernel

theorem entry_reindex_7_1 :
    Integer.Sparse.reindex key entry_7_1 = GramEntries.Block5.entries 7 1 := by
  decide +kernel

theorem entry_reindex_7_2 :
    Integer.Sparse.reindex key entry_7_2 = GramEntries.Block5.entries 7 2 := by
  decide +kernel

theorem entry_reindex_7_3 :
    Integer.Sparse.reindex key entry_7_3 = GramEntries.Block5.entries 7 3 := by
  decide +kernel

theorem entry_reindex_7_4 :
    Integer.Sparse.reindex key entry_7_4 = GramEntries.Block5.entries 7 4 := by
  decide +kernel

theorem entry_reindex_7_5 :
    Integer.Sparse.reindex key entry_7_5 = GramEntries.Block5.entries 7 5 := by
  decide +kernel

theorem entry_reindex_7_6 :
    Integer.Sparse.reindex key entry_7_6 = GramEntries.Block5.entries 7 6 := by
  decide +kernel

theorem entry_reindex_7_7 :
    Integer.Sparse.reindex key entry_7_7 = GramEntries.Block5.entries 7 7 := by
  decide +kernel

theorem entry_reindex_7_8 :
    Integer.Sparse.reindex key entry_7_8 = GramEntries.Block5.entries 7 8 := by
  decide +kernel

theorem entry_reindex_7_9 :
    Integer.Sparse.reindex key entry_7_9 = GramEntries.Block5.entries 7 9 := by
  decide +kernel

theorem entry_reindex_7_10 :
    Integer.Sparse.reindex key entry_7_10 = GramEntries.Block5.entries 7 10 := by
  decide +kernel

theorem entry_reindex_7_11 :
    Integer.Sparse.reindex key entry_7_11 = GramEntries.Block5.entries 7 11 := by
  decide +kernel

theorem entries_reindex_7 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 7 j) = GramEntries.Block5.entries 7 j := by
  fin_cases j
  · exact entry_reindex_7_0
  · exact entry_reindex_7_1
  · exact entry_reindex_7_2
  · exact entry_reindex_7_3
  · exact entry_reindex_7_4
  · exact entry_reindex_7_5
  · exact entry_reindex_7_6
  · exact entry_reindex_7_7
  · exact entry_reindex_7_8
  · exact entry_reindex_7_9
  · exact entry_reindex_7_10
  · exact entry_reindex_7_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_8_0 :
    Integer.Sparse.reindex key entry_8_0 = GramEntries.Block5.entries 8 0 := by
  decide +kernel

theorem entry_reindex_8_1 :
    Integer.Sparse.reindex key entry_8_1 = GramEntries.Block5.entries 8 1 := by
  decide +kernel

theorem entry_reindex_8_2 :
    Integer.Sparse.reindex key entry_8_2 = GramEntries.Block5.entries 8 2 := by
  decide +kernel

theorem entry_reindex_8_3 :
    Integer.Sparse.reindex key entry_8_3 = GramEntries.Block5.entries 8 3 := by
  decide +kernel

theorem entry_reindex_8_4 :
    Integer.Sparse.reindex key entry_8_4 = GramEntries.Block5.entries 8 4 := by
  decide +kernel

theorem entry_reindex_8_5 :
    Integer.Sparse.reindex key entry_8_5 = GramEntries.Block5.entries 8 5 := by
  decide +kernel

theorem entry_reindex_8_6 :
    Integer.Sparse.reindex key entry_8_6 = GramEntries.Block5.entries 8 6 := by
  decide +kernel

theorem entry_reindex_8_7 :
    Integer.Sparse.reindex key entry_8_7 = GramEntries.Block5.entries 8 7 := by
  decide +kernel

theorem entry_reindex_8_8 :
    Integer.Sparse.reindex key entry_8_8 = GramEntries.Block5.entries 8 8 := by
  decide +kernel

theorem entry_reindex_8_9 :
    Integer.Sparse.reindex key entry_8_9 = GramEntries.Block5.entries 8 9 := by
  decide +kernel

theorem entry_reindex_8_10 :
    Integer.Sparse.reindex key entry_8_10 = GramEntries.Block5.entries 8 10 := by
  decide +kernel

theorem entry_reindex_8_11 :
    Integer.Sparse.reindex key entry_8_11 = GramEntries.Block5.entries 8 11 := by
  decide +kernel

theorem entries_reindex_8 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 8 j) = GramEntries.Block5.entries 8 j := by
  fin_cases j
  · exact entry_reindex_8_0
  · exact entry_reindex_8_1
  · exact entry_reindex_8_2
  · exact entry_reindex_8_3
  · exact entry_reindex_8_4
  · exact entry_reindex_8_5
  · exact entry_reindex_8_6
  · exact entry_reindex_8_7
  · exact entry_reindex_8_8
  · exact entry_reindex_8_9
  · exact entry_reindex_8_10
  · exact entry_reindex_8_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entry_reindex_9_0 :
    Integer.Sparse.reindex key entry_9_0 = GramEntries.Block5.entries 9 0 := by
  decide +kernel

theorem entry_reindex_9_1 :
    Integer.Sparse.reindex key entry_9_1 = GramEntries.Block5.entries 9 1 := by
  decide +kernel

theorem entry_reindex_9_2 :
    Integer.Sparse.reindex key entry_9_2 = GramEntries.Block5.entries 9 2 := by
  decide +kernel

theorem entry_reindex_9_3 :
    Integer.Sparse.reindex key entry_9_3 = GramEntries.Block5.entries 9 3 := by
  decide +kernel

theorem entry_reindex_9_4 :
    Integer.Sparse.reindex key entry_9_4 = GramEntries.Block5.entries 9 4 := by
  decide +kernel

theorem entry_reindex_9_5 :
    Integer.Sparse.reindex key entry_9_5 = GramEntries.Block5.entries 9 5 := by
  decide +kernel

theorem entry_reindex_9_6 :
    Integer.Sparse.reindex key entry_9_6 = GramEntries.Block5.entries 9 6 := by
  decide +kernel

theorem entry_reindex_9_7 :
    Integer.Sparse.reindex key entry_9_7 = GramEntries.Block5.entries 9 7 := by
  decide +kernel

theorem entry_reindex_9_8 :
    Integer.Sparse.reindex key entry_9_8 = GramEntries.Block5.entries 9 8 := by
  decide +kernel

theorem entry_reindex_9_9 :
    Integer.Sparse.reindex key entry_9_9 = GramEntries.Block5.entries 9 9 := by
  decide +kernel

theorem entry_reindex_9_10 :
    Integer.Sparse.reindex key entry_9_10 = GramEntries.Block5.entries 9 10 := by
  decide +kernel

theorem entry_reindex_9_11 :
    Integer.Sparse.reindex key entry_9_11 = GramEntries.Block5.entries 9 11 := by
  decide +kernel

theorem entries_reindex_9 (j : Fin 12) :
    Integer.Sparse.reindex key (entries 9 j) = GramEntries.Block5.entries 9 j := by
  fin_cases j
  · exact entry_reindex_9_0
  · exact entry_reindex_9_1
  · exact entry_reindex_9_2
  · exact entry_reindex_9_3
  · exact entry_reindex_9_4
  · exact entry_reindex_9_5
  · exact entry_reindex_9_6
  · exact entry_reindex_9_7
  · exact entry_reindex_9_8
  · exact entry_reindex_9_9
  · exact entry_reindex_9_10
  · exact entry_reindex_9_11

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem entries_reindex (i j : Fin 12) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block5.entries i j := by
  fin_cases i
  · exact entries_reindex_0 j
  · exact entries_reindex_1 j
  · exact entries_reindex_2 j
  · exact entries_reindex_3 j
  · exact entries_reindex_4 j
  · exact entries_reindex_5 j
  · exact entries_reindex_6 j
  · exact entries_reindex_7 j
  · exact entries_reindex_8 j
  · exact entries_reindex_9 j
  · exact entries_reindex_10 j
  · exact entries_reindex_11 j

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19364 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8 = rawRow19364 := by decide +kernel

theorem rowCheck19364 : row19364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19364 := by decide +kernel

theorem rowEval19364 (x : Key → ℝ) : Integer.Sparse.eval row19364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19364, Integer.Sparse.eval_collectBalanced, rawRowCheck19364]

theorem rawRowCheck19365 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8 = rawRow19365 := by decide +kernel

theorem rowCheck19365 : row19365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19365 := by decide +kernel

theorem rowEval19365 (x : Key → ℝ) : Integer.Sparse.eval row19365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19365, Integer.Sparse.eval_collectBalanced, rawRowCheck19365]

theorem rawRowCheck19366 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8 = rawRow19366 := by decide +kernel

theorem rowCheck19366 : row19366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19366 := by decide +kernel

theorem rowEval19366 (x : Key → ℝ) : Integer.Sparse.eval row19366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19366, Integer.Sparse.eval_collectBalanced, rawRowCheck19366]

theorem rawRowCheck19367 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19367 := by decide +kernel

theorem rowCheck19367 : row19367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19367 := by decide +kernel

theorem rowEval19367 (x : Key → ℝ) : Integer.Sparse.eval row19367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19367, Integer.Sparse.eval_collectBalanced, rawRowCheck19367]

theorem rawRowCheck19368 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19368 := by decide +kernel

theorem rowCheck19368 : row19368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19368 := by decide +kernel

theorem rowEval19368 (x : Key → ℝ) : Integer.Sparse.eval row19368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19368, Integer.Sparse.eval_collectBalanced, rawRowCheck19368]

theorem rawRowCheck19369 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19369 := by decide +kernel

theorem rowCheck19369 : row19369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19369 := by decide +kernel

theorem rowEval19369 (x : Key → ℝ) : Integer.Sparse.eval row19369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19369, Integer.Sparse.eval_collectBalanced, rawRowCheck19369]

theorem rawRowCheck19370 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8 = rawRow19370 := by decide +kernel

theorem rowCheck19370 : row19370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19370 := by decide +kernel

theorem rowEval19370 (x : Key → ℝ) : Integer.Sparse.eval row19370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19370, Integer.Sparse.eval_collectBalanced, rawRowCheck19370]

theorem rawRowCheck19371 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8 = rawRow19371 := by decide +kernel

theorem rowCheck19371 : row19371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19371 := by decide +kernel

theorem rowEval19371 (x : Key → ℝ) : Integer.Sparse.eval row19371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19371, Integer.Sparse.eval_collectBalanced, rawRowCheck19371]

theorem rawRowCheck19372 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8 = rawRow19372 := by decide +kernel

theorem rowCheck19372 : row19372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19372 := by decide +kernel

theorem rowEval19372 (x : Key → ℝ) : Integer.Sparse.eval row19372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19372, Integer.Sparse.eval_collectBalanced, rawRowCheck19372]

theorem rawRowCheck19373 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8 = rawRow19373 := by decide +kernel

theorem rowCheck19373 : row19373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19373 := by decide +kernel

theorem rowEval19373 (x : Key → ℝ) : Integer.Sparse.eval row19373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck19373, Integer.Sparse.eval_collectBalanced, rawRowCheck19373]

theorem rawRowCheck19444 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19444 := by decide +kernel

theorem rowCheck19444 : row19444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19444 := by decide +kernel

theorem rowEval19444 (x : Key → ℝ) : Integer.Sparse.eval row19444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19444, Integer.Sparse.eval_collectBalanced, rawRowCheck19444]

theorem rawRowCheck19445 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19445 := by decide +kernel

theorem rowCheck19445 : row19445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19445 := by decide +kernel

theorem rowEval19445 (x : Key → ℝ) : Integer.Sparse.eval row19445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19445, Integer.Sparse.eval_collectBalanced, rawRowCheck19445]

theorem rawRowCheck19446 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19446 := by decide +kernel

theorem rowCheck19446 : row19446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19446 := by decide +kernel

theorem rowEval19446 (x : Key → ℝ) : Integer.Sparse.eval row19446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19446, Integer.Sparse.eval_collectBalanced, rawRowCheck19446]

theorem rawRowCheck19447 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19447 := by decide +kernel

theorem rowCheck19447 : row19447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19447 := by decide +kernel

theorem rowEval19447 (x : Key → ℝ) : Integer.Sparse.eval row19447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19447, Integer.Sparse.eval_collectBalanced, rawRowCheck19447]

theorem rawRowCheck19448 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19448 := by decide +kernel

theorem rowCheck19448 : row19448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19448 := by decide +kernel

theorem rowEval19448 (x : Key → ℝ) : Integer.Sparse.eval row19448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19448, Integer.Sparse.eval_collectBalanced, rawRowCheck19448]

theorem rawRowCheck19449 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19449 := by decide +kernel

theorem rowCheck19449 : row19449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19449 := by decide +kernel

theorem rowEval19449 (x : Key → ℝ) : Integer.Sparse.eval row19449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19449, Integer.Sparse.eval_collectBalanced, rawRowCheck19449]

theorem rawRowCheck19450 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19450 := by decide +kernel

theorem rowCheck19450 : row19450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19450 := by decide +kernel

theorem rowEval19450 (x : Key → ℝ) : Integer.Sparse.eval row19450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19450, Integer.Sparse.eval_collectBalanced, rawRowCheck19450]

theorem rawRowCheck19451 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3 = rawRow19451 := by decide +kernel

theorem rowCheck19451 : row19451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19451 := by decide +kernel

theorem rowEval19451 (x : Key → ℝ) : Integer.Sparse.eval row19451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19451, Integer.Sparse.eval_collectBalanced, rawRowCheck19451]

theorem rawRowCheck19452 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3 = rawRow19452 := by decide +kernel

theorem rowCheck19452 : row19452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19452 := by decide +kernel

theorem rowEval19452 (x : Key → ℝ) : Integer.Sparse.eval row19452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19452, Integer.Sparse.eval_collectBalanced, rawRowCheck19452]

theorem rawRowCheck19453 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3 = rawRow19453 := by decide +kernel

theorem rowCheck19453 : row19453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19453 := by decide +kernel

theorem rowEval19453 (x : Key → ℝ) : Integer.Sparse.eval row19453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19453, Integer.Sparse.eval_collectBalanced, rawRowCheck19453]

theorem rawRowCheck19454 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3 = rawRow19454 := by decide +kernel

theorem rowCheck19454 : row19454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19454 := by decide +kernel

theorem rowEval19454 (x : Key → ℝ) : Integer.Sparse.eval row19454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19454, Integer.Sparse.eval_collectBalanced, rawRowCheck19454]

theorem rawRowCheck19455 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3 = rawRow19455 := by decide +kernel

theorem rowCheck19455 : row19455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19455 := by decide +kernel

theorem rowEval19455 (x : Key → ℝ) : Integer.Sparse.eval row19455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19455, Integer.Sparse.eval_collectBalanced, rawRowCheck19455]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19456 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3 = rawRow19456 := by decide +kernel

theorem rowCheck19456 : row19456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19456 := by decide +kernel

theorem rowEval19456 (x : Key → ℝ) : Integer.Sparse.eval row19456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19456, Integer.Sparse.eval_collectBalanced, rawRowCheck19456]

theorem rawRowCheck19457 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19457 := by decide +kernel

theorem rowCheck19457 : row19457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19457 := by decide +kernel

theorem rowEval19457 (x : Key → ℝ) : Integer.Sparse.eval row19457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19457, Integer.Sparse.eval_collectBalanced, rawRowCheck19457]

theorem rawRowCheck19458 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19458 := by decide +kernel

theorem rowCheck19458 : row19458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19458 := by decide +kernel

theorem rowEval19458 (x : Key → ℝ) : Integer.Sparse.eval row19458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19458, Integer.Sparse.eval_collectBalanced, rawRowCheck19458]

theorem rawRowCheck19459 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19459 := by decide +kernel

theorem rowCheck19459 : row19459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19459 := by decide +kernel

theorem rowEval19459 (x : Key → ℝ) : Integer.Sparse.eval row19459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19459, Integer.Sparse.eval_collectBalanced, rawRowCheck19459]

theorem rawRowCheck19460 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19460 := by decide +kernel

theorem rowCheck19460 : row19460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19460 := by decide +kernel

theorem rowEval19460 (x : Key → ℝ) : Integer.Sparse.eval row19460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19460, Integer.Sparse.eval_collectBalanced, rawRowCheck19460]

theorem rawRowCheck19461 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19461 := by decide +kernel

theorem rowCheck19461 : row19461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19461 := by decide +kernel

theorem rowEval19461 (x : Key → ℝ) : Integer.Sparse.eval row19461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19461, Integer.Sparse.eval_collectBalanced, rawRowCheck19461]

theorem rawRowCheck19462 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19462 := by decide +kernel

theorem rowCheck19462 : row19462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19462 := by decide +kernel

theorem rowEval19462 (x : Key → ℝ) : Integer.Sparse.eval row19462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19462, Integer.Sparse.eval_collectBalanced, rawRowCheck19462]

theorem rawRowCheck19463 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19463 := by decide +kernel

theorem rowCheck19463 : row19463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19463 := by decide +kernel

theorem rowEval19463 (x : Key → ℝ) : Integer.Sparse.eval row19463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19463, Integer.Sparse.eval_collectBalanced, rawRowCheck19463]

theorem rawRowCheck19544 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19544 := by decide +kernel

theorem rowCheck19544 : row19544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19544 := by decide +kernel

theorem rowEval19544 (x : Key → ℝ) : Integer.Sparse.eval row19544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19544, Integer.Sparse.eval_collectBalanced, rawRowCheck19544]

theorem rawRowCheck19545 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19545 := by decide +kernel

theorem rowCheck19545 : row19545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19545 := by decide +kernel

theorem rowEval19545 (x : Key → ℝ) : Integer.Sparse.eval row19545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19545, Integer.Sparse.eval_collectBalanced, rawRowCheck19545]

theorem rawRowCheck19546 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19546 := by decide +kernel

theorem rowCheck19546 : row19546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19546 := by decide +kernel

theorem rowEval19546 (x : Key → ℝ) : Integer.Sparse.eval row19546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19546, Integer.Sparse.eval_collectBalanced, rawRowCheck19546]

theorem rawRowCheck19547 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19547 := by decide +kernel

theorem rowCheck19547 : row19547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19547 := by decide +kernel

theorem rowEval19547 (x : Key → ℝ) : Integer.Sparse.eval row19547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19547, Integer.Sparse.eval_collectBalanced, rawRowCheck19547]

theorem rawRowCheck19548 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19548 := by decide +kernel

theorem rowCheck19548 : row19548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19548 := by decide +kernel

theorem rowEval19548 (x : Key → ℝ) : Integer.Sparse.eval row19548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19548, Integer.Sparse.eval_collectBalanced, rawRowCheck19548]

theorem rawRowCheck19549 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19549 := by decide +kernel

theorem rowCheck19549 : row19549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19549 := by decide +kernel

theorem rowEval19549 (x : Key → ℝ) : Integer.Sparse.eval row19549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19549, Integer.Sparse.eval_collectBalanced, rawRowCheck19549]

theorem rawRowCheck19550 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19550 := by decide +kernel

theorem rowCheck19550 : row19550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19550 := by decide +kernel

theorem rowEval19550 (x : Key → ℝ) : Integer.Sparse.eval row19550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19550, Integer.Sparse.eval_collectBalanced, rawRowCheck19550]

theorem rawRowCheck19551 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow19551 := by decide +kernel

theorem rowCheck19551 : row19551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19551 := by decide +kernel

theorem rowEval19551 (x : Key → ℝ) : Integer.Sparse.eval row19551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19551, Integer.Sparse.eval_collectBalanced, rawRowCheck19551]

theorem rawRowCheck19552 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow19552 := by decide +kernel

theorem rowCheck19552 : row19552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19552 := by decide +kernel

theorem rowEval19552 (x : Key → ℝ) : Integer.Sparse.eval row19552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19552, Integer.Sparse.eval_collectBalanced, rawRowCheck19552]

theorem rawRowCheck19553 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow19553 := by decide +kernel

theorem rowCheck19553 : row19553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19553 := by decide +kernel

theorem rowEval19553 (x : Key → ℝ) : Integer.Sparse.eval row19553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19553, Integer.Sparse.eval_collectBalanced, rawRowCheck19553]

theorem rawRowCheck19554 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow19554 := by decide +kernel

theorem rowCheck19554 : row19554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19554 := by decide +kernel

theorem rowEval19554 (x : Key → ℝ) : Integer.Sparse.eval row19554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19554, Integer.Sparse.eval_collectBalanced, rawRowCheck19554]

theorem rawRowCheck19555 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow19555 := by decide +kernel

theorem rowCheck19555 : row19555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19555 := by decide +kernel

theorem rowEval19555 (x : Key → ℝ) : Integer.Sparse.eval row19555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19555, Integer.Sparse.eval_collectBalanced, rawRowCheck19555]

theorem rawRowCheck19556 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow19556 := by decide +kernel

theorem rowCheck19556 : row19556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19556 := by decide +kernel

theorem rowEval19556 (x : Key → ℝ) : Integer.Sparse.eval row19556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19556, Integer.Sparse.eval_collectBalanced, rawRowCheck19556]

theorem rawRowCheck19557 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19557 := by decide +kernel

theorem rowCheck19557 : row19557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19557 := by decide +kernel

theorem rowEval19557 (x : Key → ℝ) : Integer.Sparse.eval row19557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19557, Integer.Sparse.eval_collectBalanced, rawRowCheck19557]

theorem rawRowCheck19558 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19558 := by decide +kernel

theorem rowCheck19558 : row19558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19558 := by decide +kernel

theorem rowEval19558 (x : Key → ℝ) : Integer.Sparse.eval row19558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19558, Integer.Sparse.eval_collectBalanced, rawRowCheck19558]

theorem rawRowCheck19559 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19559 := by decide +kernel

theorem rowCheck19559 : row19559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19559 := by decide +kernel

theorem rowEval19559 (x : Key → ℝ) : Integer.Sparse.eval row19559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19559, Integer.Sparse.eval_collectBalanced, rawRowCheck19559]

theorem rawRowCheck19560 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19560 := by decide +kernel

theorem rowCheck19560 : row19560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19560 := by decide +kernel

theorem rowEval19560 (x : Key → ℝ) : Integer.Sparse.eval row19560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19560, Integer.Sparse.eval_collectBalanced, rawRowCheck19560]

theorem rawRowCheck19561 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19561 := by decide +kernel

theorem rowCheck19561 : row19561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19561 := by decide +kernel

theorem rowEval19561 (x : Key → ℝ) : Integer.Sparse.eval row19561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19561, Integer.Sparse.eval_collectBalanced, rawRowCheck19561]

theorem rawRowCheck19562 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19562 := by decide +kernel

theorem rowCheck19562 : row19562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19562 := by decide +kernel

theorem rowEval19562 (x : Key → ℝ) : Integer.Sparse.eval row19562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19562, Integer.Sparse.eval_collectBalanced, rawRowCheck19562]

theorem rawRowCheck19563 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19563 := by decide +kernel

theorem rowCheck19563 : row19563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19563 := by decide +kernel

theorem rowEval19563 (x : Key → ℝ) : Integer.Sparse.eval row19563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19563, Integer.Sparse.eval_collectBalanced, rawRowCheck19563]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19444 x
  · exact rowEval19445 x
  · exact rowEval19446 x
  · exact rowEval19447 x
  · exact rowEval19448 x
  · exact rowEval19449 x
  · exact rowEval19450 x
  · exact rowEval19451 x
  · exact rowEval19452 x
  · exact rowEval19453 x
  · exact rowEval19454 x
  · exact rowEval19455 x
  · exact rowEval19456 x
  · exact rowEval19457 x
  · exact rowEval19458 x
  · exact rowEval19459 x
  · exact rowEval19460 x
  · exact rowEval19461 x
  · exact rowEval19462 x
  · exact rowEval19463 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19544 x
  · exact rowEval19545 x
  · exact rowEval19546 x
  · exact rowEval19547 x
  · exact rowEval19548 x
  · exact rowEval19549 x
  · exact rowEval19550 x
  · exact rowEval19551 x
  · exact rowEval19552 x
  · exact rowEval19553 x
  · exact rowEval19554 x
  · exact rowEval19555 x
  · exact rowEval19556 x
  · exact rowEval19557 x
  · exact rowEval19558 x
  · exact rowEval19559 x
  · exact rowEval19560 x
  · exact rowEval19561 x
  · exact rowEval19562 x
  · exact rowEval19563 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20084 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20084 := by decide +kernel

theorem rowCheck20084 : row20084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20084 := by decide +kernel

theorem rowEval20084 (x : Key → ℝ) : Integer.Sparse.eval row20084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20084, Integer.Sparse.eval_collectBalanced, rawRowCheck20084]

theorem rawRowCheck20085 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20085 := by decide +kernel

theorem rowCheck20085 : row20085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20085 := by decide +kernel

theorem rowEval20085 (x : Key → ℝ) : Integer.Sparse.eval row20085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20085, Integer.Sparse.eval_collectBalanced, rawRowCheck20085]

theorem rawRowCheck20086 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20086 := by decide +kernel

theorem rowCheck20086 : row20086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20086 := by decide +kernel

theorem rowEval20086 (x : Key → ℝ) : Integer.Sparse.eval row20086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20086, Integer.Sparse.eval_collectBalanced, rawRowCheck20086]

theorem rawRowCheck20087 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20087 := by decide +kernel

theorem rowCheck20087 : row20087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20087 := by decide +kernel

theorem rowEval20087 (x : Key → ℝ) : Integer.Sparse.eval row20087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20087, Integer.Sparse.eval_collectBalanced, rawRowCheck20087]

theorem rawRowCheck20088 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20088 := by decide +kernel

theorem rowCheck20088 : row20088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20088 := by decide +kernel

theorem rowEval20088 (x : Key → ℝ) : Integer.Sparse.eval row20088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20088, Integer.Sparse.eval_collectBalanced, rawRowCheck20088]

theorem rawRowCheck20089 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20089 := by decide +kernel

theorem rowCheck20089 : row20089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20089 := by decide +kernel

theorem rowEval20089 (x : Key → ℝ) : Integer.Sparse.eval row20089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20089, Integer.Sparse.eval_collectBalanced, rawRowCheck20089]

theorem rawRowCheck20090 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20090 := by decide +kernel

theorem rowCheck20090 : row20090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20090 := by decide +kernel

theorem rowEval20090 (x : Key → ℝ) : Integer.Sparse.eval row20090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20090, Integer.Sparse.eval_collectBalanced, rawRowCheck20090]

theorem rawRowCheck20091 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20091 := by decide +kernel

theorem rowCheck20091 : row20091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20091 := by decide +kernel

theorem rowEval20091 (x : Key → ℝ) : Integer.Sparse.eval row20091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20091, Integer.Sparse.eval_collectBalanced, rawRowCheck20091]

theorem rawRowCheck20092 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20092 := by decide +kernel

theorem rowCheck20092 : row20092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20092 := by decide +kernel

theorem rowEval20092 (x : Key → ℝ) : Integer.Sparse.eval row20092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20092, Integer.Sparse.eval_collectBalanced, rawRowCheck20092]

theorem rawRowCheck20093 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20093 := by decide +kernel

theorem rowCheck20093 : row20093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20093 := by decide +kernel

theorem rowEval20093 (x : Key → ℝ) : Integer.Sparse.eval row20093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20093, Integer.Sparse.eval_collectBalanced, rawRowCheck20093]

theorem rawRowCheck20094 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20094 := by decide +kernel

theorem rowCheck20094 : row20094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20094 := by decide +kernel

theorem rowEval20094 (x : Key → ℝ) : Integer.Sparse.eval row20094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20094, Integer.Sparse.eval_collectBalanced, rawRowCheck20094]

theorem rawRowCheck20095 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20095 := by decide +kernel

theorem rowCheck20095 : row20095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20095 := by decide +kernel

theorem rowEval20095 (x : Key → ℝ) : Integer.Sparse.eval row20095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20095, Integer.Sparse.eval_collectBalanced, rawRowCheck20095]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20096 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20096 := by decide +kernel

theorem rowCheck20096 : row20096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20096 := by decide +kernel

theorem rowEval20096 (x : Key → ℝ) : Integer.Sparse.eval row20096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20096, Integer.Sparse.eval_collectBalanced, rawRowCheck20096]

theorem rawRowCheck20097 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20097 := by decide +kernel

theorem rowCheck20097 : row20097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20097 := by decide +kernel

theorem rowEval20097 (x : Key → ℝ) : Integer.Sparse.eval row20097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20097, Integer.Sparse.eval_collectBalanced, rawRowCheck20097]

theorem rawRowCheck20098 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20098 := by decide +kernel

theorem rowCheck20098 : row20098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20098 := by decide +kernel

theorem rowEval20098 (x : Key → ℝ) : Integer.Sparse.eval row20098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20098, Integer.Sparse.eval_collectBalanced, rawRowCheck20098]

theorem rawRowCheck20099 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20099 := by decide +kernel

theorem rowCheck20099 : row20099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20099 := by decide +kernel

theorem rowEval20099 (x : Key → ℝ) : Integer.Sparse.eval row20099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20099, Integer.Sparse.eval_collectBalanced, rawRowCheck20099]

theorem rawRowCheck20100 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20100 := by decide +kernel

theorem rowCheck20100 : row20100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20100 := by decide +kernel

theorem rowEval20100 (x : Key → ℝ) : Integer.Sparse.eval row20100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20100, Integer.Sparse.eval_collectBalanced, rawRowCheck20100]

theorem rawRowCheck20101 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20101 := by decide +kernel

theorem rowCheck20101 : row20101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20101 := by decide +kernel

theorem rowEval20101 (x : Key → ℝ) : Integer.Sparse.eval row20101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20101, Integer.Sparse.eval_collectBalanced, rawRowCheck20101]

theorem rawRowCheck20102 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20102 := by decide +kernel

theorem rowCheck20102 : row20102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20102 := by decide +kernel

theorem rowEval20102 (x : Key → ℝ) : Integer.Sparse.eval row20102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20102, Integer.Sparse.eval_collectBalanced, rawRowCheck20102]

theorem rawRowCheck20103 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20103 := by decide +kernel

theorem rowCheck20103 : row20103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20103 := by decide +kernel

theorem rowEval20103 (x : Key → ℝ) : Integer.Sparse.eval row20103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20103, Integer.Sparse.eval_collectBalanced, rawRowCheck20103]

theorem rawRowCheck20104 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20104 := by decide +kernel

theorem rowCheck20104 : row20104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20104 := by decide +kernel

theorem rowEval20104 (x : Key → ℝ) : Integer.Sparse.eval row20104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20104, Integer.Sparse.eval_collectBalanced, rawRowCheck20104]

theorem rawRowCheck20105 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20105 := by decide +kernel

theorem rowCheck20105 : row20105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20105 := by decide +kernel

theorem rowEval20105 (x : Key → ℝ) : Integer.Sparse.eval row20105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20105, Integer.Sparse.eval_collectBalanced, rawRowCheck20105]

theorem rawRowCheck20106 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20106 := by decide +kernel

theorem rowCheck20106 : row20106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20106 := by decide +kernel

theorem rowEval20106 (x : Key → ℝ) : Integer.Sparse.eval row20106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20106, Integer.Sparse.eval_collectBalanced, rawRowCheck20106]

theorem rawRowCheck20107 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20107 := by decide +kernel

theorem rowCheck20107 : row20107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20107 := by decide +kernel

theorem rowEval20107 (x : Key → ℝ) : Integer.Sparse.eval row20107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20107, Integer.Sparse.eval_collectBalanced, rawRowCheck20107]

theorem rawRowCheck20108 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20108 := by decide +kernel

theorem rowCheck20108 : row20108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20108 := by decide +kernel

theorem rowEval20108 (x : Key → ℝ) : Integer.Sparse.eval row20108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20108, Integer.Sparse.eval_collectBalanced, rawRowCheck20108]

theorem rawRowCheck20109 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20109 := by decide +kernel

theorem rowCheck20109 : row20109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20109 := by decide +kernel

theorem rowEval20109 (x : Key → ℝ) : Integer.Sparse.eval row20109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20109, Integer.Sparse.eval_collectBalanced, rawRowCheck20109]

theorem rawRowCheck20110 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20110 := by decide +kernel

theorem rowCheck20110 : row20110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20110 := by decide +kernel

theorem rowEval20110 (x : Key → ℝ) : Integer.Sparse.eval row20110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20110, Integer.Sparse.eval_collectBalanced, rawRowCheck20110]

theorem rawRowCheck20111 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20111 := by decide +kernel

theorem rowCheck20111 : row20111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20111 := by decide +kernel

theorem rowEval20111 (x : Key → ℝ) : Integer.Sparse.eval row20111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20111, Integer.Sparse.eval_collectBalanced, rawRowCheck20111]

theorem rawRowCheck20112 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20112 := by decide +kernel

theorem rowCheck20112 : row20112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20112 := by decide +kernel

theorem rowEval20112 (x : Key → ℝ) : Integer.Sparse.eval row20112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20112, Integer.Sparse.eval_collectBalanced, rawRowCheck20112]

theorem rawRowCheck20113 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20113 := by decide +kernel

theorem rowCheck20113 : row20113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20113 := by decide +kernel

theorem rowEval20113 (x : Key → ℝ) : Integer.Sparse.eval row20113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20113, Integer.Sparse.eval_collectBalanced, rawRowCheck20113]

theorem rawRowCheck20114 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20114 := by decide +kernel

theorem rowCheck20114 : row20114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20114 := by decide +kernel

theorem rowEval20114 (x : Key → ℝ) : Integer.Sparse.eval row20114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20114, Integer.Sparse.eval_collectBalanced, rawRowCheck20114]

theorem rawRowCheck20115 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20115 := by decide +kernel

theorem rowCheck20115 : row20115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20115 := by decide +kernel

theorem rowEval20115 (x : Key → ℝ) : Integer.Sparse.eval row20115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20115, Integer.Sparse.eval_collectBalanced, rawRowCheck20115]

theorem rawRowCheck20116 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20116 := by decide +kernel

theorem rowCheck20116 : row20116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20116 := by decide +kernel

theorem rowEval20116 (x : Key → ℝ) : Integer.Sparse.eval row20116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20116, Integer.Sparse.eval_collectBalanced, rawRowCheck20116]

theorem rawRowCheck20117 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20117 := by decide +kernel

theorem rowCheck20117 : row20117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20117 := by decide +kernel

theorem rowEval20117 (x : Key → ℝ) : Integer.Sparse.eval row20117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20117, Integer.Sparse.eval_collectBalanced, rawRowCheck20117]

theorem rawRowCheck20118 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20118 := by decide +kernel

theorem rowCheck20118 : row20118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20118 := by decide +kernel

theorem rowEval20118 (x : Key → ℝ) : Integer.Sparse.eval row20118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20118, Integer.Sparse.eval_collectBalanced, rawRowCheck20118]

theorem rawRowCheck20119 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20119 := by decide +kernel

theorem rowCheck20119 : row20119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20119 := by decide +kernel

theorem rowEval20119 (x : Key → ℝ) : Integer.Sparse.eval row20119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20119, Integer.Sparse.eval_collectBalanced, rawRowCheck20119]

theorem rawRowCheck20120 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8 = rawRow20120 := by decide +kernel

theorem rowCheck20120 : row20120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20120 := by decide +kernel

theorem rowEval20120 (x : Key → ℝ) : Integer.Sparse.eval row20120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20120, Integer.Sparse.eval_collectBalanced, rawRowCheck20120]

theorem rawRowCheck20121 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8 = rawRow20121 := by decide +kernel

theorem rowCheck20121 : row20121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20121 := by decide +kernel

theorem rowEval20121 (x : Key → ℝ) : Integer.Sparse.eval row20121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20121, Integer.Sparse.eval_collectBalanced, rawRowCheck20121]

theorem rawRowCheck20122 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8 = rawRow20122 := by decide +kernel

theorem rowCheck20122 : row20122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20122 := by decide +kernel

theorem rowEval20122 (x : Key → ℝ) : Integer.Sparse.eval row20122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20122, Integer.Sparse.eval_collectBalanced, rawRowCheck20122]

theorem rawRowCheck20123 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8 = rawRow20123 := by decide +kernel

theorem rowCheck20123 : row20123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20123 := by decide +kernel

theorem rowEval20123 (x : Key → ℝ) : Integer.Sparse.eval row20123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20123, Integer.Sparse.eval_collectBalanced, rawRowCheck20123]

theorem rawRowCheck20124 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8 = rawRow20124 := by decide +kernel

theorem rowCheck20124 : row20124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20124 := by decide +kernel

theorem rowEval20124 (x : Key → ℝ) : Integer.Sparse.eval row20124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20124, Integer.Sparse.eval_collectBalanced, rawRowCheck20124]

theorem rawRowCheck20125 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8 = rawRow20125 := by decide +kernel

theorem rowCheck20125 : row20125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20125 := by decide +kernel

theorem rowEval20125 (x : Key → ℝ) : Integer.Sparse.eval row20125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20125, Integer.Sparse.eval_collectBalanced, rawRowCheck20125]

theorem rawRowCheck20126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20126 := by decide +kernel

theorem rowCheck20126 : row20126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20126 := by decide +kernel

theorem rowEval20126 (x : Key → ℝ) : Integer.Sparse.eval row20126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20126, Integer.Sparse.eval_collectBalanced, rawRowCheck20126]

theorem rawRowCheck20127 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20127 := by decide +kernel

theorem rowCheck20127 : row20127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20127 := by decide +kernel

theorem rowEval20127 (x : Key → ℝ) : Integer.Sparse.eval row20127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20127, Integer.Sparse.eval_collectBalanced, rawRowCheck20127]

theorem rawRowCheck20128 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20128 := by decide +kernel

theorem rowCheck20128 : row20128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20128 := by decide +kernel

theorem rowEval20128 (x : Key → ℝ) : Integer.Sparse.eval row20128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20128, Integer.Sparse.eval_collectBalanced, rawRowCheck20128]

theorem rawRowCheck20129 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20129 := by decide +kernel

theorem rowCheck20129 : row20129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20129 := by decide +kernel

theorem rowEval20129 (x : Key → ℝ) : Integer.Sparse.eval row20129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20129, Integer.Sparse.eval_collectBalanced, rawRowCheck20129]

theorem rawRowCheck20130 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20130 := by decide +kernel

theorem rowCheck20130 : row20130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20130 := by decide +kernel

theorem rowEval20130 (x : Key → ℝ) : Integer.Sparse.eval row20130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20130, Integer.Sparse.eval_collectBalanced, rawRowCheck20130]

theorem rawRowCheck20131 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20131 := by decide +kernel

theorem rowCheck20131 : row20131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20131 := by decide +kernel

theorem rowEval20131 (x : Key → ℝ) : Integer.Sparse.eval row20131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20131, Integer.Sparse.eval_collectBalanced, rawRowCheck20131]

theorem rawRowCheck20132 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20132 := by decide +kernel

theorem rowCheck20132 : row20132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20132 := by decide +kernel

theorem rowEval20132 (x : Key → ℝ) : Integer.Sparse.eval row20132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20132, Integer.Sparse.eval_collectBalanced, rawRowCheck20132]

theorem rawRowCheck20133 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20133 := by decide +kernel

theorem rowCheck20133 : row20133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20133 := by decide +kernel

theorem rowEval20133 (x : Key → ℝ) : Integer.Sparse.eval row20133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20133, Integer.Sparse.eval_collectBalanced, rawRowCheck20133]

theorem rawRowCheck20134 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20134 := by decide +kernel

theorem rowCheck20134 : row20134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20134 := by decide +kernel

theorem rowEval20134 (x : Key → ℝ) : Integer.Sparse.eval row20134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20134, Integer.Sparse.eval_collectBalanced, rawRowCheck20134]

theorem rawRowCheck20135 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20135 := by decide +kernel

theorem rowCheck20135 : row20135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20135 := by decide +kernel

theorem rowEval20135 (x : Key → ℝ) : Integer.Sparse.eval row20135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20135, Integer.Sparse.eval_collectBalanced, rawRowCheck20135]

theorem rawRowCheck20136 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20136 := by decide +kernel

theorem rowCheck20136 : row20136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20136 := by decide +kernel

theorem rowEval20136 (x : Key → ℝ) : Integer.Sparse.eval row20136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20136, Integer.Sparse.eval_collectBalanced, rawRowCheck20136]

theorem rawRowCheck20137 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20137 := by decide +kernel

theorem rowCheck20137 : row20137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20137 := by decide +kernel

theorem rowEval20137 (x : Key → ℝ) : Integer.Sparse.eval row20137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20137, Integer.Sparse.eval_collectBalanced, rawRowCheck20137]

theorem rawRowCheck20138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20138 := by decide +kernel

theorem rowCheck20138 : row20138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20138 := by decide +kernel

theorem rowEval20138 (x : Key → ℝ) : Integer.Sparse.eval row20138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20138, Integer.Sparse.eval_collectBalanced, rawRowCheck20138]

theorem rawRowCheck20139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20139 := by decide +kernel

theorem rowCheck20139 : row20139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20139 := by decide +kernel

theorem rowEval20139 (x : Key → ℝ) : Integer.Sparse.eval row20139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20139, Integer.Sparse.eval_collectBalanced, rawRowCheck20139]

theorem rawRowCheck20140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20140 := by decide +kernel

theorem rowCheck20140 : row20140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20140 := by decide +kernel

theorem rowEval20140 (x : Key → ℝ) : Integer.Sparse.eval row20140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20140, Integer.Sparse.eval_collectBalanced, rawRowCheck20140]

theorem rawRowCheck20141 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20141 := by decide +kernel

theorem rowCheck20141 : row20141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20141 := by decide +kernel

theorem rowEval20141 (x : Key → ℝ) : Integer.Sparse.eval row20141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20141, Integer.Sparse.eval_collectBalanced, rawRowCheck20141]

theorem rawRowCheck20142 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20142 := by decide +kernel

theorem rowCheck20142 : row20142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20142 := by decide +kernel

theorem rowEval20142 (x : Key → ℝ) : Integer.Sparse.eval row20142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20142, Integer.Sparse.eval_collectBalanced, rawRowCheck20142]

theorem rawRowCheck20143 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20143 := by decide +kernel

theorem rowCheck20143 : row20143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20143 := by decide +kernel

theorem rowEval20143 (x : Key → ℝ) : Integer.Sparse.eval row20143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20143, Integer.Sparse.eval_collectBalanced, rawRowCheck20143]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval20084 x
  · exact rowEval20085 x
  · exact rowEval20086 x
  · exact rowEval20087 x
  · exact rowEval20088 x
  · exact rowEval20089 x
  · exact rowEval20090 x
  · exact rowEval20091 x
  · exact rowEval20092 x
  · exact rowEval20093 x
  · exact rowEval20094 x
  · exact rowEval20095 x
  · exact rowEval20096 x
  · exact rowEval20097 x
  · exact rowEval20098 x
  · exact rowEval20099 x
  · exact rowEval20100 x
  · exact rowEval20101 x
  · exact rowEval20102 x
  · exact rowEval20103 x
  · exact rowEval20104 x
  · exact rowEval20105 x
  · exact rowEval20106 x
  · exact rowEval20107 x
  · exact rowEval20108 x
  · exact rowEval20109 x
  · exact rowEval20110 x
  · exact rowEval20111 x
  · exact rowEval20112 x
  · exact rowEval20113 x
  · exact rowEval20114 x
  · exact rowEval20115 x
  · exact rowEval20116 x
  · exact rowEval20117 x
  · exact rowEval20118 x
  · exact rowEval20119 x
  · exact rowEval20120 x
  · exact rowEval20121 x
  · exact rowEval20122 x
  · exact rowEval20123 x
  · exact rowEval20124 x
  · exact rowEval20125 x
  · exact rowEval20126 x
  · exact rowEval20127 x
  · exact rowEval20128 x
  · exact rowEval20129 x
  · exact rowEval20130 x
  · exact rowEval20131 x
  · exact rowEval20132 x
  · exact rowEval20133 x
  · exact rowEval20134 x
  · exact rowEval20135 x
  · exact rowEval20136 x
  · exact rowEval20137 x
  · exact rowEval20138 x
  · exact rowEval20139 x
  · exact rowEval20140 x
  · exact rowEval20141 x
  · exact rowEval20142 x
  · exact rowEval20143 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18639 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18639 := by decide +kernel

theorem rowCheck18639 : row18639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18639 := by decide +kernel

theorem rowEval18639 (x : Key → ℝ) : Integer.Sparse.eval row18639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18639, Integer.Sparse.eval_collectBalanced, rawRowCheck18639]

theorem rawRowCheck18640 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18640 := by decide +kernel

theorem rowCheck18640 : row18640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18640 := by decide +kernel

theorem rowEval18640 (x : Key → ℝ) : Integer.Sparse.eval row18640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18640, Integer.Sparse.eval_collectBalanced, rawRowCheck18640]

theorem rawRowCheck18641 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18641 := by decide +kernel

theorem rowCheck18641 : row18641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18641 := by decide +kernel

theorem rowEval18641 (x : Key → ℝ) : Integer.Sparse.eval row18641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18641, Integer.Sparse.eval_collectBalanced, rawRowCheck18641]

theorem rawRowCheck18642 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18642 := by decide +kernel

theorem rowCheck18642 : row18642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18642 := by decide +kernel

theorem rowEval18642 (x : Key → ℝ) : Integer.Sparse.eval row18642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18642, Integer.Sparse.eval_collectBalanced, rawRowCheck18642]

theorem rawRowCheck18643 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18643 := by decide +kernel

theorem rowCheck18643 : row18643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18643 := by decide +kernel

theorem rowEval18643 (x : Key → ℝ) : Integer.Sparse.eval row18643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18643, Integer.Sparse.eval_collectBalanced, rawRowCheck18643]

theorem rawRowCheck18644 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18644 := by decide +kernel

theorem rowCheck18644 : row18644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18644 := by decide +kernel

theorem rowEval18644 (x : Key → ℝ) : Integer.Sparse.eval row18644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18644, Integer.Sparse.eval_collectBalanced, rawRowCheck18644]

theorem rawRowCheck18645 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18645 := by decide +kernel

theorem rowCheck18645 : row18645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18645 := by decide +kernel

theorem rowEval18645 (x : Key → ℝ) : Integer.Sparse.eval row18645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18645, Integer.Sparse.eval_collectBalanced, rawRowCheck18645]

theorem rawRowCheck18646 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18646 := by decide +kernel

theorem rowCheck18646 : row18646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18646 := by decide +kernel

theorem rowEval18646 (x : Key → ℝ) : Integer.Sparse.eval row18646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18646, Integer.Sparse.eval_collectBalanced, rawRowCheck18646]

theorem rawRowCheck18647 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18647 := by decide +kernel

theorem rowCheck18647 : row18647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18647 := by decide +kernel

theorem rowEval18647 (x : Key → ℝ) : Integer.Sparse.eval row18647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18647, Integer.Sparse.eval_collectBalanced, rawRowCheck18647]

theorem rawRowCheck18648 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18648 := by decide +kernel

theorem rowCheck18648 : row18648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18648 := by decide +kernel

theorem rowEval18648 (x : Key → ℝ) : Integer.Sparse.eval row18648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18648, Integer.Sparse.eval_collectBalanced, rawRowCheck18648]

theorem rawRowCheck18649 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18649 := by decide +kernel

theorem rowCheck18649 : row18649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18649 := by decide +kernel

theorem rowEval18649 (x : Key → ℝ) : Integer.Sparse.eval row18649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18649, Integer.Sparse.eval_collectBalanced, rawRowCheck18649]

theorem rawRowCheck18650 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18650 := by decide +kernel

theorem rowCheck18650 : row18650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18650 := by decide +kernel

theorem rowEval18650 (x : Key → ℝ) : Integer.Sparse.eval row18650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18650, Integer.Sparse.eval_collectBalanced, rawRowCheck18650]

theorem rawRowCheck18651 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18651 := by decide +kernel

theorem rowCheck18651 : row18651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18651 := by decide +kernel

theorem rowEval18651 (x : Key → ℝ) : Integer.Sparse.eval row18651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18651, Integer.Sparse.eval_collectBalanced, rawRowCheck18651]

theorem rawRowCheck18652 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18652 := by decide +kernel

theorem rowCheck18652 : row18652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18652 := by decide +kernel

theorem rowEval18652 (x : Key → ℝ) : Integer.Sparse.eval row18652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18652, Integer.Sparse.eval_collectBalanced, rawRowCheck18652]

theorem rawRowCheck18653 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18653 := by decide +kernel

theorem rowCheck18653 : row18653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18653 := by decide +kernel

theorem rowEval18653 (x : Key → ℝ) : Integer.Sparse.eval row18653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18653, Integer.Sparse.eval_collectBalanced, rawRowCheck18653]

theorem rawRowCheck18654 : GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18654 := by decide +kernel

theorem rowCheck18654 : row18654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18654 := by decide +kernel

theorem rowEval18654 (x : Key → ℝ) : Integer.Sparse.eval row18654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18654, Integer.Sparse.eval_collectBalanced, rawRowCheck18654]

theorem rawRowCheck18655 : GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18655 := by decide +kernel

theorem rowCheck18655 : row18655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18655 := by decide +kernel

theorem rowEval18655 (x : Key → ℝ) : Integer.Sparse.eval row18655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18655, Integer.Sparse.eval_collectBalanced, rawRowCheck18655]

theorem rawRowCheck18656 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18656 := by decide +kernel

theorem rowCheck18656 : row18656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18656 := by decide +kernel

theorem rowEval18656 (x : Key → ℝ) : Integer.Sparse.eval row18656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18656, Integer.Sparse.eval_collectBalanced, rawRowCheck18656]

theorem rawRowCheck18657 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18657 := by decide +kernel

theorem rowCheck18657 : row18657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18657 := by decide +kernel

theorem rowEval18657 (x : Key → ℝ) : Integer.Sparse.eval row18657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18657, Integer.Sparse.eval_collectBalanced, rawRowCheck18657]

theorem rawRowCheck18658 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18658 := by decide +kernel

theorem rowCheck18658 : row18658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18658 := by decide +kernel

theorem rowEval18658 (x : Key → ℝ) : Integer.Sparse.eval row18658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18658, Integer.Sparse.eval_collectBalanced, rawRowCheck18658]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18639 x
  · exact rowEval18640 x
  · exact rowEval18641 x
  · exact rowEval18642 x
  · exact rowEval18643 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18644 x
  · exact rowEval18645 x
  · exact rowEval18646 x
  · exact rowEval18647 x
  · exact rowEval18648 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18649 x
  · exact rowEval18650 x
  · exact rowEval18651 x
  · exact rowEval18652 x
  · exact rowEval18653 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block5.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form3.terms k).tag (GramFunctions.Block5.form3.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18654 x
  · exact rowEval18655 x
  · exact rowEval18656 x
  · exact rowEval18657 x
  · exact rowEval18658 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block5.form3.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form3 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18719 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18719 := by decide +kernel

theorem rowCheck18719 : row18719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18719 := by decide +kernel

theorem rowEval18719 (x : Key → ℝ) : Integer.Sparse.eval row18719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18719, Integer.Sparse.eval_collectBalanced, rawRowCheck18719]

theorem rawRowCheck18720 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18720 := by decide +kernel

theorem rowCheck18720 : row18720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18720 := by decide +kernel

theorem rowEval18720 (x : Key → ℝ) : Integer.Sparse.eval row18720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18720, Integer.Sparse.eval_collectBalanced, rawRowCheck18720]

theorem rawRowCheck18721 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18721 := by decide +kernel

theorem rowCheck18721 : row18721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18721 := by decide +kernel

theorem rowEval18721 (x : Key → ℝ) : Integer.Sparse.eval row18721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18721, Integer.Sparse.eval_collectBalanced, rawRowCheck18721]

theorem rawRowCheck18722 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18722 := by decide +kernel

theorem rowCheck18722 : row18722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18722 := by decide +kernel

theorem rowEval18722 (x : Key → ℝ) : Integer.Sparse.eval row18722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18722, Integer.Sparse.eval_collectBalanced, rawRowCheck18722]

theorem rawRowCheck18723 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18723 := by decide +kernel

theorem rowCheck18723 : row18723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18723 := by decide +kernel

theorem rowEval18723 (x : Key → ℝ) : Integer.Sparse.eval row18723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18723, Integer.Sparse.eval_collectBalanced, rawRowCheck18723]

theorem rawRowCheck18724 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18724 := by decide +kernel

theorem rowCheck18724 : row18724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18724 := by decide +kernel

theorem rowEval18724 (x : Key → ℝ) : Integer.Sparse.eval row18724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18724, Integer.Sparse.eval_collectBalanced, rawRowCheck18724]

theorem rawRowCheck18725 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18725 := by decide +kernel

theorem rowCheck18725 : row18725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18725 := by decide +kernel

theorem rowEval18725 (x : Key → ℝ) : Integer.Sparse.eval row18725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18725, Integer.Sparse.eval_collectBalanced, rawRowCheck18725]

theorem rawRowCheck18726 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3 = rawRow18726 := by decide +kernel

theorem rowCheck18726 : row18726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18726 := by decide +kernel

theorem rowEval18726 (x : Key → ℝ) : Integer.Sparse.eval row18726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18726, Integer.Sparse.eval_collectBalanced, rawRowCheck18726]

theorem rawRowCheck18727 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3 = rawRow18727 := by decide +kernel

theorem rowCheck18727 : row18727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18727 := by decide +kernel

theorem rowEval18727 (x : Key → ℝ) : Integer.Sparse.eval row18727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18727, Integer.Sparse.eval_collectBalanced, rawRowCheck18727]

theorem rawRowCheck18728 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3 = rawRow18728 := by decide +kernel

theorem rowCheck18728 : row18728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18728 := by decide +kernel

theorem rowEval18728 (x : Key → ℝ) : Integer.Sparse.eval row18728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18728, Integer.Sparse.eval_collectBalanced, rawRowCheck18728]

theorem rawRowCheck18729 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3 = rawRow18729 := by decide +kernel

theorem rowCheck18729 : row18729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18729 := by decide +kernel

theorem rowEval18729 (x : Key → ℝ) : Integer.Sparse.eval row18729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18729, Integer.Sparse.eval_collectBalanced, rawRowCheck18729]

theorem rawRowCheck18730 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3 = rawRow18730 := by decide +kernel

theorem rowCheck18730 : row18730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18730 := by decide +kernel

theorem rowEval18730 (x : Key → ℝ) : Integer.Sparse.eval row18730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18730, Integer.Sparse.eval_collectBalanced, rawRowCheck18730]

theorem rawRowCheck18731 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3 = rawRow18731 := by decide +kernel

theorem rowCheck18731 : row18731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18731 := by decide +kernel

theorem rowEval18731 (x : Key → ℝ) : Integer.Sparse.eval row18731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18731, Integer.Sparse.eval_collectBalanced, rawRowCheck18731]

theorem rawRowCheck18732 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18732 := by decide +kernel

theorem rowCheck18732 : row18732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18732 := by decide +kernel

theorem rowEval18732 (x : Key → ℝ) : Integer.Sparse.eval row18732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18732, Integer.Sparse.eval_collectBalanced, rawRowCheck18732]

theorem rawRowCheck18733 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18733 := by decide +kernel

theorem rowCheck18733 : row18733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18733 := by decide +kernel

theorem rowEval18733 (x : Key → ℝ) : Integer.Sparse.eval row18733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18733, Integer.Sparse.eval_collectBalanced, rawRowCheck18733]

theorem rawRowCheck18734 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18734 := by decide +kernel

theorem rowCheck18734 : row18734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18734 := by decide +kernel

theorem rowEval18734 (x : Key → ℝ) : Integer.Sparse.eval row18734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18734, Integer.Sparse.eval_collectBalanced, rawRowCheck18734]

theorem rawRowCheck18735 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18735 := by decide +kernel

theorem rowCheck18735 : row18735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18735 := by decide +kernel

theorem rowEval18735 (x : Key → ℝ) : Integer.Sparse.eval row18735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18735, Integer.Sparse.eval_collectBalanced, rawRowCheck18735]

theorem rawRowCheck18736 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18736 := by decide +kernel

theorem rowCheck18736 : row18736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18736 := by decide +kernel

theorem rowEval18736 (x : Key → ℝ) : Integer.Sparse.eval row18736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18736, Integer.Sparse.eval_collectBalanced, rawRowCheck18736]

theorem rawRowCheck18737 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18737 := by decide +kernel

theorem rowCheck18737 : row18737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18737 := by decide +kernel

theorem rowEval18737 (x : Key → ℝ) : Integer.Sparse.eval row18737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18737, Integer.Sparse.eval_collectBalanced, rawRowCheck18737]

theorem rawRowCheck18738 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18738 := by decide +kernel

theorem rowCheck18738 : row18738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18738 := by decide +kernel

theorem rowEval18738 (x : Key → ℝ) : Integer.Sparse.eval row18738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18738, Integer.Sparse.eval_collectBalanced, rawRowCheck18738]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18719 x
  · exact rowEval18720 x
  · exact rowEval18721 x
  · exact rowEval18722 x
  · exact rowEval18723 x
  · exact rowEval18724 x
  · exact rowEval18725 x
  · exact rowEval18726 x
  · exact rowEval18727 x
  · exact rowEval18728 x
  · exact rowEval18729 x
  · exact rowEval18730 x
  · exact rowEval18731 x
  · exact rowEval18732 x
  · exact rowEval18733 x
  · exact rowEval18734 x
  · exact rowEval18735 x
  · exact rowEval18736 x
  · exact rowEval18737 x
  · exact rowEval18738 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18849 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18849 := by decide +kernel

theorem rowCheck18849 : row18849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18849 := by decide +kernel

theorem rowEval18849 (x : Key → ℝ) : Integer.Sparse.eval row18849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18849, Integer.Sparse.eval_collectBalanced, rawRowCheck18849]

theorem rawRowCheck18850 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18850 := by decide +kernel

theorem rowCheck18850 : row18850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18850 := by decide +kernel

theorem rowEval18850 (x : Key → ℝ) : Integer.Sparse.eval row18850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18850, Integer.Sparse.eval_collectBalanced, rawRowCheck18850]

theorem rawRowCheck18851 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18851 := by decide +kernel

theorem rowCheck18851 : row18851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18851 := by decide +kernel

theorem rowEval18851 (x : Key → ℝ) : Integer.Sparse.eval row18851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18851, Integer.Sparse.eval_collectBalanced, rawRowCheck18851]

theorem rawRowCheck18852 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18852 := by decide +kernel

theorem rowCheck18852 : row18852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18852 := by decide +kernel

theorem rowEval18852 (x : Key → ℝ) : Integer.Sparse.eval row18852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18852, Integer.Sparse.eval_collectBalanced, rawRowCheck18852]

theorem rawRowCheck18853 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18853 := by decide +kernel

theorem rowCheck18853 : row18853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18853 := by decide +kernel

theorem rowEval18853 (x : Key → ℝ) : Integer.Sparse.eval row18853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18853, Integer.Sparse.eval_collectBalanced, rawRowCheck18853]

theorem rawRowCheck18854 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18854 := by decide +kernel

theorem rowCheck18854 : row18854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18854 := by decide +kernel

theorem rowEval18854 (x : Key → ℝ) : Integer.Sparse.eval row18854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18854, Integer.Sparse.eval_collectBalanced, rawRowCheck18854]

theorem rawRowCheck18855 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3 = rawRow18855 := by decide +kernel

theorem rowCheck18855 : row18855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18855 := by decide +kernel

theorem rowEval18855 (x : Key → ℝ) : Integer.Sparse.eval row18855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18855, Integer.Sparse.eval_collectBalanced, rawRowCheck18855]

theorem rawRowCheck18856 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3 = rawRow18856 := by decide +kernel

theorem rowCheck18856 : row18856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18856 := by decide +kernel

theorem rowEval18856 (x : Key → ℝ) : Integer.Sparse.eval row18856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18856, Integer.Sparse.eval_collectBalanced, rawRowCheck18856]

theorem rawRowCheck18857 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3 = rawRow18857 := by decide +kernel

theorem rowCheck18857 : row18857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18857 := by decide +kernel

theorem rowEval18857 (x : Key → ℝ) : Integer.Sparse.eval row18857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18857, Integer.Sparse.eval_collectBalanced, rawRowCheck18857]

theorem rawRowCheck18858 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3 = rawRow18858 := by decide +kernel

theorem rowCheck18858 : row18858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18858 := by decide +kernel

theorem rowEval18858 (x : Key → ℝ) : Integer.Sparse.eval row18858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18858, Integer.Sparse.eval_collectBalanced, rawRowCheck18858]

theorem rawRowCheck18859 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3 = rawRow18859 := by decide +kernel

theorem rowCheck18859 : row18859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18859 := by decide +kernel

theorem rowEval18859 (x : Key → ℝ) : Integer.Sparse.eval row18859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18859, Integer.Sparse.eval_collectBalanced, rawRowCheck18859]

theorem rawRowCheck18860 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3 = rawRow18860 := by decide +kernel

theorem rowCheck18860 : row18860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18860 := by decide +kernel

theorem rowEval18860 (x : Key → ℝ) : Integer.Sparse.eval row18860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18860, Integer.Sparse.eval_collectBalanced, rawRowCheck18860]

theorem rawRowCheck18861 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18861 := by decide +kernel

theorem rowCheck18861 : row18861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18861 := by decide +kernel

theorem rowEval18861 (x : Key → ℝ) : Integer.Sparse.eval row18861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18861, Integer.Sparse.eval_collectBalanced, rawRowCheck18861]

theorem rawRowCheck18862 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18862 := by decide +kernel

theorem rowCheck18862 : row18862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18862 := by decide +kernel

theorem rowEval18862 (x : Key → ℝ) : Integer.Sparse.eval row18862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18862, Integer.Sparse.eval_collectBalanced, rawRowCheck18862]

theorem rawRowCheck18863 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18863 := by decide +kernel

theorem rowCheck18863 : row18863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18863 := by decide +kernel

theorem rowEval18863 (x : Key → ℝ) : Integer.Sparse.eval row18863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18863, Integer.Sparse.eval_collectBalanced, rawRowCheck18863]

theorem rawRowCheck18864 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18864 := by decide +kernel

theorem rowCheck18864 : row18864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18864 := by decide +kernel

theorem rowEval18864 (x : Key → ℝ) : Integer.Sparse.eval row18864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18864, Integer.Sparse.eval_collectBalanced, rawRowCheck18864]

theorem rawRowCheck18865 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18865 := by decide +kernel

theorem rowCheck18865 : row18865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18865 := by decide +kernel

theorem rowEval18865 (x : Key → ℝ) : Integer.Sparse.eval row18865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18865, Integer.Sparse.eval_collectBalanced, rawRowCheck18865]

theorem rawRowCheck18866 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18866 := by decide +kernel

theorem rowCheck18866 : row18866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18866 := by decide +kernel

theorem rowEval18866 (x : Key → ℝ) : Integer.Sparse.eval row18866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18866, Integer.Sparse.eval_collectBalanced, rawRowCheck18866]

theorem rawRowCheck18867 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18867 := by decide +kernel

theorem rowCheck18867 : row18867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18867 := by decide +kernel

theorem rowEval18867 (x : Key → ℝ) : Integer.Sparse.eval row18867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18867, Integer.Sparse.eval_collectBalanced, rawRowCheck18867]

theorem rawRowCheck18868 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3 = rawRow18868 := by decide +kernel

theorem rowCheck18868 : row18868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18868 := by decide +kernel

theorem rowEval18868 (x : Key → ℝ) : Integer.Sparse.eval row18868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18868, Integer.Sparse.eval_collectBalanced, rawRowCheck18868]

theorem rawRowCheck18869 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3 = rawRow18869 := by decide +kernel

theorem rowCheck18869 : row18869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18869 := by decide +kernel

theorem rowEval18869 (x : Key → ℝ) : Integer.Sparse.eval row18869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18869, Integer.Sparse.eval_collectBalanced, rawRowCheck18869]

theorem rawRowCheck18870 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3 = rawRow18870 := by decide +kernel

theorem rowCheck18870 : row18870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18870 := by decide +kernel

theorem rowEval18870 (x : Key → ℝ) : Integer.Sparse.eval row18870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18870, Integer.Sparse.eval_collectBalanced, rawRowCheck18870]

theorem rawRowCheck18871 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3 = rawRow18871 := by decide +kernel

theorem rowCheck18871 : row18871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18871 := by decide +kernel

theorem rowEval18871 (x : Key → ℝ) : Integer.Sparse.eval row18871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18871, Integer.Sparse.eval_collectBalanced, rawRowCheck18871]

theorem rawRowCheck18872 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3 = rawRow18872 := by decide +kernel

theorem rowCheck18872 : row18872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18872 := by decide +kernel

theorem rowEval18872 (x : Key → ℝ) : Integer.Sparse.eval row18872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18872, Integer.Sparse.eval_collectBalanced, rawRowCheck18872]

theorem rawRowCheck18873 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3 = rawRow18873 := by decide +kernel

theorem rowCheck18873 : row18873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18873 := by decide +kernel

theorem rowEval18873 (x : Key → ℝ) : Integer.Sparse.eval row18873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18873, Integer.Sparse.eval_collectBalanced, rawRowCheck18873]

theorem rawRowCheck18874 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3 = rawRow18874 := by decide +kernel

theorem rowCheck18874 : row18874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18874 := by decide +kernel

theorem rowEval18874 (x : Key → ℝ) : Integer.Sparse.eval row18874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18874, Integer.Sparse.eval_collectBalanced, rawRowCheck18874]

theorem rawRowCheck18875 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3 = rawRow18875 := by decide +kernel

theorem rowCheck18875 : row18875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18875 := by decide +kernel

theorem rowEval18875 (x : Key → ℝ) : Integer.Sparse.eval row18875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18875, Integer.Sparse.eval_collectBalanced, rawRowCheck18875]

theorem rawRowCheck18876 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18876 := by decide +kernel

theorem rowCheck18876 : row18876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18876 := by decide +kernel

theorem rowEval18876 (x : Key → ℝ) : Integer.Sparse.eval row18876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18876, Integer.Sparse.eval_collectBalanced, rawRowCheck18876]

theorem rawRowCheck18877 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18877 := by decide +kernel

theorem rowCheck18877 : row18877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18877 := by decide +kernel

theorem rowEval18877 (x : Key → ℝ) : Integer.Sparse.eval row18877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18877, Integer.Sparse.eval_collectBalanced, rawRowCheck18877]

theorem rawRowCheck18878 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18878 := by decide +kernel

theorem rowCheck18878 : row18878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18878 := by decide +kernel

theorem rowEval18878 (x : Key → ℝ) : Integer.Sparse.eval row18878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18878, Integer.Sparse.eval_collectBalanced, rawRowCheck18878]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18849 x
  · exact rowEval18850 x
  · exact rowEval18851 x
  · exact rowEval18852 x
  · exact rowEval18853 x
  · exact rowEval18854 x
  · exact rowEval18855 x
  · exact rowEval18856 x
  · exact rowEval18857 x
  · exact rowEval18858 x
  · exact rowEval18859 x
  · exact rowEval18860 x
  · exact rowEval18861 x
  · exact rowEval18862 x
  · exact rowEval18863 x
  · exact rowEval18864 x
  · exact rowEval18865 x
  · exact rowEval18866 x
  · exact rowEval18867 x
  · exact rowEval18868 x
  · exact rowEval18869 x
  · exact rowEval18870 x
  · exact rowEval18871 x
  · exact rowEval18872 x
  · exact rowEval18873 x
  · exact rowEval18874 x
  · exact rowEval18875 x
  · exact rowEval18876 x
  · exact rowEval18877 x
  · exact rowEval18878 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18999 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form3 = rawRow18999 := by decide +kernel

theorem rowCheck18999 : row18999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18999 := by decide +kernel

theorem rowEval18999 (x : Key → ℝ) : Integer.Sparse.eval row18999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck18999, Integer.Sparse.eval_collectBalanced, rawRowCheck18999]

theorem rawRowCheck19000 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form3 = rawRow19000 := by decide +kernel

theorem rowCheck19000 : row19000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19000 := by decide +kernel

theorem rowEval19000 (x : Key → ℝ) : Integer.Sparse.eval row19000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19000, Integer.Sparse.eval_collectBalanced, rawRowCheck19000]

theorem rawRowCheck19001 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form3 = rawRow19001 := by decide +kernel

theorem rowCheck19001 : row19001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19001 := by decide +kernel

theorem rowEval19001 (x : Key → ℝ) : Integer.Sparse.eval row19001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19001, Integer.Sparse.eval_collectBalanced, rawRowCheck19001]

theorem rawRowCheck19002 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19002 := by decide +kernel

theorem rowCheck19002 : row19002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19002 := by decide +kernel

theorem rowEval19002 (x : Key → ℝ) : Integer.Sparse.eval row19002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19002, Integer.Sparse.eval_collectBalanced, rawRowCheck19002]

theorem rawRowCheck19003 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form3 = rawRow19003 := by decide +kernel

theorem rowCheck19003 : row19003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19003 := by decide +kernel

theorem rowEval19003 (x : Key → ℝ) : Integer.Sparse.eval row19003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19003, Integer.Sparse.eval_collectBalanced, rawRowCheck19003]

theorem rawRowCheck19004 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form3 = rawRow19004 := by decide +kernel

theorem rowCheck19004 : row19004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19004 := by decide +kernel

theorem rowEval19004 (x : Key → ℝ) : Integer.Sparse.eval row19004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19004, Integer.Sparse.eval_collectBalanced, rawRowCheck19004]

theorem rawRowCheck19005 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form3 = rawRow19005 := by decide +kernel

theorem rowCheck19005 : row19005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19005 := by decide +kernel

theorem rowEval19005 (x : Key → ℝ) : Integer.Sparse.eval row19005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19005, Integer.Sparse.eval_collectBalanced, rawRowCheck19005]

theorem rawRowCheck19006 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form3 = rawRow19006 := by decide +kernel

theorem rowCheck19006 : row19006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19006 := by decide +kernel

theorem rowEval19006 (x : Key → ℝ) : Integer.Sparse.eval row19006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19006, Integer.Sparse.eval_collectBalanced, rawRowCheck19006]

theorem rawRowCheck19007 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form3 = rawRow19007 := by decide +kernel

theorem rowCheck19007 : row19007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19007 := by decide +kernel

theorem rowEval19007 (x : Key → ℝ) : Integer.Sparse.eval row19007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19007, Integer.Sparse.eval_collectBalanced, rawRowCheck19007]

theorem rawRowCheck19008 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form3 = rawRow19008 := by decide +kernel

theorem rowCheck19008 : row19008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19008 := by decide +kernel

theorem rowEval19008 (x : Key → ℝ) : Integer.Sparse.eval row19008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19008, Integer.Sparse.eval_collectBalanced, rawRowCheck19008]

theorem rawRowCheck19009 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form3 = rawRow19009 := by decide +kernel

theorem rowCheck19009 : row19009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19009 := by decide +kernel

theorem rowEval19009 (x : Key → ℝ) : Integer.Sparse.eval row19009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19009, Integer.Sparse.eval_collectBalanced, rawRowCheck19009]

theorem rawRowCheck19010 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form3 = rawRow19010 := by decide +kernel

theorem rowCheck19010 : row19010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19010 := by decide +kernel

theorem rowEval19010 (x : Key → ℝ) : Integer.Sparse.eval row19010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19010, Integer.Sparse.eval_collectBalanced, rawRowCheck19010]

theorem rawRowCheck19011 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form3 = rawRow19011 := by decide +kernel

theorem rowCheck19011 : row19011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19011 := by decide +kernel

theorem rowEval19011 (x : Key → ℝ) : Integer.Sparse.eval row19011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19011, Integer.Sparse.eval_collectBalanced, rawRowCheck19011]

theorem rawRowCheck19012 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form3 = rawRow19012 := by decide +kernel

theorem rowCheck19012 : row19012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19012 := by decide +kernel

theorem rowEval19012 (x : Key → ℝ) : Integer.Sparse.eval row19012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19012, Integer.Sparse.eval_collectBalanced, rawRowCheck19012]

theorem rawRowCheck19013 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form3 = rawRow19013 := by decide +kernel

theorem rowCheck19013 : row19013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19013 := by decide +kernel

theorem rowEval19013 (x : Key → ℝ) : Integer.Sparse.eval row19013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19013, Integer.Sparse.eval_collectBalanced, rawRowCheck19013]

theorem rawRowCheck19014 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form3 = rawRow19014 := by decide +kernel

theorem rowCheck19014 : row19014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19014 := by decide +kernel

theorem rowEval19014 (x : Key → ℝ) : Integer.Sparse.eval row19014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19014, Integer.Sparse.eval_collectBalanced, rawRowCheck19014]

theorem rawRowCheck19015 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19015 := by decide +kernel

theorem rowCheck19015 : row19015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19015 := by decide +kernel

theorem rowEval19015 (x : Key → ℝ) : Integer.Sparse.eval row19015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19015, Integer.Sparse.eval_collectBalanced, rawRowCheck19015]

theorem rawRowCheck19016 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow19016 := by decide +kernel

theorem rowCheck19016 : row19016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19016 := by decide +kernel

theorem rowEval19016 (x : Key → ℝ) : Integer.Sparse.eval row19016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19016, Integer.Sparse.eval_collectBalanced, rawRowCheck19016]

theorem rawRowCheck19017 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow19017 := by decide +kernel

theorem rowCheck19017 : row19017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19017 := by decide +kernel

theorem rowEval19017 (x : Key → ℝ) : Integer.Sparse.eval row19017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19017, Integer.Sparse.eval_collectBalanced, rawRowCheck19017]

theorem rawRowCheck19018 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow19018 := by decide +kernel

theorem rowCheck19018 : row19018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19018 := by decide +kernel

theorem rowEval19018 (x : Key → ℝ) : Integer.Sparse.eval row19018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck19018, Integer.Sparse.eval_collectBalanced, rawRowCheck19018]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19139 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19139 := by decide +kernel

theorem rowCheck19139 : row19139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19139 := by decide +kernel

theorem rowEval19139 (x : Key → ℝ) : Integer.Sparse.eval row19139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19139, Integer.Sparse.eval_collectBalanced, rawRowCheck19139]

theorem rawRowCheck19140 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19140 := by decide +kernel

theorem rowCheck19140 : row19140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19140 := by decide +kernel

theorem rowEval19140 (x : Key → ℝ) : Integer.Sparse.eval row19140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19140, Integer.Sparse.eval_collectBalanced, rawRowCheck19140]

theorem rawRowCheck19141 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19141 := by decide +kernel

theorem rowCheck19141 : row19141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19141 := by decide +kernel

theorem rowEval19141 (x : Key → ℝ) : Integer.Sparse.eval row19141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19141, Integer.Sparse.eval_collectBalanced, rawRowCheck19141]

theorem rawRowCheck19142 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19142 := by decide +kernel

theorem rowCheck19142 : row19142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19142 := by decide +kernel

theorem rowEval19142 (x : Key → ℝ) : Integer.Sparse.eval row19142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19142, Integer.Sparse.eval_collectBalanced, rawRowCheck19142]

theorem rawRowCheck19143 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19143 := by decide +kernel

theorem rowCheck19143 : row19143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19143 := by decide +kernel

theorem rowEval19143 (x : Key → ℝ) : Integer.Sparse.eval row19143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19143, Integer.Sparse.eval_collectBalanced, rawRowCheck19143]

theorem rawRowCheck19144 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19144 := by decide +kernel

theorem rowCheck19144 : row19144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19144 := by decide +kernel

theorem rowEval19144 (x : Key → ℝ) : Integer.Sparse.eval row19144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19144, Integer.Sparse.eval_collectBalanced, rawRowCheck19144]

theorem rawRowCheck19145 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19145 := by decide +kernel

theorem rowCheck19145 : row19145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19145 := by decide +kernel

theorem rowEval19145 (x : Key → ℝ) : Integer.Sparse.eval row19145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19145, Integer.Sparse.eval_collectBalanced, rawRowCheck19145]

theorem rawRowCheck19146 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19146 := by decide +kernel

theorem rowCheck19146 : row19146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19146 := by decide +kernel

theorem rowEval19146 (x : Key → ℝ) : Integer.Sparse.eval row19146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19146, Integer.Sparse.eval_collectBalanced, rawRowCheck19146]

theorem rawRowCheck19147 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19147 := by decide +kernel

theorem rowCheck19147 : row19147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19147 := by decide +kernel

theorem rowEval19147 (x : Key → ℝ) : Integer.Sparse.eval row19147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19147, Integer.Sparse.eval_collectBalanced, rawRowCheck19147]

theorem rawRowCheck19148 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19148 := by decide +kernel

theorem rowCheck19148 : row19148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19148 := by decide +kernel

theorem rowEval19148 (x : Key → ℝ) : Integer.Sparse.eval row19148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19148, Integer.Sparse.eval_collectBalanced, rawRowCheck19148]

theorem rawRowCheck19149 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19149 := by decide +kernel

theorem rowCheck19149 : row19149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19149 := by decide +kernel

theorem rowEval19149 (x : Key → ℝ) : Integer.Sparse.eval row19149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19149, Integer.Sparse.eval_collectBalanced, rawRowCheck19149]

theorem rawRowCheck19150 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19150 := by decide +kernel

theorem rowCheck19150 : row19150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19150 := by decide +kernel

theorem rowEval19150 (x : Key → ℝ) : Integer.Sparse.eval row19150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19150, Integer.Sparse.eval_collectBalanced, rawRowCheck19150]

theorem rawRowCheck19151 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19151 := by decide +kernel

theorem rowCheck19151 : row19151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19151 := by decide +kernel

theorem rowEval19151 (x : Key → ℝ) : Integer.Sparse.eval row19151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19151, Integer.Sparse.eval_collectBalanced, rawRowCheck19151]

theorem rawRowCheck19152 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19152 := by decide +kernel

theorem rowCheck19152 : row19152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19152 := by decide +kernel

theorem rowEval19152 (x : Key → ℝ) : Integer.Sparse.eval row19152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19152, Integer.Sparse.eval_collectBalanced, rawRowCheck19152]

theorem rawRowCheck19153 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3 = rawRow19153 := by decide +kernel

theorem rowCheck19153 : row19153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19153 := by decide +kernel

theorem rowEval19153 (x : Key → ℝ) : Integer.Sparse.eval row19153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19153, Integer.Sparse.eval_collectBalanced, rawRowCheck19153]

theorem rawRowCheck19154 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3 = rawRow19154 := by decide +kernel

theorem rowCheck19154 : row19154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19154 := by decide +kernel

theorem rowEval19154 (x : Key → ℝ) : Integer.Sparse.eval row19154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19154, Integer.Sparse.eval_collectBalanced, rawRowCheck19154]

theorem rawRowCheck19155 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3 = rawRow19155 := by decide +kernel

theorem rowCheck19155 : row19155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19155 := by decide +kernel

theorem rowEval19155 (x : Key → ℝ) : Integer.Sparse.eval row19155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19155, Integer.Sparse.eval_collectBalanced, rawRowCheck19155]

theorem rawRowCheck19156 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3 = rawRow19156 := by decide +kernel

theorem rowCheck19156 : row19156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19156 := by decide +kernel

theorem rowEval19156 (x : Key → ℝ) : Integer.Sparse.eval row19156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19156, Integer.Sparse.eval_collectBalanced, rawRowCheck19156]

theorem rawRowCheck19157 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3 = rawRow19157 := by decide +kernel

theorem rowCheck19157 : row19157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19157 := by decide +kernel

theorem rowEval19157 (x : Key → ℝ) : Integer.Sparse.eval row19157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19157, Integer.Sparse.eval_collectBalanced, rawRowCheck19157]

theorem rawRowCheck19158 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3 = rawRow19158 := by decide +kernel

theorem rowCheck19158 : row19158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19158 := by decide +kernel

theorem rowEval19158 (x : Key → ℝ) : Integer.Sparse.eval row19158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19158, Integer.Sparse.eval_collectBalanced, rawRowCheck19158]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck6_3 : entry6_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_3 k)) := by decide +kernel

theorem rowsSound6_3 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18999 x
  · exact rowEval19000 x
  · exact rowEval19001 x
  · exact rowEval19002 x
  · exact rowEval19003 x
  · exact rowEval19004 x
  · exact rowEval19005 x
  · exact rowEval19006 x
  · exact rowEval19007 x
  · exact rowEval19008 x
  · exact rowEval19009 x
  · exact rowEval19010 x
  · exact rowEval19011 x
  · exact rowEval19012 x
  · exact rowEval19013 x
  · exact rowEval19014 x
  · exact rowEval19015 x
  · exact rowEval19016 x
  · exact rowEval19017 x
  · exact rowEval19018 x

theorem entryEval6_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_3 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck6_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19239 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19239 := by decide +kernel

theorem rowCheck19239 : row19239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19239 := by decide +kernel

theorem rowEval19239 (x : Key → ℝ) : Integer.Sparse.eval row19239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19239, Integer.Sparse.eval_collectBalanced, rawRowCheck19239]

theorem rawRowCheck19240 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19240 := by decide +kernel

theorem rowCheck19240 : row19240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19240 := by decide +kernel

theorem rowEval19240 (x : Key → ℝ) : Integer.Sparse.eval row19240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19240, Integer.Sparse.eval_collectBalanced, rawRowCheck19240]

theorem rawRowCheck19241 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19241 := by decide +kernel

theorem rowCheck19241 : row19241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19241 := by decide +kernel

theorem rowEval19241 (x : Key → ℝ) : Integer.Sparse.eval row19241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19241, Integer.Sparse.eval_collectBalanced, rawRowCheck19241]

theorem rawRowCheck19242 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19242 := by decide +kernel

theorem rowCheck19242 : row19242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19242 := by decide +kernel

theorem rowEval19242 (x : Key → ℝ) : Integer.Sparse.eval row19242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19242, Integer.Sparse.eval_collectBalanced, rawRowCheck19242]

theorem rawRowCheck19243 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19243 := by decide +kernel

theorem rowCheck19243 : row19243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19243 := by decide +kernel

theorem rowEval19243 (x : Key → ℝ) : Integer.Sparse.eval row19243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19243, Integer.Sparse.eval_collectBalanced, rawRowCheck19243]

theorem rawRowCheck19244 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19244 := by decide +kernel

theorem rowCheck19244 : row19244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19244 := by decide +kernel

theorem rowEval19244 (x : Key → ℝ) : Integer.Sparse.eval row19244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19244, Integer.Sparse.eval_collectBalanced, rawRowCheck19244]

theorem rawRowCheck19245 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19245 := by decide +kernel

theorem rowCheck19245 : row19245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19245 := by decide +kernel

theorem rowEval19245 (x : Key → ℝ) : Integer.Sparse.eval row19245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19245, Integer.Sparse.eval_collectBalanced, rawRowCheck19245]

theorem rawRowCheck19246 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19246 := by decide +kernel

theorem rowCheck19246 : row19246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19246 := by decide +kernel

theorem rowEval19246 (x : Key → ℝ) : Integer.Sparse.eval row19246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19246, Integer.Sparse.eval_collectBalanced, rawRowCheck19246]

theorem rawRowCheck19247 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19247 := by decide +kernel

theorem rowCheck19247 : row19247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19247 := by decide +kernel

theorem rowEval19247 (x : Key → ℝ) : Integer.Sparse.eval row19247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19247, Integer.Sparse.eval_collectBalanced, rawRowCheck19247]

theorem rawRowCheck19248 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19248 := by decide +kernel

theorem rowCheck19248 : row19248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19248 := by decide +kernel

theorem rowEval19248 (x : Key → ℝ) : Integer.Sparse.eval row19248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19248, Integer.Sparse.eval_collectBalanced, rawRowCheck19248]

theorem rawRowCheck19249 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19249 := by decide +kernel

theorem rowCheck19249 : row19249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19249 := by decide +kernel

theorem rowEval19249 (x : Key → ℝ) : Integer.Sparse.eval row19249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19249, Integer.Sparse.eval_collectBalanced, rawRowCheck19249]

theorem rawRowCheck19250 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19250 := by decide +kernel

theorem rowCheck19250 : row19250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19250 := by decide +kernel

theorem rowEval19250 (x : Key → ℝ) : Integer.Sparse.eval row19250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19250, Integer.Sparse.eval_collectBalanced, rawRowCheck19250]

theorem rawRowCheck19251 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19251 := by decide +kernel

theorem rowCheck19251 : row19251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19251 := by decide +kernel

theorem rowEval19251 (x : Key → ℝ) : Integer.Sparse.eval row19251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19251, Integer.Sparse.eval_collectBalanced, rawRowCheck19251]

theorem rawRowCheck19252 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19252 := by decide +kernel

theorem rowCheck19252 : row19252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19252 := by decide +kernel

theorem rowEval19252 (x : Key → ℝ) : Integer.Sparse.eval row19252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19252, Integer.Sparse.eval_collectBalanced, rawRowCheck19252]

theorem rawRowCheck19253 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19253 := by decide +kernel

theorem rowCheck19253 : row19253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19253 := by decide +kernel

theorem rowEval19253 (x : Key → ℝ) : Integer.Sparse.eval row19253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19253, Integer.Sparse.eval_collectBalanced, rawRowCheck19253]

theorem rawRowCheck19254 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19254 := by decide +kernel

theorem rowCheck19254 : row19254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19254 := by decide +kernel

theorem rowEval19254 (x : Key → ℝ) : Integer.Sparse.eval row19254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19254, Integer.Sparse.eval_collectBalanced, rawRowCheck19254]

theorem rawRowCheck19255 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19255 := by decide +kernel

theorem rowCheck19255 : row19255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19255 := by decide +kernel

theorem rowEval19255 (x : Key → ℝ) : Integer.Sparse.eval row19255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19255, Integer.Sparse.eval_collectBalanced, rawRowCheck19255]

theorem rawRowCheck19256 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19256 := by decide +kernel

theorem rowCheck19256 : row19256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19256 := by decide +kernel

theorem rowEval19256 (x : Key → ℝ) : Integer.Sparse.eval row19256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19256, Integer.Sparse.eval_collectBalanced, rawRowCheck19256]

theorem rawRowCheck19257 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19257 := by decide +kernel

theorem rowCheck19257 : row19257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19257 := by decide +kernel

theorem rowEval19257 (x : Key → ℝ) : Integer.Sparse.eval row19257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19257, Integer.Sparse.eval_collectBalanced, rawRowCheck19257]

theorem rawRowCheck19258 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19258 := by decide +kernel

theorem rowCheck19258 : row19258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19258 := by decide +kernel

theorem rowEval19258 (x : Key → ℝ) : Integer.Sparse.eval row19258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19258, Integer.Sparse.eval_collectBalanced, rawRowCheck19258]

theorem rawRowCheck19259 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19259 := by decide +kernel

theorem rowCheck19259 : row19259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19259 := by decide +kernel

theorem rowEval19259 (x : Key → ℝ) : Integer.Sparse.eval row19259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19259, Integer.Sparse.eval_collectBalanced, rawRowCheck19259]

theorem rawRowCheck19260 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19260 := by decide +kernel

theorem rowCheck19260 : row19260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19260 := by decide +kernel

theorem rowEval19260 (x : Key → ℝ) : Integer.Sparse.eval row19260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19260, Integer.Sparse.eval_collectBalanced, rawRowCheck19260]

theorem rawRowCheck19261 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19261 := by decide +kernel

theorem rowCheck19261 : row19261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19261 := by decide +kernel

theorem rowEval19261 (x : Key → ℝ) : Integer.Sparse.eval row19261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19261, Integer.Sparse.eval_collectBalanced, rawRowCheck19261]

theorem rawRowCheck19262 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19262 := by decide +kernel

theorem rowCheck19262 : row19262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19262 := by decide +kernel

theorem rowEval19262 (x : Key → ℝ) : Integer.Sparse.eval row19262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19262, Integer.Sparse.eval_collectBalanced, rawRowCheck19262]

theorem rawRowCheck19263 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19263 := by decide +kernel

theorem rowCheck19263 : row19263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19263 := by decide +kernel

theorem rowEval19263 (x : Key → ℝ) : Integer.Sparse.eval row19263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19263, Integer.Sparse.eval_collectBalanced, rawRowCheck19263]

theorem rawRowCheck19264 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19264 := by decide +kernel

theorem rowCheck19264 : row19264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19264 := by decide +kernel

theorem rowEval19264 (x : Key → ℝ) : Integer.Sparse.eval row19264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19264, Integer.Sparse.eval_collectBalanced, rawRowCheck19264]

theorem rawRowCheck19265 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19265 := by decide +kernel

theorem rowCheck19265 : row19265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19265 := by decide +kernel

theorem rowEval19265 (x : Key → ℝ) : Integer.Sparse.eval row19265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19265, Integer.Sparse.eval_collectBalanced, rawRowCheck19265]

theorem rawRowCheck19266 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19266 := by decide +kernel

theorem rowCheck19266 : row19266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19266 := by decide +kernel

theorem rowEval19266 (x : Key → ℝ) : Integer.Sparse.eval row19266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19266, Integer.Sparse.eval_collectBalanced, rawRowCheck19266]

theorem rawRowCheck19267 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19267 := by decide +kernel

theorem rowCheck19267 : row19267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19267 := by decide +kernel

theorem rowEval19267 (x : Key → ℝ) : Integer.Sparse.eval row19267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19267, Integer.Sparse.eval_collectBalanced, rawRowCheck19267]

theorem rawRowCheck19268 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19268 := by decide +kernel

theorem rowCheck19268 : row19268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19268 := by decide +kernel

theorem rowEval19268 (x : Key → ℝ) : Integer.Sparse.eval row19268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19268, Integer.Sparse.eval_collectBalanced, rawRowCheck19268]

theorem rawRowCheck19269 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19269 := by decide +kernel

theorem rowCheck19269 : row19269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19269 := by decide +kernel

theorem rowEval19269 (x : Key → ℝ) : Integer.Sparse.eval row19269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19269, Integer.Sparse.eval_collectBalanced, rawRowCheck19269]

theorem rawRowCheck19270 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19270 := by decide +kernel

theorem rowCheck19270 : row19270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19270 := by decide +kernel

theorem rowEval19270 (x : Key → ℝ) : Integer.Sparse.eval row19270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19270, Integer.Sparse.eval_collectBalanced, rawRowCheck19270]

theorem rawRowCheck19271 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19271 := by decide +kernel

theorem rowCheck19271 : row19271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19271 := by decide +kernel

theorem rowEval19271 (x : Key → ℝ) : Integer.Sparse.eval row19271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19271, Integer.Sparse.eval_collectBalanced, rawRowCheck19271]

theorem rawRowCheck19272 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19272 := by decide +kernel

theorem rowCheck19272 : row19272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19272 := by decide +kernel

theorem rowEval19272 (x : Key → ℝ) : Integer.Sparse.eval row19272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19272, Integer.Sparse.eval_collectBalanced, rawRowCheck19272]

theorem rawRowCheck19273 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19273 := by decide +kernel

theorem rowCheck19273 : row19273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19273 := by decide +kernel

theorem rowEval19273 (x : Key → ℝ) : Integer.Sparse.eval row19273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19273, Integer.Sparse.eval_collectBalanced, rawRowCheck19273]

theorem rawRowCheck19274 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19274 := by decide +kernel

theorem rowCheck19274 : row19274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19274 := by decide +kernel

theorem rowEval19274 (x : Key → ℝ) : Integer.Sparse.eval row19274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19274, Integer.Sparse.eval_collectBalanced, rawRowCheck19274]

theorem rawRowCheck19275 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19275 := by decide +kernel

theorem rowCheck19275 : row19275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19275 := by decide +kernel

theorem rowEval19275 (x : Key → ℝ) : Integer.Sparse.eval row19275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19275, Integer.Sparse.eval_collectBalanced, rawRowCheck19275]

theorem rawRowCheck19276 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19276 := by decide +kernel

theorem rowCheck19276 : row19276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19276 := by decide +kernel

theorem rowEval19276 (x : Key → ℝ) : Integer.Sparse.eval row19276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19276, Integer.Sparse.eval_collectBalanced, rawRowCheck19276]

theorem rawRowCheck19277 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19277 := by decide +kernel

theorem rowCheck19277 : row19277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19277 := by decide +kernel

theorem rowEval19277 (x : Key → ℝ) : Integer.Sparse.eval row19277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19277, Integer.Sparse.eval_collectBalanced, rawRowCheck19277]

theorem rawRowCheck19278 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19278 := by decide +kernel

theorem rowCheck19278 : row19278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19278 := by decide +kernel

theorem rowEval19278 (x : Key → ℝ) : Integer.Sparse.eval row19278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19278, Integer.Sparse.eval_collectBalanced, rawRowCheck19278]

theorem rawRowCheck19279 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19279 := by decide +kernel

theorem rowCheck19279 : row19279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19279 := by decide +kernel

theorem rowEval19279 (x : Key → ℝ) : Integer.Sparse.eval row19279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19279, Integer.Sparse.eval_collectBalanced, rawRowCheck19279]

theorem rawRowCheck19280 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19280 := by decide +kernel

theorem rowCheck19280 : row19280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19280 := by decide +kernel

theorem rowEval19280 (x : Key → ℝ) : Integer.Sparse.eval row19280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19280, Integer.Sparse.eval_collectBalanced, rawRowCheck19280]

theorem rawRowCheck19281 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19281 := by decide +kernel

theorem rowCheck19281 : row19281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19281 := by decide +kernel

theorem rowEval19281 (x : Key → ℝ) : Integer.Sparse.eval row19281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19281, Integer.Sparse.eval_collectBalanced, rawRowCheck19281]

theorem rawRowCheck19282 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19282 := by decide +kernel

theorem rowCheck19282 : row19282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19282 := by decide +kernel

theorem rowEval19282 (x : Key → ℝ) : Integer.Sparse.eval row19282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19282, Integer.Sparse.eval_collectBalanced, rawRowCheck19282]

theorem rawRowCheck19283 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19283 := by decide +kernel

theorem rowCheck19283 : row19283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19283 := by decide +kernel

theorem rowEval19283 (x : Key → ℝ) : Integer.Sparse.eval row19283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19283, Integer.Sparse.eval_collectBalanced, rawRowCheck19283]

theorem rawRowCheck19314 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19314 := by decide +kernel

theorem rowCheck19314 : row19314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19314 := by decide +kernel

theorem rowEval19314 (x : Key → ℝ) : Integer.Sparse.eval row19314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19314, Integer.Sparse.eval_collectBalanced, rawRowCheck19314]

theorem rawRowCheck19315 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19315 := by decide +kernel

theorem rowCheck19315 : row19315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19315 := by decide +kernel

theorem rowEval19315 (x : Key → ℝ) : Integer.Sparse.eval row19315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19315, Integer.Sparse.eval_collectBalanced, rawRowCheck19315]

theorem rawRowCheck19316 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19316 := by decide +kernel

theorem rowCheck19316 : row19316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19316 := by decide +kernel

theorem rowEval19316 (x : Key → ℝ) : Integer.Sparse.eval row19316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19316, Integer.Sparse.eval_collectBalanced, rawRowCheck19316]

theorem rawRowCheck19317 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19317 := by decide +kernel

theorem rowCheck19317 : row19317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19317 := by decide +kernel

theorem rowEval19317 (x : Key → ℝ) : Integer.Sparse.eval row19317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19317, Integer.Sparse.eval_collectBalanced, rawRowCheck19317]

theorem rawRowCheck19318 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19318 := by decide +kernel

theorem rowCheck19318 : row19318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19318 := by decide +kernel

theorem rowEval19318 (x : Key → ℝ) : Integer.Sparse.eval row19318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19318, Integer.Sparse.eval_collectBalanced, rawRowCheck19318]

theorem rawRowCheck19319 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19319 := by decide +kernel

theorem rowCheck19319 : row19319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19319 := by decide +kernel

theorem rowEval19319 (x : Key → ℝ) : Integer.Sparse.eval row19319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19319, Integer.Sparse.eval_collectBalanced, rawRowCheck19319]

theorem rawRowCheck19320 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19320 := by decide +kernel

theorem rowCheck19320 : row19320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19320 := by decide +kernel

theorem rowEval19320 (x : Key → ℝ) : Integer.Sparse.eval row19320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19320, Integer.Sparse.eval_collectBalanced, rawRowCheck19320]

theorem rawRowCheck19321 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19321 := by decide +kernel

theorem rowCheck19321 : row19321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19321 := by decide +kernel

theorem rowEval19321 (x : Key → ℝ) : Integer.Sparse.eval row19321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19321, Integer.Sparse.eval_collectBalanced, rawRowCheck19321]

theorem rawRowCheck19322 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19322 := by decide +kernel

theorem rowCheck19322 : row19322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19322 := by decide +kernel

theorem rowEval19322 (x : Key → ℝ) : Integer.Sparse.eval row19322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19322, Integer.Sparse.eval_collectBalanced, rawRowCheck19322]

theorem rawRowCheck19323 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3 = rawRow19323 := by decide +kernel

theorem rowCheck19323 : row19323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19323 := by decide +kernel

theorem rowEval19323 (x : Key → ℝ) : Integer.Sparse.eval row19323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19323, Integer.Sparse.eval_collectBalanced, rawRowCheck19323]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19139 x
  · exact rowEval19140 x
  · exact rowEval19141 x
  · exact rowEval19142 x
  · exact rowEval19143 x
  · exact rowEval19144 x
  · exact rowEval19145 x
  · exact rowEval19146 x
  · exact rowEval19147 x
  · exact rowEval19148 x
  · exact rowEval19149 x
  · exact rowEval19150 x
  · exact rowEval19151 x
  · exact rowEval19152 x
  · exact rowEval19153 x
  · exact rowEval19154 x
  · exact rowEval19155 x
  · exact rowEval19156 x
  · exact rowEval19157 x
  · exact rowEval19158 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19239 x
  · exact rowEval19240 x
  · exact rowEval19241 x
  · exact rowEval19242 x
  · exact rowEval19243 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19244 x
  · exact rowEval19245 x
  · exact rowEval19246 x
  · exact rowEval19247 x
  · exact rowEval19248 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval19249 x
  · exact rowEval19250 x
  · exact rowEval19251 x
  · exact rowEval19252 x
  · exact rowEval19253 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19254 x
  · exact rowEval19255 x
  · exact rowEval19256 x
  · exact rowEval19257 x
  · exact rowEval19258 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19259 x
  · exact rowEval19260 x
  · exact rowEval19261 x
  · exact rowEval19262 x
  · exact rowEval19263 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19264 x
  · exact rowEval19265 x
  · exact rowEval19266 x
  · exact rowEval19267 x
  · exact rowEval19268 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19269 x
  · exact rowEval19270 x
  · exact rowEval19271 x
  · exact rowEval19272 x
  · exact rowEval19273 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval19274 x
  · exact rowEval19275 x
  · exact rowEval19276 x
  · exact rowEval19277 x
  · exact rowEval19278 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19279 x
  · exact rowEval19280 x
  · exact rowEval19281 x
  · exact rowEval19282 x
  · exact rowEval19283 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval19314 x
  · exact rowEval19315 x
  · exact rowEval19316 x
  · exact rowEval19317 x
  · exact rowEval19318 x
  · exact rowEval19319 x
  · exact rowEval19320 x
  · exact rowEval19321 x
  · exact rowEval19322 x
  · exact rowEval19323 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval19364 x
  · exact rowEval19365 x
  · exact rowEval19366 x
  · exact rowEval19367 x
  · exact rowEval19368 x
  · exact rowEval19369 x
  · exact rowEval19370 x
  · exact rowEval19371 x
  · exact rowEval19372 x
  · exact rowEval19373 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

theorem entryEvalRow3 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 3).mixedGram (GramFunctions.Block5.forms j) B := by
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
  · exact (entryEval9_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_3 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEvalRow8 (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 8 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 8).mixedGram (GramFunctions.Block5.forms j) B := by
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
  · exact (entryEval9_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_8 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEval (i j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms i).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases i
  · exact entryEvalRow0_e j B hB
  · exact entryEvalRow1_e j B hB
  · exact entryEvalRow2_e j B hB
  · exact entryEvalRow3 j B hB
  · exact entryEvalRow4_e j B hB
  · exact entryEvalRow5_e j B hB
  · exact entryEvalRow6_e j B hB
  · exact entryEvalRow7_e j B hB
  · exact entryEvalRow8 j B hB
  · exact entryEvalRow9_e j B hB
  · exact entryEvalRow10_e j B hB
  · exact entryEvalRow11_e j B hB

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block5

theorem indexed_entry_eval_e_oai (i j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
      (GramFunctions.Block5.forms i).mixedGram (GramFunctions.Block5.forms j) B := by
  have he := Integer.Sparse.eval_reindex key (entries i j) (GramNormalization.eval B)
  rw [entries_reindex] at he
  exact he.symm.trans (GramEntries.Block5.entryEval i j B hB)

end MUB6.Certificate.GramAssembly.Block5

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e_oai
