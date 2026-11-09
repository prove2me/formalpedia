-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:40:53.146246+00:00
-- url     : https://prove2.me/submissions/8ee02257-6c05-47c6-82f1-83c043cecc2b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_17_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck3734 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3734 := by decide +kernel

theorem rowCheck3734 : row3734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3734 := by decide +kernel

theorem rowEval3734 (x : Key → ℝ) : Integer.Sparse.eval row3734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3734, Integer.Sparse.eval_collectBalanced, rawRowCheck3734]

theorem rawRowCheck3735 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3735 := by decide +kernel

theorem rowCheck3735 : row3735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3735 := by decide +kernel

theorem rowEval3735 (x : Key → ℝ) : Integer.Sparse.eval row3735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3735, Integer.Sparse.eval_collectBalanced, rawRowCheck3735]

theorem rawRowCheck3736 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3736 := by decide +kernel

theorem rowCheck3736 : row3736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3736 := by decide +kernel

theorem rowEval3736 (x : Key → ℝ) : Integer.Sparse.eval row3736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3736, Integer.Sparse.eval_collectBalanced, rawRowCheck3736]

theorem rawRowCheck3737 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3737 := by decide +kernel

theorem rowCheck3737 : row3737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3737 := by decide +kernel

theorem rowEval3737 (x : Key → ℝ) : Integer.Sparse.eval row3737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3737, Integer.Sparse.eval_collectBalanced, rawRowCheck3737]

theorem rawRowCheck3738 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3738 := by decide +kernel

theorem rowCheck3738 : row3738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3738 := by decide +kernel

theorem rowEval3738 (x : Key → ℝ) : Integer.Sparse.eval row3738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3738, Integer.Sparse.eval_collectBalanced, rawRowCheck3738]

theorem rawRowCheck3739 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3739 := by decide +kernel

theorem rowCheck3739 : row3739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3739 := by decide +kernel

theorem rowEval3739 (x : Key → ℝ) : Integer.Sparse.eval row3739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3739, Integer.Sparse.eval_collectBalanced, rawRowCheck3739]

theorem rawRowCheck3740 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3740 := by decide +kernel

theorem rowCheck3740 : row3740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3740 := by decide +kernel

theorem rowEval3740 (x : Key → ℝ) : Integer.Sparse.eval row3740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3740, Integer.Sparse.eval_collectBalanced, rawRowCheck3740]

theorem rawRowCheck3741 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3741 := by decide +kernel

theorem rowCheck3741 : row3741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3741 := by decide +kernel

theorem rowEval3741 (x : Key → ℝ) : Integer.Sparse.eval row3741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3741, Integer.Sparse.eval_collectBalanced, rawRowCheck3741]

theorem rawRowCheck3742 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3742 := by decide +kernel

theorem rowCheck3742 : row3742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3742 := by decide +kernel

theorem rowEval3742 (x : Key → ℝ) : Integer.Sparse.eval row3742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3742, Integer.Sparse.eval_collectBalanced, rawRowCheck3742]

theorem rawRowCheck3743 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1 = rawRow3743 := by decide +kernel

theorem rowCheck3743 : row3743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3743 := by decide +kernel

theorem rowEval3743 (x : Key → ℝ) : Integer.Sparse.eval row3743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3743, Integer.Sparse.eval_collectBalanced, rawRowCheck3743]

theorem rawRowCheck3744 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1 = rawRow3744 := by decide +kernel

theorem rowCheck3744 : row3744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3744 := by decide +kernel

theorem rowEval3744 (x : Key → ℝ) : Integer.Sparse.eval row3744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3744, Integer.Sparse.eval_collectBalanced, rawRowCheck3744]

theorem rawRowCheck3745 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1 = rawRow3745 := by decide +kernel

theorem rowCheck3745 : row3745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3745 := by decide +kernel

theorem rowEval3745 (x : Key → ℝ) : Integer.Sparse.eval row3745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3745, Integer.Sparse.eval_collectBalanced, rawRowCheck3745]

theorem rawRowCheck3746 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1 = rawRow3746 := by decide +kernel

theorem rowCheck3746 : row3746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3746 := by decide +kernel

theorem rowEval3746 (x : Key → ℝ) : Integer.Sparse.eval row3746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3746, Integer.Sparse.eval_collectBalanced, rawRowCheck3746]

theorem rawRowCheck3747 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1 = rawRow3747 := by decide +kernel

theorem rowCheck3747 : row3747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3747 := by decide +kernel

theorem rowEval3747 (x : Key → ℝ) : Integer.Sparse.eval row3747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3747, Integer.Sparse.eval_collectBalanced, rawRowCheck3747]

theorem rawRowCheck3748 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1 = rawRow3748 := by decide +kernel

theorem rowCheck3748 : row3748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3748 := by decide +kernel

theorem rowEval3748 (x : Key → ℝ) : Integer.Sparse.eval row3748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3748, Integer.Sparse.eval_collectBalanced, rawRowCheck3748]

theorem rawRowCheck3749 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3749 := by decide +kernel

theorem rowCheck3749 : row3749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3749 := by decide +kernel

theorem rowEval3749 (x : Key → ℝ) : Integer.Sparse.eval row3749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3749, Integer.Sparse.eval_collectBalanced, rawRowCheck3749]

theorem rawRowCheck3750 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3750 := by decide +kernel

theorem rowCheck3750 : row3750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3750 := by decide +kernel

theorem rowEval3750 (x : Key → ℝ) : Integer.Sparse.eval row3750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3750, Integer.Sparse.eval_collectBalanced, rawRowCheck3750]

theorem rawRowCheck3751 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3751 := by decide +kernel

theorem rowCheck3751 : row3751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3751 := by decide +kernel

theorem rowEval3751 (x : Key → ℝ) : Integer.Sparse.eval row3751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3751, Integer.Sparse.eval_collectBalanced, rawRowCheck3751]

theorem rawRowCheck3752 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3752 := by decide +kernel

theorem rowCheck3752 : row3752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3752 := by decide +kernel

theorem rowEval3752 (x : Key → ℝ) : Integer.Sparse.eval row3752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3752, Integer.Sparse.eval_collectBalanced, rawRowCheck3752]

theorem rawRowCheck3753 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3753 := by decide +kernel

theorem rowCheck3753 : row3753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3753 := by decide +kernel

theorem rowEval3753 (x : Key → ℝ) : Integer.Sparse.eval row3753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3753, Integer.Sparse.eval_collectBalanced, rawRowCheck3753]

theorem rawRowCheck3754 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3754 := by decide +kernel

theorem rowCheck3754 : row3754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3754 := by decide +kernel

theorem rowEval3754 (x : Key → ℝ) : Integer.Sparse.eval row3754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3754, Integer.Sparse.eval_collectBalanced, rawRowCheck3754]

theorem rawRowCheck3755 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow3755 := by decide +kernel

theorem rowCheck3755 : row3755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3755 := by decide +kernel

theorem rowEval3755 (x : Key → ℝ) : Integer.Sparse.eval row3755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3755, Integer.Sparse.eval_collectBalanced, rawRowCheck3755]

theorem rawRowCheck3756 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow3756 := by decide +kernel

theorem rowCheck3756 : row3756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3756 := by decide +kernel

theorem rowEval3756 (x : Key → ℝ) : Integer.Sparse.eval row3756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3756, Integer.Sparse.eval_collectBalanced, rawRowCheck3756]

theorem rawRowCheck3757 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow3757 := by decide +kernel

theorem rowCheck3757 : row3757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3757 := by decide +kernel

theorem rowEval3757 (x : Key → ℝ) : Integer.Sparse.eval row3757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3757, Integer.Sparse.eval_collectBalanced, rawRowCheck3757]

theorem rawRowCheck3758 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow3758 := by decide +kernel

theorem rowCheck3758 : row3758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3758 := by decide +kernel

theorem rowEval3758 (x : Key → ℝ) : Integer.Sparse.eval row3758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3758, Integer.Sparse.eval_collectBalanced, rawRowCheck3758]

theorem rawRowCheck3759 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow3759 := by decide +kernel

theorem rowCheck3759 : row3759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3759 := by decide +kernel

theorem rowEval3759 (x : Key → ℝ) : Integer.Sparse.eval row3759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3759, Integer.Sparse.eval_collectBalanced, rawRowCheck3759]

theorem rawRowCheck3760 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow3760 := by decide +kernel

theorem rowCheck3760 : row3760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3760 := by decide +kernel

theorem rowEval3760 (x : Key → ℝ) : Integer.Sparse.eval row3760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck3760, Integer.Sparse.eval_collectBalanced, rawRowCheck3760]

theorem rawRowCheck3761 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow3761 := by decide +kernel

theorem rowCheck3761 : row3761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3761 := by decide +kernel

theorem rowEval3761 (x : Key → ℝ) : Integer.Sparse.eval row3761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3761, Integer.Sparse.eval_collectBalanced, rawRowCheck3761]

theorem rawRowCheck3762 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow3762 := by decide +kernel

theorem rowCheck3762 : row3762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3762 := by decide +kernel

theorem rowEval3762 (x : Key → ℝ) : Integer.Sparse.eval row3762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck3762, Integer.Sparse.eval_collectBalanced, rawRowCheck3762]

theorem rawRowCheck3763 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow3763 := by decide +kernel

theorem rowCheck3763 : row3763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3763 := by decide +kernel

theorem rowEval3763 (x : Key → ℝ) : Integer.Sparse.eval row3763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck3763, Integer.Sparse.eval_collectBalanced, rawRowCheck3763]

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

theorem rawRowCheck3794 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3794 := by decide +kernel

theorem rowCheck3794 : row3794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3794 := by decide +kernel

theorem rowEval3794 (x : Key → ℝ) : Integer.Sparse.eval row3794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3794, Integer.Sparse.eval_collectBalanced, rawRowCheck3794]

theorem rawRowCheck3795 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3795 := by decide +kernel

theorem rowCheck3795 : row3795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3795 := by decide +kernel

theorem rowEval3795 (x : Key → ℝ) : Integer.Sparse.eval row3795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3795, Integer.Sparse.eval_collectBalanced, rawRowCheck3795]

theorem rawRowCheck3796 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3796 := by decide +kernel

theorem rowCheck3796 : row3796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3796 := by decide +kernel

theorem rowEval3796 (x : Key → ℝ) : Integer.Sparse.eval row3796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3796, Integer.Sparse.eval_collectBalanced, rawRowCheck3796]

theorem rawRowCheck3797 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3797 := by decide +kernel

theorem rowCheck3797 : row3797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3797 := by decide +kernel

theorem rowEval3797 (x : Key → ℝ) : Integer.Sparse.eval row3797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3797, Integer.Sparse.eval_collectBalanced, rawRowCheck3797]

theorem rawRowCheck3798 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3798 := by decide +kernel

theorem rowCheck3798 : row3798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3798 := by decide +kernel

theorem rowEval3798 (x : Key → ℝ) : Integer.Sparse.eval row3798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3798, Integer.Sparse.eval_collectBalanced, rawRowCheck3798]

theorem rawRowCheck3799 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3799 := by decide +kernel

theorem rowCheck3799 : row3799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3799 := by decide +kernel

theorem rowEval3799 (x : Key → ℝ) : Integer.Sparse.eval row3799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3799, Integer.Sparse.eval_collectBalanced, rawRowCheck3799]

theorem rawRowCheck3800 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3800 := by decide +kernel

theorem rowCheck3800 : row3800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3800 := by decide +kernel

theorem rowEval3800 (x : Key → ℝ) : Integer.Sparse.eval row3800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3800, Integer.Sparse.eval_collectBalanced, rawRowCheck3800]

theorem rawRowCheck3801 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3801 := by decide +kernel

theorem rowCheck3801 : row3801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3801 := by decide +kernel

theorem rowEval3801 (x : Key → ℝ) : Integer.Sparse.eval row3801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3801, Integer.Sparse.eval_collectBalanced, rawRowCheck3801]

theorem rawRowCheck3802 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3802 := by decide +kernel

theorem rowCheck3802 : row3802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3802 := by decide +kernel

theorem rowEval3802 (x : Key → ℝ) : Integer.Sparse.eval row3802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3802, Integer.Sparse.eval_collectBalanced, rawRowCheck3802]

theorem rawRowCheck3803 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3 = rawRow3803 := by decide +kernel

theorem rowCheck3803 : row3803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3803 := by decide +kernel

theorem rowEval3803 (x : Key → ℝ) : Integer.Sparse.eval row3803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3803, Integer.Sparse.eval_collectBalanced, rawRowCheck3803]

theorem rawRowCheck3804 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3 = rawRow3804 := by decide +kernel

theorem rowCheck3804 : row3804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3804 := by decide +kernel

theorem rowEval3804 (x : Key → ℝ) : Integer.Sparse.eval row3804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3804, Integer.Sparse.eval_collectBalanced, rawRowCheck3804]

theorem rawRowCheck3805 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3 = rawRow3805 := by decide +kernel

theorem rowCheck3805 : row3805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3805 := by decide +kernel

theorem rowEval3805 (x : Key → ℝ) : Integer.Sparse.eval row3805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3805, Integer.Sparse.eval_collectBalanced, rawRowCheck3805]

theorem rawRowCheck3806 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3 = rawRow3806 := by decide +kernel

theorem rowCheck3806 : row3806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3806 := by decide +kernel

theorem rowEval3806 (x : Key → ℝ) : Integer.Sparse.eval row3806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3806, Integer.Sparse.eval_collectBalanced, rawRowCheck3806]

theorem rawRowCheck3807 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3 = rawRow3807 := by decide +kernel

theorem rowCheck3807 : row3807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3807 := by decide +kernel

theorem rowEval3807 (x : Key → ℝ) : Integer.Sparse.eval row3807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3807, Integer.Sparse.eval_collectBalanced, rawRowCheck3807]

theorem rawRowCheck3808 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3 = rawRow3808 := by decide +kernel

theorem rowCheck3808 : row3808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3808 := by decide +kernel

theorem rowEval3808 (x : Key → ℝ) : Integer.Sparse.eval row3808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3808, Integer.Sparse.eval_collectBalanced, rawRowCheck3808]

theorem rawRowCheck3809 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3809 := by decide +kernel

theorem rowCheck3809 : row3809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3809 := by decide +kernel

theorem rowEval3809 (x : Key → ℝ) : Integer.Sparse.eval row3809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3809, Integer.Sparse.eval_collectBalanced, rawRowCheck3809]

theorem rawRowCheck3810 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3810 := by decide +kernel

theorem rowCheck3810 : row3810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3810 := by decide +kernel

theorem rowEval3810 (x : Key → ℝ) : Integer.Sparse.eval row3810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3810, Integer.Sparse.eval_collectBalanced, rawRowCheck3810]

theorem rawRowCheck3811 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3811 := by decide +kernel

theorem rowCheck3811 : row3811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3811 := by decide +kernel

theorem rowEval3811 (x : Key → ℝ) : Integer.Sparse.eval row3811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3811, Integer.Sparse.eval_collectBalanced, rawRowCheck3811]

theorem rawRowCheck3812 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3812 := by decide +kernel

theorem rowCheck3812 : row3812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3812 := by decide +kernel

theorem rowEval3812 (x : Key → ℝ) : Integer.Sparse.eval row3812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3812, Integer.Sparse.eval_collectBalanced, rawRowCheck3812]

theorem rawRowCheck3813 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3813 := by decide +kernel

theorem rowCheck3813 : row3813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3813 := by decide +kernel

theorem rowEval3813 (x : Key → ℝ) : Integer.Sparse.eval row3813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3813, Integer.Sparse.eval_collectBalanced, rawRowCheck3813]

theorem rawRowCheck3814 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3814 := by decide +kernel

theorem rowCheck3814 : row3814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3814 := by decide +kernel

theorem rowEval3814 (x : Key → ℝ) : Integer.Sparse.eval row3814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3814, Integer.Sparse.eval_collectBalanced, rawRowCheck3814]

theorem rawRowCheck3815 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow3815 := by decide +kernel

theorem rowCheck3815 : row3815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3815 := by decide +kernel

theorem rowEval3815 (x : Key → ℝ) : Integer.Sparse.eval row3815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3815, Integer.Sparse.eval_collectBalanced, rawRowCheck3815]

theorem rawRowCheck3816 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow3816 := by decide +kernel

theorem rowCheck3816 : row3816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3816 := by decide +kernel

theorem rowEval3816 (x : Key → ℝ) : Integer.Sparse.eval row3816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3816, Integer.Sparse.eval_collectBalanced, rawRowCheck3816]

theorem rawRowCheck3817 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow3817 := by decide +kernel

theorem rowCheck3817 : row3817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3817 := by decide +kernel

theorem rowEval3817 (x : Key → ℝ) : Integer.Sparse.eval row3817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3817, Integer.Sparse.eval_collectBalanced, rawRowCheck3817]

theorem rawRowCheck3818 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3 = rawRow3818 := by decide +kernel

theorem rowCheck3818 : row3818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3818 := by decide +kernel

theorem rowEval3818 (x : Key → ℝ) : Integer.Sparse.eval row3818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3818, Integer.Sparse.eval_collectBalanced, rawRowCheck3818]

theorem rawRowCheck3819 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3 = rawRow3819 := by decide +kernel

theorem rowCheck3819 : row3819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3819 := by decide +kernel

theorem rowEval3819 (x : Key → ℝ) : Integer.Sparse.eval row3819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3819, Integer.Sparse.eval_collectBalanced, rawRowCheck3819]

theorem rawRowCheck3820 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3 = rawRow3820 := by decide +kernel

theorem rowCheck3820 : row3820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3820 := by decide +kernel

theorem rowEval3820 (x : Key → ℝ) : Integer.Sparse.eval row3820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck3820, Integer.Sparse.eval_collectBalanced, rawRowCheck3820]

theorem rawRowCheck3821 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3 = rawRow3821 := by decide +kernel

theorem rowCheck3821 : row3821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3821 := by decide +kernel

theorem rowEval3821 (x : Key → ℝ) : Integer.Sparse.eval row3821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3821, Integer.Sparse.eval_collectBalanced, rawRowCheck3821]

theorem rawRowCheck3822 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3 = rawRow3822 := by decide +kernel

theorem rowCheck3822 : row3822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3822 := by decide +kernel

theorem rowEval3822 (x : Key → ℝ) : Integer.Sparse.eval row3822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck3822, Integer.Sparse.eval_collectBalanced, rawRowCheck3822]

theorem rawRowCheck3823 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3 = rawRow3823 := by decide +kernel

theorem rowCheck3823 : row3823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3823 := by decide +kernel

theorem rowEval3823 (x : Key → ℝ) : Integer.Sparse.eval row3823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck3823, Integer.Sparse.eval_collectBalanced, rawRowCheck3823]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck3974 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9 = rawRow3974 := by decide +kernel

theorem rowCheck3974 : row3974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3974 := by decide +kernel

theorem rowEval3974 (x : Key → ℝ) : Integer.Sparse.eval row3974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3974, Integer.Sparse.eval_collectBalanced, rawRowCheck3974]

theorem rawRowCheck3975 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9 = rawRow3975 := by decide +kernel

theorem rowCheck3975 : row3975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3975 := by decide +kernel

theorem rowEval3975 (x : Key → ℝ) : Integer.Sparse.eval row3975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3975, Integer.Sparse.eval_collectBalanced, rawRowCheck3975]

theorem rawRowCheck3976 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9 = rawRow3976 := by decide +kernel

theorem rowCheck3976 : row3976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3976 := by decide +kernel

theorem rowEval3976 (x : Key → ℝ) : Integer.Sparse.eval row3976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3976, Integer.Sparse.eval_collectBalanced, rawRowCheck3976]

theorem rawRowCheck3977 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9 = rawRow3977 := by decide +kernel

theorem rowCheck3977 : row3977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3977 := by decide +kernel

theorem rowEval3977 (x : Key → ℝ) : Integer.Sparse.eval row3977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3977, Integer.Sparse.eval_collectBalanced, rawRowCheck3977]

theorem rawRowCheck3978 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9 = rawRow3978 := by decide +kernel

theorem rowCheck3978 : row3978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3978 := by decide +kernel

theorem rowEval3978 (x : Key → ℝ) : Integer.Sparse.eval row3978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3978, Integer.Sparse.eval_collectBalanced, rawRowCheck3978]

theorem rawRowCheck3979 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9 = rawRow3979 := by decide +kernel

theorem rowCheck3979 : row3979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3979 := by decide +kernel

theorem rowEval3979 (x : Key → ℝ) : Integer.Sparse.eval row3979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3979, Integer.Sparse.eval_collectBalanced, rawRowCheck3979]

theorem rawRowCheck3980 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3980 := by decide +kernel

theorem rowCheck3980 : row3980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3980 := by decide +kernel

theorem rowEval3980 (x : Key → ℝ) : Integer.Sparse.eval row3980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3980, Integer.Sparse.eval_collectBalanced, rawRowCheck3980]

theorem rawRowCheck3981 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3981 := by decide +kernel

theorem rowCheck3981 : row3981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3981 := by decide +kernel

theorem rowEval3981 (x : Key → ℝ) : Integer.Sparse.eval row3981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3981, Integer.Sparse.eval_collectBalanced, rawRowCheck3981]

theorem rawRowCheck3982 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3982 := by decide +kernel

theorem rowCheck3982 : row3982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3982 := by decide +kernel

theorem rowEval3982 (x : Key → ℝ) : Integer.Sparse.eval row3982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3982, Integer.Sparse.eval_collectBalanced, rawRowCheck3982]

theorem rawRowCheck3983 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9 = rawRow3983 := by decide +kernel

theorem rowCheck3983 : row3983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3983 := by decide +kernel

theorem rowEval3983 (x : Key → ℝ) : Integer.Sparse.eval row3983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3983, Integer.Sparse.eval_collectBalanced, rawRowCheck3983]

theorem rawRowCheck3984 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9 = rawRow3984 := by decide +kernel

theorem rowCheck3984 : row3984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3984 := by decide +kernel

theorem rowEval3984 (x : Key → ℝ) : Integer.Sparse.eval row3984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3984, Integer.Sparse.eval_collectBalanced, rawRowCheck3984]

theorem rawRowCheck3985 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9 = rawRow3985 := by decide +kernel

theorem rowCheck3985 : row3985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3985 := by decide +kernel

theorem rowEval3985 (x : Key → ℝ) : Integer.Sparse.eval row3985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3985, Integer.Sparse.eval_collectBalanced, rawRowCheck3985]

theorem rawRowCheck3986 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9 = rawRow3986 := by decide +kernel

theorem rowCheck3986 : row3986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3986 := by decide +kernel

theorem rowEval3986 (x : Key → ℝ) : Integer.Sparse.eval row3986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3986, Integer.Sparse.eval_collectBalanced, rawRowCheck3986]

theorem rawRowCheck3987 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9 = rawRow3987 := by decide +kernel

theorem rowCheck3987 : row3987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3987 := by decide +kernel

theorem rowEval3987 (x : Key → ℝ) : Integer.Sparse.eval row3987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3987, Integer.Sparse.eval_collectBalanced, rawRowCheck3987]

theorem rawRowCheck3988 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9 = rawRow3988 := by decide +kernel

theorem rowCheck3988 : row3988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3988 := by decide +kernel

theorem rowEval3988 (x : Key → ℝ) : Integer.Sparse.eval row3988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3988, Integer.Sparse.eval_collectBalanced, rawRowCheck3988]

theorem rawRowCheck3989 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3989 := by decide +kernel

theorem rowCheck3989 : row3989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3989 := by decide +kernel

theorem rowEval3989 (x : Key → ℝ) : Integer.Sparse.eval row3989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3989, Integer.Sparse.eval_collectBalanced, rawRowCheck3989]

theorem rawRowCheck3990 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3990 := by decide +kernel

theorem rowCheck3990 : row3990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3990 := by decide +kernel

theorem rowEval3990 (x : Key → ℝ) : Integer.Sparse.eval row3990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3990, Integer.Sparse.eval_collectBalanced, rawRowCheck3990]

theorem rawRowCheck3991 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9 = rawRow3991 := by decide +kernel

theorem rowCheck3991 : row3991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3991 := by decide +kernel

theorem rowEval3991 (x : Key → ℝ) : Integer.Sparse.eval row3991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3991, Integer.Sparse.eval_collectBalanced, rawRowCheck3991]

theorem rawRowCheck3992 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9 = rawRow3992 := by decide +kernel

theorem rowCheck3992 : row3992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3992 := by decide +kernel

theorem rowEval3992 (x : Key → ℝ) : Integer.Sparse.eval row3992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3992, Integer.Sparse.eval_collectBalanced, rawRowCheck3992]

theorem rawRowCheck3993 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9 = rawRow3993 := by decide +kernel

theorem rowCheck3993 : row3993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3993 := by decide +kernel

theorem rowEval3993 (x : Key → ℝ) : Integer.Sparse.eval row3993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3993, Integer.Sparse.eval_collectBalanced, rawRowCheck3993]

theorem rawRowCheck3994 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9 = rawRow3994 := by decide +kernel

theorem rowCheck3994 : row3994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3994 := by decide +kernel

theorem rowEval3994 (x : Key → ℝ) : Integer.Sparse.eval row3994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3994, Integer.Sparse.eval_collectBalanced, rawRowCheck3994]

theorem rawRowCheck3995 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3995 := by decide +kernel

theorem rowCheck3995 : row3995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3995 := by decide +kernel

theorem rowEval3995 (x : Key → ℝ) : Integer.Sparse.eval row3995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3995, Integer.Sparse.eval_collectBalanced, rawRowCheck3995]

theorem rawRowCheck3996 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3996 := by decide +kernel

theorem rowCheck3996 : row3996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3996 := by decide +kernel

theorem rowEval3996 (x : Key → ℝ) : Integer.Sparse.eval row3996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3996, Integer.Sparse.eval_collectBalanced, rawRowCheck3996]

theorem rawRowCheck3997 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3997 := by decide +kernel

theorem rowCheck3997 : row3997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3997 := by decide +kernel

theorem rowEval3997 (x : Key → ℝ) : Integer.Sparse.eval row3997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3997, Integer.Sparse.eval_collectBalanced, rawRowCheck3997]

theorem rawRowCheck3998 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3998 := by decide +kernel

theorem rowCheck3998 : row3998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3998 := by decide +kernel

theorem rowEval3998 (x : Key → ℝ) : Integer.Sparse.eval row3998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3998, Integer.Sparse.eval_collectBalanced, rawRowCheck3998]

theorem rawRowCheck3999 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3999 := by decide +kernel

theorem rowCheck3999 : row3999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3999 := by decide +kernel

theorem rowEval3999 (x : Key → ℝ) : Integer.Sparse.eval row3999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3999, Integer.Sparse.eval_collectBalanced, rawRowCheck3999]

theorem rawRowCheck4000 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9 = rawRow4000 := by decide +kernel

theorem rowCheck4000 : row4000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4000 := by decide +kernel

theorem rowEval4000 (x : Key → ℝ) : Integer.Sparse.eval row4000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4000, Integer.Sparse.eval_collectBalanced, rawRowCheck4000]

theorem rawRowCheck4001 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9 = rawRow4001 := by decide +kernel

theorem rowCheck4001 : row4001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4001 := by decide +kernel

theorem rowEval4001 (x : Key → ℝ) : Integer.Sparse.eval row4001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4001, Integer.Sparse.eval_collectBalanced, rawRowCheck4001]

theorem rawRowCheck4002 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9 = rawRow4002 := by decide +kernel

theorem rowCheck4002 : row4002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4002 := by decide +kernel

theorem rowEval4002 (x : Key → ℝ) : Integer.Sparse.eval row4002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4002, Integer.Sparse.eval_collectBalanced, rawRowCheck4002]

theorem rawRowCheck4003 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9 = rawRow4003 := by decide +kernel

theorem rowCheck4003 : row4003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4003 := by decide +kernel

theorem rowEval4003 (x : Key → ℝ) : Integer.Sparse.eval row4003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4003, Integer.Sparse.eval_collectBalanced, rawRowCheck4003]

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

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval3734 x
  · exact rowEval3735 x
  · exact rowEval3736 x
  · exact rowEval3737 x
  · exact rowEval3738 x
  · exact rowEval3739 x
  · exact rowEval3740 x
  · exact rowEval3741 x
  · exact rowEval3742 x
  · exact rowEval3743 x
  · exact rowEval3744 x
  · exact rowEval3745 x
  · exact rowEval3746 x
  · exact rowEval3747 x
  · exact rowEval3748 x
  · exact rowEval3749 x
  · exact rowEval3750 x
  · exact rowEval3751 x
  · exact rowEval3752 x
  · exact rowEval3753 x
  · exact rowEval3754 x
  · exact rowEval3755 x
  · exact rowEval3756 x
  · exact rowEval3757 x
  · exact rowEval3758 x
  · exact rowEval3759 x
  · exact rowEval3760 x
  · exact rowEval3761 x
  · exact rowEval3762 x
  · exact rowEval3763 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

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

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval3794 x
  · exact rowEval3795 x
  · exact rowEval3796 x
  · exact rowEval3797 x
  · exact rowEval3798 x
  · exact rowEval3799 x
  · exact rowEval3800 x
  · exact rowEval3801 x
  · exact rowEval3802 x
  · exact rowEval3803 x
  · exact rowEval3804 x
  · exact rowEval3805 x
  · exact rowEval3806 x
  · exact rowEval3807 x
  · exact rowEval3808 x
  · exact rowEval3809 x
  · exact rowEval3810 x
  · exact rowEval3811 x
  · exact rowEval3812 x
  · exact rowEval3813 x
  · exact rowEval3814 x
  · exact rowEval3815 x
  · exact rowEval3816 x
  · exact rowEval3817 x
  · exact rowEval3818 x
  · exact rowEval3819 x
  · exact rowEval3820 x
  · exact rowEval3821 x
  · exact rowEval3822 x
  · exact rowEval3823 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval3974 x
  · exact rowEval3975 x
  · exact rowEval3976 x
  · exact rowEval3977 x
  · exact rowEval3978 x
  · exact rowEval3979 x
  · exact rowEval3980 x
  · exact rowEval3981 x
  · exact rowEval3982 x
  · exact rowEval3983 x
  · exact rowEval3984 x
  · exact rowEval3985 x
  · exact rowEval3986 x
  · exact rowEval3987 x
  · exact rowEval3988 x
  · exact rowEval3989 x
  · exact rowEval3990 x
  · exact rowEval3991 x
  · exact rowEval3992 x
  · exact rowEval3993 x
  · exact rowEval3994 x
  · exact rowEval3995 x
  · exact rowEval3996 x
  · exact rowEval3997 x
  · exact rowEval3998 x
  · exact rowEval3999 x
  · exact rowEval4000 x
  · exact rowEval4001 x
  · exact rowEval4002 x
  · exact rowEval4003 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

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

theorem rawRowCheck4794 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form17 = rawRow4794 := by decide +kernel

theorem rowCheck4794 : row4794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4794 := by decide +kernel

theorem rowEval4794 (x : Key → ℝ) : Integer.Sparse.eval row4794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4794, Integer.Sparse.eval_collectBalanced, rawRowCheck4794]

theorem rawRowCheck4795 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form17 = rawRow4795 := by decide +kernel

theorem rowCheck4795 : row4795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4795 := by decide +kernel

theorem rowEval4795 (x : Key → ℝ) : Integer.Sparse.eval row4795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4795, Integer.Sparse.eval_collectBalanced, rawRowCheck4795]

theorem rawRowCheck4796 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form17 = rawRow4796 := by decide +kernel

theorem rowCheck4796 : row4796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4796 := by decide +kernel

theorem rowEval4796 (x : Key → ℝ) : Integer.Sparse.eval row4796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4796, Integer.Sparse.eval_collectBalanced, rawRowCheck4796]

theorem rawRowCheck4797 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form17 = rawRow4797 := by decide +kernel

theorem rowCheck4797 : row4797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4797 := by decide +kernel

theorem rowEval4797 (x : Key → ℝ) : Integer.Sparse.eval row4797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4797, Integer.Sparse.eval_collectBalanced, rawRowCheck4797]

theorem rawRowCheck4798 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form17 = rawRow4798 := by decide +kernel

theorem rowCheck4798 : row4798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4798 := by decide +kernel

theorem rowEval4798 (x : Key → ℝ) : Integer.Sparse.eval row4798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4798, Integer.Sparse.eval_collectBalanced, rawRowCheck4798]

theorem rawRowCheck4799 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form17 = rawRow4799 := by decide +kernel

theorem rowCheck4799 : row4799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4799 := by decide +kernel

theorem rowEval4799 (x : Key → ℝ) : Integer.Sparse.eval row4799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4799, Integer.Sparse.eval_collectBalanced, rawRowCheck4799]

theorem rawRowCheck4800 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form17 = rawRow4800 := by decide +kernel

theorem rowCheck4800 : row4800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4800 := by decide +kernel

theorem rowEval4800 (x : Key → ℝ) : Integer.Sparse.eval row4800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4800, Integer.Sparse.eval_collectBalanced, rawRowCheck4800]

theorem rawRowCheck4801 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4801 := by decide +kernel

theorem rowCheck4801 : row4801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4801 := by decide +kernel

theorem rowEval4801 (x : Key → ℝ) : Integer.Sparse.eval row4801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4801, Integer.Sparse.eval_collectBalanced, rawRowCheck4801]

theorem rawRowCheck4802 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4802 := by decide +kernel

theorem rowCheck4802 : row4802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4802 := by decide +kernel

theorem rowEval4802 (x : Key → ℝ) : Integer.Sparse.eval row4802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4802, Integer.Sparse.eval_collectBalanced, rawRowCheck4802]

theorem rawRowCheck4803 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4803 := by decide +kernel

theorem rowCheck4803 : row4803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4803 := by decide +kernel

theorem rowEval4803 (x : Key → ℝ) : Integer.Sparse.eval row4803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4803, Integer.Sparse.eval_collectBalanced, rawRowCheck4803]

theorem rawRowCheck4804 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form17 = rawRow4804 := by decide +kernel

theorem rowCheck4804 : row4804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4804 := by decide +kernel

theorem rowEval4804 (x : Key → ℝ) : Integer.Sparse.eval row4804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4804, Integer.Sparse.eval_collectBalanced, rawRowCheck4804]

theorem rawRowCheck4805 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4805 := by decide +kernel

theorem rowCheck4805 : row4805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4805 := by decide +kernel

theorem rowEval4805 (x : Key → ℝ) : Integer.Sparse.eval row4805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4805, Integer.Sparse.eval_collectBalanced, rawRowCheck4805]

theorem rawRowCheck4806 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4806 := by decide +kernel

theorem rowCheck4806 : row4806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4806 := by decide +kernel

theorem rowEval4806 (x : Key → ℝ) : Integer.Sparse.eval row4806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4806, Integer.Sparse.eval_collectBalanced, rawRowCheck4806]

theorem rawRowCheck4807 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4807 := by decide +kernel

theorem rowCheck4807 : row4807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4807 := by decide +kernel

theorem rowEval4807 (x : Key → ℝ) : Integer.Sparse.eval row4807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4807, Integer.Sparse.eval_collectBalanced, rawRowCheck4807]

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

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form17) x := by
  fin_cases k
  · exact rowEval4794 x
  · exact rowEval4795 x
  · exact rowEval4796 x
  · exact rowEval4797 x
  · exact rowEval4798 x
  · exact rowEval4799 x
  · exact rowEval4800 x
  · exact rowEval4801 x
  · exact rowEval4802 x
  · exact rowEval4803 x
  · exact rowEval4804 x
  · exact rowEval4805 x
  · exact rowEval4806 x
  · exact rowEval4807 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

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

theorem entryEvalRow17_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 17 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 17).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval17_0_e B hB
  · exact entryEval17_1 B hB
  · exact entryEval17_2 B hB
  · exact entryEval17_3 B hB
  · exact entryEval17_4_e B hB
  · exact entryEval17_5_e B hB
  · exact entryEval17_6_e B hB
  · exact entryEval17_7_e B hB
  · exact entryEval17_8_e B hB
  · exact entryEval17_9 B hB
  · exact entryEval17_10_e B hB
  · exact entryEval17_11_e B hB
  · exact entryEval17_12_e B hB
  · exact entryEval17_13_e B hB
  · exact entryEval17_14_e B hB
  · exact entryEval17_15_e B hB
  · exact entryEval17_16_e B hB
  · exact entryEval17_17_e B hB
  · exact (entryEval18_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_17 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_17_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e_oai
