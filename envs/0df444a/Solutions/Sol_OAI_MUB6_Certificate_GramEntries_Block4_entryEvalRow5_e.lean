-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:46:09.013276+00:00
-- url     : https://prove2.me/submissions/d5178f3b-ce68-4c80-81e9-c1185bd0c05f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_5_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14155 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow14155 := by decide +kernel

theorem rowCheck14155 : row14155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14155 := by decide +kernel

theorem rowEval14155 (x : Key → ℝ) : Integer.Sparse.eval row14155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14155, Integer.Sparse.eval_collectBalanced, rawRowCheck14155]

theorem rawRowCheck14156 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow14156 := by decide +kernel

theorem rowCheck14156 : row14156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14156 := by decide +kernel

theorem rowEval14156 (x : Key → ℝ) : Integer.Sparse.eval row14156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14156, Integer.Sparse.eval_collectBalanced, rawRowCheck14156]

theorem rawRowCheck14157 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow14157 := by decide +kernel

theorem rowCheck14157 : row14157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14157 := by decide +kernel

theorem rowEval14157 (x : Key → ℝ) : Integer.Sparse.eval row14157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14157, Integer.Sparse.eval_collectBalanced, rawRowCheck14157]

theorem rawRowCheck14158 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14158 := by decide +kernel

theorem rowCheck14158 : row14158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14158 := by decide +kernel

theorem rowEval14158 (x : Key → ℝ) : Integer.Sparse.eval row14158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14158, Integer.Sparse.eval_collectBalanced, rawRowCheck14158]

theorem rawRowCheck14159 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14159 := by decide +kernel

theorem rowCheck14159 : row14159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14159 := by decide +kernel

theorem rowEval14159 (x : Key → ℝ) : Integer.Sparse.eval row14159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14159, Integer.Sparse.eval_collectBalanced, rawRowCheck14159]

theorem rawRowCheck14160 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14160 := by decide +kernel

theorem rowCheck14160 : row14160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14160 := by decide +kernel

theorem rowEval14160 (x : Key → ℝ) : Integer.Sparse.eval row14160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14160, Integer.Sparse.eval_collectBalanced, rawRowCheck14160]

theorem rawRowCheck14161 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow14161 := by decide +kernel

theorem rowCheck14161 : row14161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14161 := by decide +kernel

theorem rowEval14161 (x : Key → ℝ) : Integer.Sparse.eval row14161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14161, Integer.Sparse.eval_collectBalanced, rawRowCheck14161]

theorem rawRowCheck14162 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow14162 := by decide +kernel

theorem rowCheck14162 : row14162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14162 := by decide +kernel

theorem rowEval14162 (x : Key → ℝ) : Integer.Sparse.eval row14162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14162, Integer.Sparse.eval_collectBalanced, rawRowCheck14162]

theorem rawRowCheck14163 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow14163 := by decide +kernel

theorem rowCheck14163 : row14163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14163 := by decide +kernel

theorem rowEval14163 (x : Key → ℝ) : Integer.Sparse.eval row14163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14163, Integer.Sparse.eval_collectBalanced, rawRowCheck14163]

theorem rawRowCheck14164 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow14164 := by decide +kernel

theorem rowCheck14164 : row14164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14164 := by decide +kernel

theorem rowEval14164 (x : Key → ℝ) : Integer.Sparse.eval row14164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14164, Integer.Sparse.eval_collectBalanced, rawRowCheck14164]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14701 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14701 := by decide +kernel

theorem rowCheck14701 : row14701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14701 := by decide +kernel

theorem rowEval14701 (x : Key → ℝ) : Integer.Sparse.eval row14701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14701, Integer.Sparse.eval_collectBalanced, rawRowCheck14701]

theorem rawRowCheck14702 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14702 := by decide +kernel

theorem rowCheck14702 : row14702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14702 := by decide +kernel

theorem rowEval14702 (x : Key → ℝ) : Integer.Sparse.eval row14702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14702, Integer.Sparse.eval_collectBalanced, rawRowCheck14702]

theorem rawRowCheck14703 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14703 := by decide +kernel

theorem rowCheck14703 : row14703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14703 := by decide +kernel

theorem rowEval14703 (x : Key → ℝ) : Integer.Sparse.eval row14703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14703, Integer.Sparse.eval_collectBalanced, rawRowCheck14703]

theorem rawRowCheck14704 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14704 := by decide +kernel

theorem rowCheck14704 : row14704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14704 := by decide +kernel

theorem rowEval14704 (x : Key → ℝ) : Integer.Sparse.eval row14704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14704, Integer.Sparse.eval_collectBalanced, rawRowCheck14704]

theorem rawRowCheck14705 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5 = rawRow14705 := by decide +kernel

theorem rowCheck14705 : row14705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14705 := by decide +kernel

theorem rowEval14705 (x : Key → ℝ) : Integer.Sparse.eval row14705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14705, Integer.Sparse.eval_collectBalanced, rawRowCheck14705]

theorem rawRowCheck14706 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5 = rawRow14706 := by decide +kernel

theorem rowCheck14706 : row14706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14706 := by decide +kernel

theorem rowEval14706 (x : Key → ℝ) : Integer.Sparse.eval row14706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14706, Integer.Sparse.eval_collectBalanced, rawRowCheck14706]

theorem rawRowCheck14707 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5 = rawRow14707 := by decide +kernel

theorem rowCheck14707 : row14707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14707 := by decide +kernel

theorem rowEval14707 (x : Key → ℝ) : Integer.Sparse.eval row14707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14707, Integer.Sparse.eval_collectBalanced, rawRowCheck14707]

theorem rawRowCheck14708 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5 = rawRow14708 := by decide +kernel

theorem rowCheck14708 : row14708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14708 := by decide +kernel

theorem rowEval14708 (x : Key → ℝ) : Integer.Sparse.eval row14708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14708, Integer.Sparse.eval_collectBalanced, rawRowCheck14708]

theorem rawRowCheck14709 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5 = rawRow14709 := by decide +kernel

theorem rowCheck14709 : row14709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14709 := by decide +kernel

theorem rowEval14709 (x : Key → ℝ) : Integer.Sparse.eval row14709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14709, Integer.Sparse.eval_collectBalanced, rawRowCheck14709]

theorem rawRowCheck14710 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5 = rawRow14710 := by decide +kernel

theorem rowCheck14710 : row14710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14710 := by decide +kernel

theorem rowEval14710 (x : Key → ℝ) : Integer.Sparse.eval row14710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14710, Integer.Sparse.eval_collectBalanced, rawRowCheck14710]

theorem rawRowCheck14711 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5 = rawRow14711 := by decide +kernel

theorem rowCheck14711 : row14711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14711 := by decide +kernel

theorem rowEval14711 (x : Key → ℝ) : Integer.Sparse.eval row14711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14711, Integer.Sparse.eval_collectBalanced, rawRowCheck14711]

theorem rawRowCheck14712 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5 = rawRow14712 := by decide +kernel

theorem rowCheck14712 : row14712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14712 := by decide +kernel

theorem rowEval14712 (x : Key → ℝ) : Integer.Sparse.eval row14712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14712, Integer.Sparse.eval_collectBalanced, rawRowCheck14712]

theorem rawRowCheck14713 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5 = rawRow14713 := by decide +kernel

theorem rowCheck14713 : row14713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14713 := by decide +kernel

theorem rowEval14713 (x : Key → ℝ) : Integer.Sparse.eval row14713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14713, Integer.Sparse.eval_collectBalanced, rawRowCheck14713]

theorem rawRowCheck14714 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14714 := by decide +kernel

theorem rowCheck14714 : row14714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14714 := by decide +kernel

theorem rowEval14714 (x : Key → ℝ) : Integer.Sparse.eval row14714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14714, Integer.Sparse.eval_collectBalanced, rawRowCheck14714]

theorem rawRowCheck14715 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14715 := by decide +kernel

theorem rowCheck14715 : row14715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14715 := by decide +kernel

theorem rowEval14715 (x : Key → ℝ) : Integer.Sparse.eval row14715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14715, Integer.Sparse.eval_collectBalanced, rawRowCheck14715]

theorem rawRowCheck14716 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14716 := by decide +kernel

theorem rowCheck14716 : row14716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14716 := by decide +kernel

theorem rowEval14716 (x : Key → ℝ) : Integer.Sparse.eval row14716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14716, Integer.Sparse.eval_collectBalanced, rawRowCheck14716]

theorem rawRowCheck14717 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14717 := by decide +kernel

theorem rowCheck14717 : row14717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14717 := by decide +kernel

theorem rowEval14717 (x : Key → ℝ) : Integer.Sparse.eval row14717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14717, Integer.Sparse.eval_collectBalanced, rawRowCheck14717]

theorem rawRowCheck14718 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5 = rawRow14718 := by decide +kernel

theorem rowCheck14718 : row14718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14718 := by decide +kernel

theorem rowEval14718 (x : Key → ℝ) : Integer.Sparse.eval row14718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14718, Integer.Sparse.eval_collectBalanced, rawRowCheck14718]

theorem rawRowCheck14719 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5 = rawRow14719 := by decide +kernel

theorem rowCheck14719 : row14719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14719 := by decide +kernel

theorem rowEval14719 (x : Key → ℝ) : Integer.Sparse.eval row14719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14719, Integer.Sparse.eval_collectBalanced, rawRowCheck14719]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14720 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5 = rawRow14720 := by decide +kernel

theorem rowCheck14720 : row14720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14720 := by decide +kernel

theorem rowEval14720 (x : Key → ℝ) : Integer.Sparse.eval row14720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck14720, Integer.Sparse.eval_collectBalanced, rawRowCheck14720]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14701 x
  · exact rowEval14702 x
  · exact rowEval14703 x
  · exact rowEval14704 x
  · exact rowEval14705 x
  · exact rowEval14706 x
  · exact rowEval14707 x
  · exact rowEval14708 x
  · exact rowEval14709 x
  · exact rowEval14710 x
  · exact rowEval14711 x
  · exact rowEval14712 x
  · exact rowEval14713 x
  · exact rowEval14714 x
  · exact rowEval14715 x
  · exact rowEval14716 x
  · exact rowEval14717 x
  · exact rowEval14718 x
  · exact rowEval14719 x
  · exact rowEval14720 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14961 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14961 := by decide +kernel

theorem rowCheck14961 : row14961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14961 := by decide +kernel

theorem rowEval14961 (x : Key → ℝ) : Integer.Sparse.eval row14961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14961, Integer.Sparse.eval_collectBalanced, rawRowCheck14961]

theorem rawRowCheck14962 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14962 := by decide +kernel

theorem rowCheck14962 : row14962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14962 := by decide +kernel

theorem rowEval14962 (x : Key → ℝ) : Integer.Sparse.eval row14962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14962, Integer.Sparse.eval_collectBalanced, rawRowCheck14962]

theorem rawRowCheck14963 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14963 := by decide +kernel

theorem rowCheck14963 : row14963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14963 := by decide +kernel

theorem rowEval14963 (x : Key → ℝ) : Integer.Sparse.eval row14963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14963, Integer.Sparse.eval_collectBalanced, rawRowCheck14963]

theorem rawRowCheck14964 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14964 := by decide +kernel

theorem rowCheck14964 : row14964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14964 := by decide +kernel

theorem rowEval14964 (x : Key → ℝ) : Integer.Sparse.eval row14964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14964, Integer.Sparse.eval_collectBalanced, rawRowCheck14964]

theorem rawRowCheck14965 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14965 := by decide +kernel

theorem rowCheck14965 : row14965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14965 := by decide +kernel

theorem rowEval14965 (x : Key → ℝ) : Integer.Sparse.eval row14965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14965, Integer.Sparse.eval_collectBalanced, rawRowCheck14965]

theorem rawRowCheck14966 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14966 := by decide +kernel

theorem rowCheck14966 : row14966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14966 := by decide +kernel

theorem rowEval14966 (x : Key → ℝ) : Integer.Sparse.eval row14966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14966, Integer.Sparse.eval_collectBalanced, rawRowCheck14966]

theorem rawRowCheck14967 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5 = rawRow14967 := by decide +kernel

theorem rowCheck14967 : row14967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14967 := by decide +kernel

theorem rowEval14967 (x : Key → ℝ) : Integer.Sparse.eval row14967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14967, Integer.Sparse.eval_collectBalanced, rawRowCheck14967]

theorem rawRowCheck14968 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5 = rawRow14968 := by decide +kernel

theorem rowCheck14968 : row14968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14968 := by decide +kernel

theorem rowEval14968 (x : Key → ℝ) : Integer.Sparse.eval row14968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14968, Integer.Sparse.eval_collectBalanced, rawRowCheck14968]

theorem rawRowCheck14969 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5 = rawRow14969 := by decide +kernel

theorem rowCheck14969 : row14969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14969 := by decide +kernel

theorem rowEval14969 (x : Key → ℝ) : Integer.Sparse.eval row14969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14969, Integer.Sparse.eval_collectBalanced, rawRowCheck14969]

theorem rawRowCheck14970 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14970 := by decide +kernel

theorem rowCheck14970 : row14970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14970 := by decide +kernel

theorem rowEval14970 (x : Key → ℝ) : Integer.Sparse.eval row14970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14970, Integer.Sparse.eval_collectBalanced, rawRowCheck14970]

theorem rawRowCheck14971 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14971 := by decide +kernel

theorem rowCheck14971 : row14971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14971 := by decide +kernel

theorem rowEval14971 (x : Key → ℝ) : Integer.Sparse.eval row14971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14971, Integer.Sparse.eval_collectBalanced, rawRowCheck14971]

theorem rawRowCheck14972 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14972 := by decide +kernel

theorem rowCheck14972 : row14972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14972 := by decide +kernel

theorem rowEval14972 (x : Key → ℝ) : Integer.Sparse.eval row14972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14972, Integer.Sparse.eval_collectBalanced, rawRowCheck14972]

theorem rawRowCheck14973 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14973 := by decide +kernel

theorem rowCheck14973 : row14973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14973 := by decide +kernel

theorem rowEval14973 (x : Key → ℝ) : Integer.Sparse.eval row14973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14973, Integer.Sparse.eval_collectBalanced, rawRowCheck14973]

theorem rawRowCheck14974 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14974 := by decide +kernel

theorem rowCheck14974 : row14974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14974 := by decide +kernel

theorem rowEval14974 (x : Key → ℝ) : Integer.Sparse.eval row14974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14974, Integer.Sparse.eval_collectBalanced, rawRowCheck14974]

theorem rawRowCheck14975 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14975 := by decide +kernel

theorem rowCheck14975 : row14975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14975 := by decide +kernel

theorem rowEval14975 (x : Key → ℝ) : Integer.Sparse.eval row14975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14975, Integer.Sparse.eval_collectBalanced, rawRowCheck14975]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14976 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14976 := by decide +kernel

theorem rowCheck14976 : row14976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14976 := by decide +kernel

theorem rowEval14976 (x : Key → ℝ) : Integer.Sparse.eval row14976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14976, Integer.Sparse.eval_collectBalanced, rawRowCheck14976]

theorem rawRowCheck14977 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14977 := by decide +kernel

theorem rowCheck14977 : row14977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14977 := by decide +kernel

theorem rowEval14977 (x : Key → ℝ) : Integer.Sparse.eval row14977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14977, Integer.Sparse.eval_collectBalanced, rawRowCheck14977]

theorem rawRowCheck14978 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14978 := by decide +kernel

theorem rowCheck14978 : row14978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14978 := by decide +kernel

theorem rowEval14978 (x : Key → ℝ) : Integer.Sparse.eval row14978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14978, Integer.Sparse.eval_collectBalanced, rawRowCheck14978]

theorem rawRowCheck14979 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14979 := by decide +kernel

theorem rowCheck14979 : row14979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14979 := by decide +kernel

theorem rowEval14979 (x : Key → ℝ) : Integer.Sparse.eval row14979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14979, Integer.Sparse.eval_collectBalanced, rawRowCheck14979]

theorem rawRowCheck14980 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14980 := by decide +kernel

theorem rowCheck14980 : row14980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14980 := by decide +kernel

theorem rowEval14980 (x : Key → ℝ) : Integer.Sparse.eval row14980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14980, Integer.Sparse.eval_collectBalanced, rawRowCheck14980]

theorem rawRowCheck14981 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14981 := by decide +kernel

theorem rowCheck14981 : row14981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14981 := by decide +kernel

theorem rowEval14981 (x : Key → ℝ) : Integer.Sparse.eval row14981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14981, Integer.Sparse.eval_collectBalanced, rawRowCheck14981]

theorem rawRowCheck14982 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14982 := by decide +kernel

theorem rowCheck14982 : row14982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14982 := by decide +kernel

theorem rowEval14982 (x : Key → ℝ) : Integer.Sparse.eval row14982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14982, Integer.Sparse.eval_collectBalanced, rawRowCheck14982]

theorem rawRowCheck14983 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14983 := by decide +kernel

theorem rowCheck14983 : row14983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14983 := by decide +kernel

theorem rowEval14983 (x : Key → ℝ) : Integer.Sparse.eval row14983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14983, Integer.Sparse.eval_collectBalanced, rawRowCheck14983]

theorem rawRowCheck14984 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14984 := by decide +kernel

theorem rowCheck14984 : row14984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14984 := by decide +kernel

theorem rowEval14984 (x : Key → ℝ) : Integer.Sparse.eval row14984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14984, Integer.Sparse.eval_collectBalanced, rawRowCheck14984]

theorem rawRowCheck14985 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14985 := by decide +kernel

theorem rowCheck14985 : row14985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14985 := by decide +kernel

theorem rowEval14985 (x : Key → ℝ) : Integer.Sparse.eval row14985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14985, Integer.Sparse.eval_collectBalanced, rawRowCheck14985]

theorem rawRowCheck14986 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14986 := by decide +kernel

theorem rowCheck14986 : row14986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14986 := by decide +kernel

theorem rowEval14986 (x : Key → ℝ) : Integer.Sparse.eval row14986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14986, Integer.Sparse.eval_collectBalanced, rawRowCheck14986]

theorem rawRowCheck14987 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14987 := by decide +kernel

theorem rowCheck14987 : row14987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14987 := by decide +kernel

theorem rowEval14987 (x : Key → ℝ) : Integer.Sparse.eval row14987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14987, Integer.Sparse.eval_collectBalanced, rawRowCheck14987]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14961 x
  · exact rowEval14962 x
  · exact rowEval14963 x
  · exact rowEval14964 x
  · exact rowEval14965 x
  · exact rowEval14966 x
  · exact rowEval14967 x
  · exact rowEval14968 x
  · exact rowEval14969 x
  · exact rowEval14970 x
  · exact rowEval14971 x
  · exact rowEval14972 x
  · exact rowEval14973 x
  · exact rowEval14974 x
  · exact rowEval14975 x
  · exact rowEval14976 x
  · exact rowEval14977 x
  · exact rowEval14978 x
  · exact rowEval14979 x
  · exact rowEval14980 x
  · exact rowEval14981 x
  · exact rowEval14982 x
  · exact rowEval14983 x
  · exact rowEval14984 x
  · exact rowEval14985 x
  · exact rowEval14986 x
  · exact rowEval14987 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13568 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13568 := by decide +kernel

theorem rowCheck13568 : row13568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13568 := by decide +kernel

theorem rowEval13568 (x : Key → ℝ) : Integer.Sparse.eval row13568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13568, Integer.Sparse.eval_collectBalanced, rawRowCheck13568]

theorem rawRowCheck13569 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13569 := by decide +kernel

theorem rowCheck13569 : row13569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13569 := by decide +kernel

theorem rowEval13569 (x : Key → ℝ) : Integer.Sparse.eval row13569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13569, Integer.Sparse.eval_collectBalanced, rawRowCheck13569]

theorem rawRowCheck13570 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13570 := by decide +kernel

theorem rowCheck13570 : row13570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13570 := by decide +kernel

theorem rowEval13570 (x : Key → ℝ) : Integer.Sparse.eval row13570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13570, Integer.Sparse.eval_collectBalanced, rawRowCheck13570]

theorem rawRowCheck13571 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13571 := by decide +kernel

theorem rowCheck13571 : row13571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13571 := by decide +kernel

theorem rowEval13571 (x : Key → ℝ) : Integer.Sparse.eval row13571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13571, Integer.Sparse.eval_collectBalanced, rawRowCheck13571]

theorem rawRowCheck13572 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13572 := by decide +kernel

theorem rowCheck13572 : row13572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13572 := by decide +kernel

theorem rowEval13572 (x : Key → ℝ) : Integer.Sparse.eval row13572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13572, Integer.Sparse.eval_collectBalanced, rawRowCheck13572]

theorem rawRowCheck13573 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13573 := by decide +kernel

theorem rowCheck13573 : row13573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13573 := by decide +kernel

theorem rowEval13573 (x : Key → ℝ) : Integer.Sparse.eval row13573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13573, Integer.Sparse.eval_collectBalanced, rawRowCheck13573]

theorem rawRowCheck13574 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13574 := by decide +kernel

theorem rowCheck13574 : row13574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13574 := by decide +kernel

theorem rowEval13574 (x : Key → ℝ) : Integer.Sparse.eval row13574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13574, Integer.Sparse.eval_collectBalanced, rawRowCheck13574]

theorem rawRowCheck13575 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form5 = rawRow13575 := by decide +kernel

theorem rowCheck13575 : row13575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13575 := by decide +kernel

theorem rowEval13575 (x : Key → ℝ) : Integer.Sparse.eval row13575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13575, Integer.Sparse.eval_collectBalanced, rawRowCheck13575]

theorem rawRowCheck13576 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form5 = rawRow13576 := by decide +kernel

theorem rowCheck13576 : row13576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13576 := by decide +kernel

theorem rowEval13576 (x : Key → ℝ) : Integer.Sparse.eval row13576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13576, Integer.Sparse.eval_collectBalanced, rawRowCheck13576]

theorem rawRowCheck13577 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form5 = rawRow13577 := by decide +kernel

theorem rowCheck13577 : row13577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13577 := by decide +kernel

theorem rowEval13577 (x : Key → ℝ) : Integer.Sparse.eval row13577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13577, Integer.Sparse.eval_collectBalanced, rawRowCheck13577]

theorem rawRowCheck13578 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5 = rawRow13578 := by decide +kernel

theorem rowCheck13578 : row13578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13578 := by decide +kernel

theorem rowEval13578 (x : Key → ℝ) : Integer.Sparse.eval row13578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13578, Integer.Sparse.eval_collectBalanced, rawRowCheck13578]

theorem rawRowCheck13579 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5 = rawRow13579 := by decide +kernel

theorem rowCheck13579 : row13579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13579 := by decide +kernel

theorem rowEval13579 (x : Key → ℝ) : Integer.Sparse.eval row13579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13579, Integer.Sparse.eval_collectBalanced, rawRowCheck13579]

theorem rawRowCheck13580 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5 = rawRow13580 := by decide +kernel

theorem rowCheck13580 : row13580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13580 := by decide +kernel

theorem rowEval13580 (x : Key → ℝ) : Integer.Sparse.eval row13580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13580, Integer.Sparse.eval_collectBalanced, rawRowCheck13580]

theorem rawRowCheck13581 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5 = rawRow13581 := by decide +kernel

theorem rowCheck13581 : row13581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13581 := by decide +kernel

theorem rowEval13581 (x : Key → ℝ) : Integer.Sparse.eval row13581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13581, Integer.Sparse.eval_collectBalanced, rawRowCheck13581]

theorem rawRowCheck13582 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5 = rawRow13582 := by decide +kernel

theorem rowCheck13582 : row13582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13582 := by decide +kernel

theorem rowEval13582 (x : Key → ℝ) : Integer.Sparse.eval row13582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13582, Integer.Sparse.eval_collectBalanced, rawRowCheck13582]

theorem rawRowCheck13583 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5 = rawRow13583 := by decide +kernel

theorem rowCheck13583 : row13583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13583 := by decide +kernel

theorem rowEval13583 (x : Key → ℝ) : Integer.Sparse.eval row13583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13583, Integer.Sparse.eval_collectBalanced, rawRowCheck13583]

theorem rawRowCheck13584 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow13584 := by decide +kernel

theorem rowCheck13584 : row13584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13584 := by decide +kernel

theorem rowEval13584 (x : Key → ℝ) : Integer.Sparse.eval row13584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13584, Integer.Sparse.eval_collectBalanced, rawRowCheck13584]

theorem rawRowCheck13585 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow13585 := by decide +kernel

theorem rowCheck13585 : row13585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13585 := by decide +kernel

theorem rowEval13585 (x : Key → ℝ) : Integer.Sparse.eval row13585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13585, Integer.Sparse.eval_collectBalanced, rawRowCheck13585]

theorem rawRowCheck13586 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow13586 := by decide +kernel

theorem rowCheck13586 : row13586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13586 := by decide +kernel

theorem rowEval13586 (x : Key → ℝ) : Integer.Sparse.eval row13586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13586, Integer.Sparse.eval_collectBalanced, rawRowCheck13586]

theorem rawRowCheck13587 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow13587 := by decide +kernel

theorem rowCheck13587 : row13587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13587 := by decide +kernel

theorem rowEval13587 (x : Key → ℝ) : Integer.Sparse.eval row13587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13587, Integer.Sparse.eval_collectBalanced, rawRowCheck13587]

theorem rawRowCheck13588 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow13588 := by decide +kernel

theorem rowCheck13588 : row13588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13588 := by decide +kernel

theorem rowEval13588 (x : Key → ℝ) : Integer.Sparse.eval row13588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13588, Integer.Sparse.eval_collectBalanced, rawRowCheck13588]

theorem rawRowCheck13589 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow13589 := by decide +kernel

theorem rowCheck13589 : row13589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13589 := by decide +kernel

theorem rowEval13589 (x : Key → ℝ) : Integer.Sparse.eval row13589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13589, Integer.Sparse.eval_collectBalanced, rawRowCheck13589]

theorem rawRowCheck13590 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow13590 := by decide +kernel

theorem rowCheck13590 : row13590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13590 := by decide +kernel

theorem rowEval13590 (x : Key → ℝ) : Integer.Sparse.eval row13590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13590, Integer.Sparse.eval_collectBalanced, rawRowCheck13590]

theorem rawRowCheck13591 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow13591 := by decide +kernel

theorem rowCheck13591 : row13591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13591 := by decide +kernel

theorem rowEval13591 (x : Key → ℝ) : Integer.Sparse.eval row13591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13591, Integer.Sparse.eval_collectBalanced, rawRowCheck13591]

theorem rawRowCheck13592 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow13592 := by decide +kernel

theorem rowCheck13592 : row13592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13592 := by decide +kernel

theorem rowEval13592 (x : Key → ℝ) : Integer.Sparse.eval row13592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck13592, Integer.Sparse.eval_collectBalanced, rawRowCheck13592]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13895 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5 = rawRow13895 := by decide +kernel

theorem rowCheck13895 : row13895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13895 := by decide +kernel

theorem rowEval13895 (x : Key → ℝ) : Integer.Sparse.eval row13895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13895, Integer.Sparse.eval_collectBalanced, rawRowCheck13895]

theorem rawRowCheck13896 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5 = rawRow13896 := by decide +kernel

theorem rowCheck13896 : row13896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13896 := by decide +kernel

theorem rowEval13896 (x : Key → ℝ) : Integer.Sparse.eval row13896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13896, Integer.Sparse.eval_collectBalanced, rawRowCheck13896]

theorem rawRowCheck13897 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5 = rawRow13897 := by decide +kernel

theorem rowCheck13897 : row13897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13897 := by decide +kernel

theorem rowEval13897 (x : Key → ℝ) : Integer.Sparse.eval row13897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13897, Integer.Sparse.eval_collectBalanced, rawRowCheck13897]

theorem rawRowCheck13898 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13898 := by decide +kernel

theorem rowCheck13898 : row13898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13898 := by decide +kernel

theorem rowEval13898 (x : Key → ℝ) : Integer.Sparse.eval row13898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13898, Integer.Sparse.eval_collectBalanced, rawRowCheck13898]

theorem rawRowCheck13899 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13899 := by decide +kernel

theorem rowCheck13899 : row13899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13899 := by decide +kernel

theorem rowEval13899 (x : Key → ℝ) : Integer.Sparse.eval row13899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13899, Integer.Sparse.eval_collectBalanced, rawRowCheck13899]

theorem rawRowCheck13900 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13900 := by decide +kernel

theorem rowCheck13900 : row13900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13900 := by decide +kernel

theorem rowEval13900 (x : Key → ℝ) : Integer.Sparse.eval row13900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13900, Integer.Sparse.eval_collectBalanced, rawRowCheck13900]

theorem rawRowCheck13901 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow13901 := by decide +kernel

theorem rowCheck13901 : row13901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13901 := by decide +kernel

theorem rowEval13901 (x : Key → ℝ) : Integer.Sparse.eval row13901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck13901, Integer.Sparse.eval_collectBalanced, rawRowCheck13901]

theorem rawRowCheck13902 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow13902 := by decide +kernel

theorem rowCheck13902 : row13902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13902 := by decide +kernel

theorem rowEval13902 (x : Key → ℝ) : Integer.Sparse.eval row13902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13902, Integer.Sparse.eval_collectBalanced, rawRowCheck13902]

theorem rawRowCheck13903 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow13903 := by decide +kernel

theorem rowCheck13903 : row13903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13903 := by decide +kernel

theorem rowEval13903 (x : Key → ℝ) : Integer.Sparse.eval row13903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13903, Integer.Sparse.eval_collectBalanced, rawRowCheck13903]

theorem rawRowCheck13904 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow13904 := by decide +kernel

theorem rowCheck13904 : row13904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13904 := by decide +kernel

theorem rowEval13904 (x : Key → ℝ) : Integer.Sparse.eval row13904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck13904, Integer.Sparse.eval_collectBalanced, rawRowCheck13904]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck16797 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5 = rawRow16797 := by decide +kernel

theorem rowCheck16797 : row16797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16797 := by decide +kernel

theorem rowEval16797 (x : Key → ℝ) : Integer.Sparse.eval row16797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16797, Integer.Sparse.eval_collectBalanced, rawRowCheck16797]

theorem rawRowCheck16798 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5 = rawRow16798 := by decide +kernel

theorem rowCheck16798 : row16798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16798 := by decide +kernel

theorem rowEval16798 (x : Key → ℝ) : Integer.Sparse.eval row16798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16798, Integer.Sparse.eval_collectBalanced, rawRowCheck16798]

theorem rawRowCheck16799 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5 = rawRow16799 := by decide +kernel

theorem rowCheck16799 : row16799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16799 := by decide +kernel

theorem rowEval16799 (x : Key → ℝ) : Integer.Sparse.eval row16799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16799, Integer.Sparse.eval_collectBalanced, rawRowCheck16799]

theorem rawRowCheck16800 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16800 := by decide +kernel

theorem rowCheck16800 : row16800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16800 := by decide +kernel

theorem rowEval16800 (x : Key → ℝ) : Integer.Sparse.eval row16800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16800, Integer.Sparse.eval_collectBalanced, rawRowCheck16800]

theorem rawRowCheck16801 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16801 := by decide +kernel

theorem rowCheck16801 : row16801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16801 := by decide +kernel

theorem rowEval16801 (x : Key → ℝ) : Integer.Sparse.eval row16801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16801, Integer.Sparse.eval_collectBalanced, rawRowCheck16801]

theorem rawRowCheck16802 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16802 := by decide +kernel

theorem rowCheck16802 : row16802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16802 := by decide +kernel

theorem rowEval16802 (x : Key → ℝ) : Integer.Sparse.eval row16802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16802, Integer.Sparse.eval_collectBalanced, rawRowCheck16802]

theorem rawRowCheck16803 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16803 := by decide +kernel

theorem rowCheck16803 : row16803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16803 := by decide +kernel

theorem rowEval16803 (x : Key → ℝ) : Integer.Sparse.eval row16803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16803, Integer.Sparse.eval_collectBalanced, rawRowCheck16803]

theorem rawRowCheck16804 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16804 := by decide +kernel

theorem rowCheck16804 : row16804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16804 := by decide +kernel

theorem rowEval16804 (x : Key → ℝ) : Integer.Sparse.eval row16804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16804, Integer.Sparse.eval_collectBalanced, rawRowCheck16804]

theorem rawRowCheck16805 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16805 := by decide +kernel

theorem rowCheck16805 : row16805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16805 := by decide +kernel

theorem rowEval16805 (x : Key → ℝ) : Integer.Sparse.eval row16805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16805, Integer.Sparse.eval_collectBalanced, rawRowCheck16805]

theorem rawRowCheck16806 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow16806 := by decide +kernel

theorem rowCheck16806 : row16806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16806 := by decide +kernel

theorem rowEval16806 (x : Key → ℝ) : Integer.Sparse.eval row16806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16806, Integer.Sparse.eval_collectBalanced, rawRowCheck16806]

theorem rawRowCheck16807 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow16807 := by decide +kernel

theorem rowCheck16807 : row16807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16807 := by decide +kernel

theorem rowEval16807 (x : Key → ℝ) : Integer.Sparse.eval row16807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16807, Integer.Sparse.eval_collectBalanced, rawRowCheck16807]

theorem rawRowCheck16808 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow16808 := by decide +kernel

theorem rowCheck16808 : row16808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16808 := by decide +kernel

theorem rowEval16808 (x : Key → ℝ) : Integer.Sparse.eval row16808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16808, Integer.Sparse.eval_collectBalanced, rawRowCheck16808]

theorem rawRowCheck16809 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow16809 := by decide +kernel

theorem rowCheck16809 : row16809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16809 := by decide +kernel

theorem rowEval16809 (x : Key → ℝ) : Integer.Sparse.eval row16809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16809, Integer.Sparse.eval_collectBalanced, rawRowCheck16809]

theorem rawRowCheck16810 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow16810 := by decide +kernel

theorem rowCheck16810 : row16810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16810 := by decide +kernel

theorem rowEval16810 (x : Key → ℝ) : Integer.Sparse.eval row16810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16810, Integer.Sparse.eval_collectBalanced, rawRowCheck16810]

theorem rawRowCheck16811 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow16811 := by decide +kernel

theorem rowCheck16811 : row16811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16811 := by decide +kernel

theorem rowEval16811 (x : Key → ℝ) : Integer.Sparse.eval row16811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16811, Integer.Sparse.eval_collectBalanced, rawRowCheck16811]

theorem rawRowCheck16812 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow16812 := by decide +kernel

theorem rowCheck16812 : row16812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16812 := by decide +kernel

theorem rowEval16812 (x : Key → ℝ) : Integer.Sparse.eval row16812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16812, Integer.Sparse.eval_collectBalanced, rawRowCheck16812]

theorem rawRowCheck16813 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow16813 := by decide +kernel

theorem rowCheck16813 : row16813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16813 := by decide +kernel

theorem rowEval16813 (x : Key → ℝ) : Integer.Sparse.eval row16813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16813, Integer.Sparse.eval_collectBalanced, rawRowCheck16813]

theorem rawRowCheck16814 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow16814 := by decide +kernel

theorem rowCheck16814 : row16814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16814 := by decide +kernel

theorem rowEval16814 (x : Key → ℝ) : Integer.Sparse.eval row16814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16814, Integer.Sparse.eval_collectBalanced, rawRowCheck16814]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17131 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow17131 := by decide +kernel

theorem rowCheck17131 : row17131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17131 := by decide +kernel

theorem rowEval17131 (x : Key → ℝ) : Integer.Sparse.eval row17131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17131, Integer.Sparse.eval_collectBalanced, rawRowCheck17131]

theorem rawRowCheck17132 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow17132 := by decide +kernel

theorem rowCheck17132 : row17132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17132 := by decide +kernel

theorem rowEval17132 (x : Key → ℝ) : Integer.Sparse.eval row17132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17132, Integer.Sparse.eval_collectBalanced, rawRowCheck17132]

theorem rawRowCheck17133 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow17133 := by decide +kernel

theorem rowCheck17133 : row17133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17133 := by decide +kernel

theorem rowEval17133 (x : Key → ℝ) : Integer.Sparse.eval row17133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17133, Integer.Sparse.eval_collectBalanced, rawRowCheck17133]

theorem rawRowCheck17134 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow17134 := by decide +kernel

theorem rowCheck17134 : row17134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17134 := by decide +kernel

theorem rowEval17134 (x : Key → ℝ) : Integer.Sparse.eval row17134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17134, Integer.Sparse.eval_collectBalanced, rawRowCheck17134]

theorem rawRowCheck17135 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow17135 := by decide +kernel

theorem rowCheck17135 : row17135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17135 := by decide +kernel

theorem rowEval17135 (x : Key → ℝ) : Integer.Sparse.eval row17135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17135, Integer.Sparse.eval_collectBalanced, rawRowCheck17135]

theorem rawRowCheck17136 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow17136 := by decide +kernel

theorem rowCheck17136 : row17136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17136 := by decide +kernel

theorem rowEval17136 (x : Key → ℝ) : Integer.Sparse.eval row17136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17136, Integer.Sparse.eval_collectBalanced, rawRowCheck17136]

theorem rawRowCheck17137 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17137 := by decide +kernel

theorem rowCheck17137 : row17137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17137 := by decide +kernel

theorem rowEval17137 (x : Key → ℝ) : Integer.Sparse.eval row17137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17137, Integer.Sparse.eval_collectBalanced, rawRowCheck17137]

theorem rawRowCheck17138 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17138 := by decide +kernel

theorem rowCheck17138 : row17138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17138 := by decide +kernel

theorem rowEval17138 (x : Key → ℝ) : Integer.Sparse.eval row17138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17138, Integer.Sparse.eval_collectBalanced, rawRowCheck17138]

theorem rawRowCheck17139 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17139 := by decide +kernel

theorem rowCheck17139 : row17139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17139 := by decide +kernel

theorem rowEval17139 (x : Key → ℝ) : Integer.Sparse.eval row17139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17139, Integer.Sparse.eval_collectBalanced, rawRowCheck17139]

theorem rawRowCheck17140 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17140 := by decide +kernel

theorem rowCheck17140 : row17140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17140 := by decide +kernel

theorem rowEval17140 (x : Key → ℝ) : Integer.Sparse.eval row17140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17140, Integer.Sparse.eval_collectBalanced, rawRowCheck17140]

theorem rawRowCheck17141 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17141 := by decide +kernel

theorem rowCheck17141 : row17141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17141 := by decide +kernel

theorem rowEval17141 (x : Key → ℝ) : Integer.Sparse.eval row17141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17141, Integer.Sparse.eval_collectBalanced, rawRowCheck17141]

theorem rawRowCheck17142 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17142 := by decide +kernel

theorem rowCheck17142 : row17142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17142 := by decide +kernel

theorem rowEval17142 (x : Key → ℝ) : Integer.Sparse.eval row17142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17142, Integer.Sparse.eval_collectBalanced, rawRowCheck17142]

theorem rawRowCheck17143 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17143 := by decide +kernel

theorem rowCheck17143 : row17143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17143 := by decide +kernel

theorem rowEval17143 (x : Key → ℝ) : Integer.Sparse.eval row17143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17143, Integer.Sparse.eval_collectBalanced, rawRowCheck17143]

theorem rawRowCheck17144 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17144 := by decide +kernel

theorem rowCheck17144 : row17144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17144 := by decide +kernel

theorem rowEval17144 (x : Key → ℝ) : Integer.Sparse.eval row17144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17144, Integer.Sparse.eval_collectBalanced, rawRowCheck17144]

theorem rawRowCheck17145 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17145 := by decide +kernel

theorem rowCheck17145 : row17145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17145 := by decide +kernel

theorem rowEval17145 (x : Key → ℝ) : Integer.Sparse.eval row17145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17145, Integer.Sparse.eval_collectBalanced, rawRowCheck17145]

theorem rawRowCheck17146 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17146 := by decide +kernel

theorem rowCheck17146 : row17146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17146 := by decide +kernel

theorem rowEval17146 (x : Key → ℝ) : Integer.Sparse.eval row17146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17146, Integer.Sparse.eval_collectBalanced, rawRowCheck17146]

theorem rawRowCheck17147 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17147 := by decide +kernel

theorem rowCheck17147 : row17147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17147 := by decide +kernel

theorem rowEval17147 (x : Key → ℝ) : Integer.Sparse.eval row17147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17147, Integer.Sparse.eval_collectBalanced, rawRowCheck17147]

theorem rawRowCheck17148 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17148 := by decide +kernel

theorem rowCheck17148 : row17148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17148 := by decide +kernel

theorem rowEval17148 (x : Key → ℝ) : Integer.Sparse.eval row17148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17148, Integer.Sparse.eval_collectBalanced, rawRowCheck17148]

theorem rawRowCheck17149 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17149 := by decide +kernel

theorem rowCheck17149 : row17149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17149 := by decide +kernel

theorem rowEval17149 (x : Key → ℝ) : Integer.Sparse.eval row17149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17149, Integer.Sparse.eval_collectBalanced, rawRowCheck17149]

theorem rawRowCheck17150 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17150 := by decide +kernel

theorem rowCheck17150 : row17150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17150 := by decide +kernel

theorem rowEval17150 (x : Key → ℝ) : Integer.Sparse.eval row17150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17150, Integer.Sparse.eval_collectBalanced, rawRowCheck17150]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck17_5 : entry17_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_5 k)) := by decide +kernel

theorem rowsSound17_5 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval16797 x
  · exact rowEval16798 x
  · exact rowEval16799 x
  · exact rowEval16800 x
  · exact rowEval16801 x
  · exact rowEval16802 x
  · exact rowEval16803 x
  · exact rowEval16804 x
  · exact rowEval16805 x
  · exact rowEval16806 x
  · exact rowEval16807 x
  · exact rowEval16808 x
  · exact rowEval16809 x
  · exact rowEval16810 x
  · exact rowEval16811 x
  · exact rowEval16812 x
  · exact rowEval16813 x
  · exact rowEval16814 x

theorem entryEval17_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_5 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck17_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17461 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow17461 := by decide +kernel

theorem rowCheck17461 : row17461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17461 := by decide +kernel

theorem rowEval17461 (x : Key → ℝ) : Integer.Sparse.eval row17461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17461, Integer.Sparse.eval_collectBalanced, rawRowCheck17461]

theorem rawRowCheck17462 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow17462 := by decide +kernel

theorem rowCheck17462 : row17462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17462 := by decide +kernel

theorem rowEval17462 (x : Key → ℝ) : Integer.Sparse.eval row17462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17462, Integer.Sparse.eval_collectBalanced, rawRowCheck17462]

theorem rawRowCheck17463 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow17463 := by decide +kernel

theorem rowCheck17463 : row17463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17463 := by decide +kernel

theorem rowEval17463 (x : Key → ℝ) : Integer.Sparse.eval row17463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17463, Integer.Sparse.eval_collectBalanced, rawRowCheck17463]

theorem rawRowCheck17464 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17464 := by decide +kernel

theorem rowCheck17464 : row17464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17464 := by decide +kernel

theorem rowEval17464 (x : Key → ℝ) : Integer.Sparse.eval row17464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17464, Integer.Sparse.eval_collectBalanced, rawRowCheck17464]

theorem rawRowCheck17465 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17465 := by decide +kernel

theorem rowCheck17465 : row17465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17465 := by decide +kernel

theorem rowEval17465 (x : Key → ℝ) : Integer.Sparse.eval row17465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17465, Integer.Sparse.eval_collectBalanced, rawRowCheck17465]

theorem rawRowCheck17466 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17466 := by decide +kernel

theorem rowCheck17466 : row17466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17466 := by decide +kernel

theorem rowEval17466 (x : Key → ℝ) : Integer.Sparse.eval row17466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17466, Integer.Sparse.eval_collectBalanced, rawRowCheck17466]

theorem rawRowCheck17467 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17467 := by decide +kernel

theorem rowCheck17467 : row17467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17467 := by decide +kernel

theorem rowEval17467 (x : Key → ℝ) : Integer.Sparse.eval row17467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17467, Integer.Sparse.eval_collectBalanced, rawRowCheck17467]

theorem rawRowCheck17468 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17468 := by decide +kernel

theorem rowCheck17468 : row17468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17468 := by decide +kernel

theorem rowEval17468 (x : Key → ℝ) : Integer.Sparse.eval row17468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17468, Integer.Sparse.eval_collectBalanced, rawRowCheck17468]

theorem rawRowCheck17469 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17469 := by decide +kernel

theorem rowCheck17469 : row17469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17469 := by decide +kernel

theorem rowEval17469 (x : Key → ℝ) : Integer.Sparse.eval row17469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17469, Integer.Sparse.eval_collectBalanced, rawRowCheck17469]

theorem rawRowCheck17470 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow17470 := by decide +kernel

theorem rowCheck17470 : row17470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17470 := by decide +kernel

theorem rowEval17470 (x : Key → ℝ) : Integer.Sparse.eval row17470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17470, Integer.Sparse.eval_collectBalanced, rawRowCheck17470]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck18_5 : entry18_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_5 k)) := by decide +kernel

theorem rowsSound18_5 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17131 x
  · exact rowEval17132 x
  · exact rowEval17133 x
  · exact rowEval17134 x
  · exact rowEval17135 x
  · exact rowEval17136 x
  · exact rowEval17137 x
  · exact rowEval17138 x
  · exact rowEval17139 x
  · exact rowEval17140 x
  · exact rowEval17141 x
  · exact rowEval17142 x
  · exact rowEval17143 x
  · exact rowEval17144 x
  · exact rowEval17145 x
  · exact rowEval17146 x
  · exact rowEval17147 x
  · exact rowEval17148 x
  · exact rowEval17149 x
  · exact rowEval17150 x

theorem entryEval18_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_5 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck18_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17461 x
  · exact rowEval17462 x
  · exact rowEval17463 x
  · exact rowEval17464 x
  · exact rowEval17465 x
  · exact rowEval17466 x
  · exact rowEval17467 x
  · exact rowEval17468 x
  · exact rowEval17469 x
  · exact rowEval17470 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17701 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17701 := by decide +kernel

theorem rowCheck17701 : row17701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17701 := by decide +kernel

theorem rowEval17701 (x : Key → ℝ) : Integer.Sparse.eval row17701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17701, Integer.Sparse.eval_collectBalanced, rawRowCheck17701]

theorem rawRowCheck17702 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17702 := by decide +kernel

theorem rowCheck17702 : row17702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17702 := by decide +kernel

theorem rowEval17702 (x : Key → ℝ) : Integer.Sparse.eval row17702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17702, Integer.Sparse.eval_collectBalanced, rawRowCheck17702]

theorem rawRowCheck17703 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17703 := by decide +kernel

theorem rowCheck17703 : row17703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17703 := by decide +kernel

theorem rowEval17703 (x : Key → ℝ) : Integer.Sparse.eval row17703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17703, Integer.Sparse.eval_collectBalanced, rawRowCheck17703]

theorem rawRowCheck17704 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17704 := by decide +kernel

theorem rowCheck17704 : row17704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17704 := by decide +kernel

theorem rowEval17704 (x : Key → ℝ) : Integer.Sparse.eval row17704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17704, Integer.Sparse.eval_collectBalanced, rawRowCheck17704]

theorem rawRowCheck17705 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17705 := by decide +kernel

theorem rowCheck17705 : row17705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17705 := by decide +kernel

theorem rowEval17705 (x : Key → ℝ) : Integer.Sparse.eval row17705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17705, Integer.Sparse.eval_collectBalanced, rawRowCheck17705]

theorem rawRowCheck17706 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17706 := by decide +kernel

theorem rowCheck17706 : row17706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17706 := by decide +kernel

theorem rowEval17706 (x : Key → ℝ) : Integer.Sparse.eval row17706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17706, Integer.Sparse.eval_collectBalanced, rawRowCheck17706]

theorem rawRowCheck17707 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17707 := by decide +kernel

theorem rowCheck17707 : row17707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17707 := by decide +kernel

theorem rowEval17707 (x : Key → ℝ) : Integer.Sparse.eval row17707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17707, Integer.Sparse.eval_collectBalanced, rawRowCheck17707]

theorem rawRowCheck17708 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17708 := by decide +kernel

theorem rowCheck17708 : row17708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17708 := by decide +kernel

theorem rowEval17708 (x : Key → ℝ) : Integer.Sparse.eval row17708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17708, Integer.Sparse.eval_collectBalanced, rawRowCheck17708]

theorem rawRowCheck17709 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17709 := by decide +kernel

theorem rowCheck17709 : row17709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17709 := by decide +kernel

theorem rowEval17709 (x : Key → ℝ) : Integer.Sparse.eval row17709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17709, Integer.Sparse.eval_collectBalanced, rawRowCheck17709]

theorem rawRowCheck17710 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17710 := by decide +kernel

theorem rowCheck17710 : row17710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17710 := by decide +kernel

theorem rowEval17710 (x : Key → ℝ) : Integer.Sparse.eval row17710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17710, Integer.Sparse.eval_collectBalanced, rawRowCheck17710]

theorem rawRowCheck17711 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17711 := by decide +kernel

theorem rowCheck17711 : row17711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17711 := by decide +kernel

theorem rowEval17711 (x : Key → ℝ) : Integer.Sparse.eval row17711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17711, Integer.Sparse.eval_collectBalanced, rawRowCheck17711]

theorem rawRowCheck17712 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17712 := by decide +kernel

theorem rowCheck17712 : row17712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17712 := by decide +kernel

theorem rowEval17712 (x : Key → ℝ) : Integer.Sparse.eval row17712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17712, Integer.Sparse.eval_collectBalanced, rawRowCheck17712]

theorem rawRowCheck17713 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17713 := by decide +kernel

theorem rowCheck17713 : row17713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17713 := by decide +kernel

theorem rowEval17713 (x : Key → ℝ) : Integer.Sparse.eval row17713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17713, Integer.Sparse.eval_collectBalanced, rawRowCheck17713]

theorem rawRowCheck17714 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17714 := by decide +kernel

theorem rowCheck17714 : row17714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17714 := by decide +kernel

theorem rowEval17714 (x : Key → ℝ) : Integer.Sparse.eval row17714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17714, Integer.Sparse.eval_collectBalanced, rawRowCheck17714]

theorem rawRowCheck17715 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17715 := by decide +kernel

theorem rowCheck17715 : row17715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17715 := by decide +kernel

theorem rowEval17715 (x : Key → ℝ) : Integer.Sparse.eval row17715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17715, Integer.Sparse.eval_collectBalanced, rawRowCheck17715]

theorem rawRowCheck17716 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow17716 := by decide +kernel

theorem rowCheck17716 : row17716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17716 := by decide +kernel

theorem rowEval17716 (x : Key → ℝ) : Integer.Sparse.eval row17716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17716, Integer.Sparse.eval_collectBalanced, rawRowCheck17716]

theorem rawRowCheck17717 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow17717 := by decide +kernel

theorem rowCheck17717 : row17717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17717 := by decide +kernel

theorem rowEval17717 (x : Key → ℝ) : Integer.Sparse.eval row17717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17717, Integer.Sparse.eval_collectBalanced, rawRowCheck17717]

theorem rawRowCheck17718 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow17718 := by decide +kernel

theorem rowCheck17718 : row17718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17718 := by decide +kernel

theorem rowEval17718 (x : Key → ℝ) : Integer.Sparse.eval row17718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17718, Integer.Sparse.eval_collectBalanced, rawRowCheck17718]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17701 x
  · exact rowEval17702 x
  · exact rowEval17703 x
  · exact rowEval17704 x
  · exact rowEval17705 x
  · exact rowEval17706 x
  · exact rowEval17707 x
  · exact rowEval17708 x
  · exact rowEval17709 x
  · exact rowEval17710 x
  · exact rowEval17711 x
  · exact rowEval17712 x
  · exact rowEval17713 x
  · exact rowEval17714 x
  · exact rowEval17715 x
  · exact rowEval17716 x
  · exact rowEval17717 x
  · exact rowEval17718 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18089 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow18089 := by decide +kernel

theorem rowCheck18089 : row18089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18089 := by decide +kernel

theorem rowEval18089 (x : Key → ℝ) : Integer.Sparse.eval row18089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18089, Integer.Sparse.eval_collectBalanced, rawRowCheck18089]

theorem rawRowCheck18090 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow18090 := by decide +kernel

theorem rowCheck18090 : row18090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18090 := by decide +kernel

theorem rowEval18090 (x : Key → ℝ) : Integer.Sparse.eval row18090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18090, Integer.Sparse.eval_collectBalanced, rawRowCheck18090]

theorem rawRowCheck18091 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow18091 := by decide +kernel

theorem rowCheck18091 : row18091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18091 := by decide +kernel

theorem rowEval18091 (x : Key → ℝ) : Integer.Sparse.eval row18091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18091, Integer.Sparse.eval_collectBalanced, rawRowCheck18091]

theorem rawRowCheck18092 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow18092 := by decide +kernel

theorem rowCheck18092 : row18092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18092 := by decide +kernel

theorem rowEval18092 (x : Key → ℝ) : Integer.Sparse.eval row18092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18092, Integer.Sparse.eval_collectBalanced, rawRowCheck18092]

theorem rawRowCheck18093 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow18093 := by decide +kernel

theorem rowCheck18093 : row18093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18093 := by decide +kernel

theorem rowEval18093 (x : Key → ℝ) : Integer.Sparse.eval row18093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18093, Integer.Sparse.eval_collectBalanced, rawRowCheck18093]

theorem rawRowCheck18094 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow18094 := by decide +kernel

theorem rowCheck18094 : row18094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18094 := by decide +kernel

theorem rowEval18094 (x : Key → ℝ) : Integer.Sparse.eval row18094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18094, Integer.Sparse.eval_collectBalanced, rawRowCheck18094]

theorem rawRowCheck18095 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18095 := by decide +kernel

theorem rowCheck18095 : row18095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18095 := by decide +kernel

theorem rowEval18095 (x : Key → ℝ) : Integer.Sparse.eval row18095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18095, Integer.Sparse.eval_collectBalanced, rawRowCheck18095]

theorem rawRowCheck18096 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18096 := by decide +kernel

theorem rowCheck18096 : row18096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18096 := by decide +kernel

theorem rowEval18096 (x : Key → ℝ) : Integer.Sparse.eval row18096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18096, Integer.Sparse.eval_collectBalanced, rawRowCheck18096]

theorem rawRowCheck18097 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18097 := by decide +kernel

theorem rowCheck18097 : row18097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18097 := by decide +kernel

theorem rowEval18097 (x : Key → ℝ) : Integer.Sparse.eval row18097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18097, Integer.Sparse.eval_collectBalanced, rawRowCheck18097]

theorem rawRowCheck18098 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18098 := by decide +kernel

theorem rowCheck18098 : row18098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18098 := by decide +kernel

theorem rowEval18098 (x : Key → ℝ) : Integer.Sparse.eval row18098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18098, Integer.Sparse.eval_collectBalanced, rawRowCheck18098]

theorem rawRowCheck18099 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18099 := by decide +kernel

theorem rowCheck18099 : row18099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18099 := by decide +kernel

theorem rowEval18099 (x : Key → ℝ) : Integer.Sparse.eval row18099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18099, Integer.Sparse.eval_collectBalanced, rawRowCheck18099]

theorem rawRowCheck18100 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18100 := by decide +kernel

theorem rowCheck18100 : row18100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18100 := by decide +kernel

theorem rowEval18100 (x : Key → ℝ) : Integer.Sparse.eval row18100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18100, Integer.Sparse.eval_collectBalanced, rawRowCheck18100]

theorem rawRowCheck18101 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5 = rawRow18101 := by decide +kernel

theorem rowCheck18101 : row18101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18101 := by decide +kernel

theorem rowEval18101 (x : Key → ℝ) : Integer.Sparse.eval row18101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18101, Integer.Sparse.eval_collectBalanced, rawRowCheck18101]

theorem rawRowCheck18102 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5 = rawRow18102 := by decide +kernel

theorem rowCheck18102 : row18102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18102 := by decide +kernel

theorem rowEval18102 (x : Key → ℝ) : Integer.Sparse.eval row18102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18102, Integer.Sparse.eval_collectBalanced, rawRowCheck18102]

theorem rawRowCheck18103 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5 = rawRow18103 := by decide +kernel

theorem rowCheck18103 : row18103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18103 := by decide +kernel

theorem rowEval18103 (x : Key → ℝ) : Integer.Sparse.eval row18103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18103, Integer.Sparse.eval_collectBalanced, rawRowCheck18103]

theorem rawRowCheck18104 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18104 := by decide +kernel

theorem rowCheck18104 : row18104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18104 := by decide +kernel

theorem rowEval18104 (x : Key → ℝ) : Integer.Sparse.eval row18104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18104, Integer.Sparse.eval_collectBalanced, rawRowCheck18104]

theorem rawRowCheck18105 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow18105 := by decide +kernel

theorem rowCheck18105 : row18105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18105 := by decide +kernel

theorem rowEval18105 (x : Key → ℝ) : Integer.Sparse.eval row18105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck18105, Integer.Sparse.eval_collectBalanced, rawRowCheck18105]

theorem rawRowCheck18106 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow18106 := by decide +kernel

theorem rowCheck18106 : row18106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18106 := by decide +kernel

theorem rowEval18106 (x : Key → ℝ) : Integer.Sparse.eval row18106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18106, Integer.Sparse.eval_collectBalanced, rawRowCheck18106]

theorem rawRowCheck18107 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow18107 := by decide +kernel

theorem rowCheck18107 : row18107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18107 := by decide +kernel

theorem rowEval18107 (x : Key → ℝ) : Integer.Sparse.eval row18107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18107, Integer.Sparse.eval_collectBalanced, rawRowCheck18107]

theorem rawRowCheck18108 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow18108 := by decide +kernel

theorem rowCheck18108 : row18108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18108 := by decide +kernel

theorem rowEval18108 (x : Key → ℝ) : Integer.Sparse.eval row18108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck18108, Integer.Sparse.eval_collectBalanced, rawRowCheck18108]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck21_5 : entry21_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_5 k)) := by decide +kernel

theorem rowsSound21_5 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval18089 x
  · exact rowEval18090 x
  · exact rowEval18091 x
  · exact rowEval18092 x
  · exact rowEval18093 x
  · exact rowEval18094 x
  · exact rowEval18095 x
  · exact rowEval18096 x
  · exact rowEval18097 x
  · exact rowEval18098 x
  · exact rowEval18099 x
  · exact rowEval18100 x
  · exact rowEval18101 x
  · exact rowEval18102 x
  · exact rowEval18103 x
  · exact rowEval18104 x
  · exact rowEval18105 x
  · exact rowEval18106 x
  · exact rowEval18107 x
  · exact rowEval18108 x

theorem entryEval21_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_5 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck21_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13485 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0 = rawRow13485 := by decide +kernel

theorem rowCheck13485 : row13485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13485 := by decide +kernel

theorem rowEval13485 (x : Key → ℝ) : Integer.Sparse.eval row13485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13485, Integer.Sparse.eval_collectBalanced, rawRowCheck13485]

theorem rawRowCheck13486 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0 = rawRow13486 := by decide +kernel

theorem rowCheck13486 : row13486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13486 := by decide +kernel

theorem rowEval13486 (x : Key → ℝ) : Integer.Sparse.eval row13486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13486, Integer.Sparse.eval_collectBalanced, rawRowCheck13486]

theorem rawRowCheck13487 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0 = rawRow13487 := by decide +kernel

theorem rowCheck13487 : row13487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13487 := by decide +kernel

theorem rowEval13487 (x : Key → ℝ) : Integer.Sparse.eval row13487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13487, Integer.Sparse.eval_collectBalanced, rawRowCheck13487]

theorem rawRowCheck13488 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13488 := by decide +kernel

theorem rowCheck13488 : row13488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13488 := by decide +kernel

theorem rowEval13488 (x : Key → ℝ) : Integer.Sparse.eval row13488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13488, Integer.Sparse.eval_collectBalanced, rawRowCheck13488]

theorem rawRowCheck13489 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13489 := by decide +kernel

theorem rowCheck13489 : row13489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13489 := by decide +kernel

theorem rowEval13489 (x : Key → ℝ) : Integer.Sparse.eval row13489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13489, Integer.Sparse.eval_collectBalanced, rawRowCheck13489]

theorem rawRowCheck13490 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13490 := by decide +kernel

theorem rowCheck13490 : row13490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13490 := by decide +kernel

theorem rowEval13490 (x : Key → ℝ) : Integer.Sparse.eval row13490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13490, Integer.Sparse.eval_collectBalanced, rawRowCheck13490]

theorem rawRowCheck13491 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13491 := by decide +kernel

theorem rowCheck13491 : row13491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13491 := by decide +kernel

theorem rowEval13491 (x : Key → ℝ) : Integer.Sparse.eval row13491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13491, Integer.Sparse.eval_collectBalanced, rawRowCheck13491]

theorem rawRowCheck13492 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13492 := by decide +kernel

theorem rowCheck13492 : row13492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13492 := by decide +kernel

theorem rowEval13492 (x : Key → ℝ) : Integer.Sparse.eval row13492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13492, Integer.Sparse.eval_collectBalanced, rawRowCheck13492]

theorem rawRowCheck13493 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13493 := by decide +kernel

theorem rowCheck13493 : row13493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13493 := by decide +kernel

theorem rowEval13493 (x : Key → ℝ) : Integer.Sparse.eval row13493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13493, Integer.Sparse.eval_collectBalanced, rawRowCheck13493]

theorem rawRowCheck13494 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13494 := by decide +kernel

theorem rowCheck13494 : row13494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13494 := by decide +kernel

theorem rowEval13494 (x : Key → ℝ) : Integer.Sparse.eval row13494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13494, Integer.Sparse.eval_collectBalanced, rawRowCheck13494]

theorem rawRowCheck13495 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13495 := by decide +kernel

theorem rowCheck13495 : row13495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13495 := by decide +kernel

theorem rowEval13495 (x : Key → ℝ) : Integer.Sparse.eval row13495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13495, Integer.Sparse.eval_collectBalanced, rawRowCheck13495]

theorem rawRowCheck13496 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13496 := by decide +kernel

theorem rowCheck13496 : row13496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13496 := by decide +kernel

theorem rowEval13496 (x : Key → ℝ) : Integer.Sparse.eval row13496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13496, Integer.Sparse.eval_collectBalanced, rawRowCheck13496]

theorem rawRowCheck13497 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13497 := by decide +kernel

theorem rowCheck13497 : row13497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13497 := by decide +kernel

theorem rowEval13497 (x : Key → ℝ) : Integer.Sparse.eval row13497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13497, Integer.Sparse.eval_collectBalanced, rawRowCheck13497]

theorem rawRowCheck13498 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13498 := by decide +kernel

theorem rowCheck13498 : row13498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13498 := by decide +kernel

theorem rowEval13498 (x : Key → ℝ) : Integer.Sparse.eval row13498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13498, Integer.Sparse.eval_collectBalanced, rawRowCheck13498]

theorem rawRowCheck13499 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13499 := by decide +kernel

theorem rowCheck13499 : row13499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13499 := by decide +kernel

theorem rowEval13499 (x : Key → ℝ) : Integer.Sparse.eval row13499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13499, Integer.Sparse.eval_collectBalanced, rawRowCheck13499]

theorem rawRowCheck13500 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13500 := by decide +kernel

theorem rowCheck13500 : row13500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13500 := by decide +kernel

theorem rowEval13500 (x : Key → ℝ) : Integer.Sparse.eval row13500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13500, Integer.Sparse.eval_collectBalanced, rawRowCheck13500]

theorem rawRowCheck13501 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13501 := by decide +kernel

theorem rowCheck13501 : row13501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13501 := by decide +kernel

theorem rowEval13501 (x : Key → ℝ) : Integer.Sparse.eval row13501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13501, Integer.Sparse.eval_collectBalanced, rawRowCheck13501]

theorem rawRowCheck13502 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13502 := by decide +kernel

theorem rowCheck13502 : row13502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13502 := by decide +kernel

theorem rowEval13502 (x : Key → ℝ) : Integer.Sparse.eval row13502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13502, Integer.Sparse.eval_collectBalanced, rawRowCheck13502]

theorem rawRowCheck13503 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1 = rawRow13503 := by decide +kernel

theorem rowCheck13503 : row13503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13503 := by decide +kernel

theorem rowEval13503 (x : Key → ℝ) : Integer.Sparse.eval row13503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13503, Integer.Sparse.eval_collectBalanced, rawRowCheck13503]

theorem rawRowCheck13504 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1 = rawRow13504 := by decide +kernel

theorem rowCheck13504 : row13504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13504 := by decide +kernel

theorem rowEval13504 (x : Key → ℝ) : Integer.Sparse.eval row13504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13504, Integer.Sparse.eval_collectBalanced, rawRowCheck13504]

theorem rawRowCheck13505 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1 = rawRow13505 := by decide +kernel

theorem rowCheck13505 : row13505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13505 := by decide +kernel

theorem rowEval13505 (x : Key → ℝ) : Integer.Sparse.eval row13505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13505, Integer.Sparse.eval_collectBalanced, rawRowCheck13505]

theorem rawRowCheck13506 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13506 := by decide +kernel

theorem rowCheck13506 : row13506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13506 := by decide +kernel

theorem rowEval13506 (x : Key → ℝ) : Integer.Sparse.eval row13506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13506, Integer.Sparse.eval_collectBalanced, rawRowCheck13506]

theorem rawRowCheck13507 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13507 := by decide +kernel

theorem rowCheck13507 : row13507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13507 := by decide +kernel

theorem rowEval13507 (x : Key → ℝ) : Integer.Sparse.eval row13507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13507, Integer.Sparse.eval_collectBalanced, rawRowCheck13507]

theorem rawRowCheck13508 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13508 := by decide +kernel

theorem rowCheck13508 : row13508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13508 := by decide +kernel

theorem rowEval13508 (x : Key → ℝ) : Integer.Sparse.eval row13508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13508, Integer.Sparse.eval_collectBalanced, rawRowCheck13508]

theorem rawRowCheck13509 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13509 := by decide +kernel

theorem rowCheck13509 : row13509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13509 := by decide +kernel

theorem rowEval13509 (x : Key → ℝ) : Integer.Sparse.eval row13509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13509, Integer.Sparse.eval_collectBalanced, rawRowCheck13509]

theorem rawRowCheck13510 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13510 := by decide +kernel

theorem rowCheck13510 : row13510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13510 := by decide +kernel

theorem rowEval13510 (x : Key → ℝ) : Integer.Sparse.eval row13510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13510, Integer.Sparse.eval_collectBalanced, rawRowCheck13510]

theorem rawRowCheck13511 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13511 := by decide +kernel

theorem rowCheck13511 : row13511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13511 := by decide +kernel

theorem rowEval13511 (x : Key → ℝ) : Integer.Sparse.eval row13511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13511, Integer.Sparse.eval_collectBalanced, rawRowCheck13511]

theorem rawRowCheck13512 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13512 := by decide +kernel

theorem rowCheck13512 : row13512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13512 := by decide +kernel

theorem rowEval13512 (x : Key → ℝ) : Integer.Sparse.eval row13512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13512, Integer.Sparse.eval_collectBalanced, rawRowCheck13512]

theorem rawRowCheck13513 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13513 := by decide +kernel

theorem rowCheck13513 : row13513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13513 := by decide +kernel

theorem rowEval13513 (x : Key → ℝ) : Integer.Sparse.eval row13513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13513, Integer.Sparse.eval_collectBalanced, rawRowCheck13513]

theorem rawRowCheck13514 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13514 := by decide +kernel

theorem rowCheck13514 : row13514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13514 := by decide +kernel

theorem rowEval13514 (x : Key → ℝ) : Integer.Sparse.eval row13514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13514, Integer.Sparse.eval_collectBalanced, rawRowCheck13514]

theorem rawRowCheck13515 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13515 := by decide +kernel

theorem rowCheck13515 : row13515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13515 := by decide +kernel

theorem rowEval13515 (x : Key → ℝ) : Integer.Sparse.eval row13515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13515, Integer.Sparse.eval_collectBalanced, rawRowCheck13515]

theorem rawRowCheck13516 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13516 := by decide +kernel

theorem rowCheck13516 : row13516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13516 := by decide +kernel

theorem rowEval13516 (x : Key → ℝ) : Integer.Sparse.eval row13516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13516, Integer.Sparse.eval_collectBalanced, rawRowCheck13516]

theorem rawRowCheck13517 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13517 := by decide +kernel

theorem rowCheck13517 : row13517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13517 := by decide +kernel

theorem rowEval13517 (x : Key → ℝ) : Integer.Sparse.eval row13517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13517, Integer.Sparse.eval_collectBalanced, rawRowCheck13517]

theorem rawRowCheck13518 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13518 := by decide +kernel

theorem rowCheck13518 : row13518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13518 := by decide +kernel

theorem rowEval13518 (x : Key → ℝ) : Integer.Sparse.eval row13518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13518, Integer.Sparse.eval_collectBalanced, rawRowCheck13518]

theorem rawRowCheck13519 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13519 := by decide +kernel

theorem rowCheck13519 : row13519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13519 := by decide +kernel

theorem rowEval13519 (x : Key → ℝ) : Integer.Sparse.eval row13519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13519, Integer.Sparse.eval_collectBalanced, rawRowCheck13519]

theorem rawRowCheck13520 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13520 := by decide +kernel

theorem rowCheck13520 : row13520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13520 := by decide +kernel

theorem rowEval13520 (x : Key → ℝ) : Integer.Sparse.eval row13520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13520, Integer.Sparse.eval_collectBalanced, rawRowCheck13520]

theorem rawRowCheck13521 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2 = rawRow13521 := by decide +kernel

theorem rowCheck13521 : row13521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13521 := by decide +kernel

theorem rowEval13521 (x : Key → ℝ) : Integer.Sparse.eval row13521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13521, Integer.Sparse.eval_collectBalanced, rawRowCheck13521]

theorem rawRowCheck13522 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2 = rawRow13522 := by decide +kernel

theorem rowCheck13522 : row13522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13522 := by decide +kernel

theorem rowEval13522 (x : Key → ℝ) : Integer.Sparse.eval row13522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13522, Integer.Sparse.eval_collectBalanced, rawRowCheck13522]

theorem rawRowCheck13523 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2 = rawRow13523 := by decide +kernel

theorem rowCheck13523 : row13523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13523 := by decide +kernel

theorem rowEval13523 (x : Key → ℝ) : Integer.Sparse.eval row13523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13523, Integer.Sparse.eval_collectBalanced, rawRowCheck13523]

theorem rawRowCheck13524 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13524 := by decide +kernel

theorem rowCheck13524 : row13524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13524 := by decide +kernel

theorem rowEval13524 (x : Key → ℝ) : Integer.Sparse.eval row13524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13524, Integer.Sparse.eval_collectBalanced, rawRowCheck13524]

theorem rawRowCheck13525 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13525 := by decide +kernel

theorem rowCheck13525 : row13525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13525 := by decide +kernel

theorem rowEval13525 (x : Key → ℝ) : Integer.Sparse.eval row13525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13525, Integer.Sparse.eval_collectBalanced, rawRowCheck13525]

theorem rawRowCheck13526 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13526 := by decide +kernel

theorem rowCheck13526 : row13526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13526 := by decide +kernel

theorem rowEval13526 (x : Key → ℝ) : Integer.Sparse.eval row13526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13526, Integer.Sparse.eval_collectBalanced, rawRowCheck13526]

theorem rawRowCheck13527 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13527 := by decide +kernel

theorem rowCheck13527 : row13527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13527 := by decide +kernel

theorem rowEval13527 (x : Key → ℝ) : Integer.Sparse.eval row13527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13527, Integer.Sparse.eval_collectBalanced, rawRowCheck13527]

theorem rawRowCheck13528 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13528 := by decide +kernel

theorem rowCheck13528 : row13528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13528 := by decide +kernel

theorem rowEval13528 (x : Key → ℝ) : Integer.Sparse.eval row13528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13528, Integer.Sparse.eval_collectBalanced, rawRowCheck13528]

theorem rawRowCheck13529 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13529 := by decide +kernel

theorem rowCheck13529 : row13529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13529 := by decide +kernel

theorem rowEval13529 (x : Key → ℝ) : Integer.Sparse.eval row13529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13529, Integer.Sparse.eval_collectBalanced, rawRowCheck13529]

theorem rawRowCheck13530 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13530 := by decide +kernel

theorem rowCheck13530 : row13530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13530 := by decide +kernel

theorem rowEval13530 (x : Key → ℝ) : Integer.Sparse.eval row13530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13530, Integer.Sparse.eval_collectBalanced, rawRowCheck13530]

theorem rawRowCheck13531 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13531 := by decide +kernel

theorem rowCheck13531 : row13531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13531 := by decide +kernel

theorem rowEval13531 (x : Key → ℝ) : Integer.Sparse.eval row13531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13531, Integer.Sparse.eval_collectBalanced, rawRowCheck13531]

theorem rawRowCheck13532 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13532 := by decide +kernel

theorem rowCheck13532 : row13532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13532 := by decide +kernel

theorem rowEval13532 (x : Key → ℝ) : Integer.Sparse.eval row13532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13532, Integer.Sparse.eval_collectBalanced, rawRowCheck13532]

theorem rawRowCheck13533 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13533 := by decide +kernel

theorem rowCheck13533 : row13533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13533 := by decide +kernel

theorem rowEval13533 (x : Key → ℝ) : Integer.Sparse.eval row13533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13533, Integer.Sparse.eval_collectBalanced, rawRowCheck13533]

theorem rawRowCheck13534 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13534 := by decide +kernel

theorem rowCheck13534 : row13534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13534 := by decide +kernel

theorem rowEval13534 (x : Key → ℝ) : Integer.Sparse.eval row13534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13534, Integer.Sparse.eval_collectBalanced, rawRowCheck13534]

theorem rawRowCheck13535 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13535 := by decide +kernel

theorem rowCheck13535 : row13535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13535 := by decide +kernel

theorem rowEval13535 (x : Key → ℝ) : Integer.Sparse.eval row13535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13535, Integer.Sparse.eval_collectBalanced, rawRowCheck13535]

theorem rawRowCheck13536 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13536 := by decide +kernel

theorem rowCheck13536 : row13536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13536 := by decide +kernel

theorem rowEval13536 (x : Key → ℝ) : Integer.Sparse.eval row13536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13536, Integer.Sparse.eval_collectBalanced, rawRowCheck13536]

theorem rawRowCheck13537 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13537 := by decide +kernel

theorem rowCheck13537 : row13537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13537 := by decide +kernel

theorem rowEval13537 (x : Key → ℝ) : Integer.Sparse.eval row13537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13537, Integer.Sparse.eval_collectBalanced, rawRowCheck13537]

theorem rawRowCheck13538 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13538 := by decide +kernel

theorem rowCheck13538 : row13538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13538 := by decide +kernel

theorem rowEval13538 (x : Key → ℝ) : Integer.Sparse.eval row13538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13538, Integer.Sparse.eval_collectBalanced, rawRowCheck13538]

theorem rawRowCheck13539 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3 = rawRow13539 := by decide +kernel

theorem rowCheck13539 : row13539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13539 := by decide +kernel

theorem rowEval13539 (x : Key → ℝ) : Integer.Sparse.eval row13539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13539, Integer.Sparse.eval_collectBalanced, rawRowCheck13539]

theorem rawRowCheck13540 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3 = rawRow13540 := by decide +kernel

theorem rowCheck13540 : row13540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13540 := by decide +kernel

theorem rowEval13540 (x : Key → ℝ) : Integer.Sparse.eval row13540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13540, Integer.Sparse.eval_collectBalanced, rawRowCheck13540]

theorem rawRowCheck13541 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3 = rawRow13541 := by decide +kernel

theorem rowCheck13541 : row13541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13541 := by decide +kernel

theorem rowEval13541 (x : Key → ℝ) : Integer.Sparse.eval row13541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13541, Integer.Sparse.eval_collectBalanced, rawRowCheck13541]

theorem rawRowCheck13542 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13542 := by decide +kernel

theorem rowCheck13542 : row13542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13542 := by decide +kernel

theorem rowEval13542 (x : Key → ℝ) : Integer.Sparse.eval row13542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13542, Integer.Sparse.eval_collectBalanced, rawRowCheck13542]

theorem rawRowCheck13543 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13543 := by decide +kernel

theorem rowCheck13543 : row13543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13543 := by decide +kernel

theorem rowEval13543 (x : Key → ℝ) : Integer.Sparse.eval row13543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13543, Integer.Sparse.eval_collectBalanced, rawRowCheck13543]

theorem rawRowCheck13544 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13544 := by decide +kernel

theorem rowCheck13544 : row13544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13544 := by decide +kernel

theorem rowEval13544 (x : Key → ℝ) : Integer.Sparse.eval row13544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13544, Integer.Sparse.eval_collectBalanced, rawRowCheck13544]

theorem rawRowCheck13545 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13545 := by decide +kernel

theorem rowCheck13545 : row13545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13545 := by decide +kernel

theorem rowEval13545 (x : Key → ℝ) : Integer.Sparse.eval row13545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13545, Integer.Sparse.eval_collectBalanced, rawRowCheck13545]

theorem rawRowCheck13546 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13546 := by decide +kernel

theorem rowCheck13546 : row13546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13546 := by decide +kernel

theorem rowEval13546 (x : Key → ℝ) : Integer.Sparse.eval row13546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13546, Integer.Sparse.eval_collectBalanced, rawRowCheck13546]

theorem rawRowCheck13547 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13547 := by decide +kernel

theorem rowCheck13547 : row13547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13547 := by decide +kernel

theorem rowEval13547 (x : Key → ℝ) : Integer.Sparse.eval row13547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13547, Integer.Sparse.eval_collectBalanced, rawRowCheck13547]

theorem rawRowCheck13548 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13548 := by decide +kernel

theorem rowCheck13548 : row13548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13548 := by decide +kernel

theorem rowEval13548 (x : Key → ℝ) : Integer.Sparse.eval row13548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13548, Integer.Sparse.eval_collectBalanced, rawRowCheck13548]

theorem rawRowCheck13549 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13549 := by decide +kernel

theorem rowCheck13549 : row13549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13549 := by decide +kernel

theorem rowEval13549 (x : Key → ℝ) : Integer.Sparse.eval row13549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13549, Integer.Sparse.eval_collectBalanced, rawRowCheck13549]

theorem rawRowCheck13550 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13550 := by decide +kernel

theorem rowCheck13550 : row13550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13550 := by decide +kernel

theorem rowEval13550 (x : Key → ℝ) : Integer.Sparse.eval row13550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13550, Integer.Sparse.eval_collectBalanced, rawRowCheck13550]

theorem rawRowCheck13551 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13551 := by decide +kernel

theorem rowCheck13551 : row13551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13551 := by decide +kernel

theorem rowEval13551 (x : Key → ℝ) : Integer.Sparse.eval row13551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13551, Integer.Sparse.eval_collectBalanced, rawRowCheck13551]

theorem rawRowCheck13552 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13552 := by decide +kernel

theorem rowCheck13552 : row13552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13552 := by decide +kernel

theorem rowEval13552 (x : Key → ℝ) : Integer.Sparse.eval row13552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13552, Integer.Sparse.eval_collectBalanced, rawRowCheck13552]

theorem rawRowCheck13553 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13553 := by decide +kernel

theorem rowCheck13553 : row13553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13553 := by decide +kernel

theorem rowEval13553 (x : Key → ℝ) : Integer.Sparse.eval row13553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13553, Integer.Sparse.eval_collectBalanced, rawRowCheck13553]

theorem rawRowCheck13554 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13554 := by decide +kernel

theorem rowCheck13554 : row13554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13554 := by decide +kernel

theorem rowEval13554 (x : Key → ℝ) : Integer.Sparse.eval row13554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13554, Integer.Sparse.eval_collectBalanced, rawRowCheck13554]

theorem rawRowCheck13555 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13555 := by decide +kernel

theorem rowCheck13555 : row13555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13555 := by decide +kernel

theorem rowEval13555 (x : Key → ℝ) : Integer.Sparse.eval row13555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13555, Integer.Sparse.eval_collectBalanced, rawRowCheck13555]

theorem rawRowCheck13556 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13556 := by decide +kernel

theorem rowCheck13556 : row13556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13556 := by decide +kernel

theorem rowEval13556 (x : Key → ℝ) : Integer.Sparse.eval row13556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13556, Integer.Sparse.eval_collectBalanced, rawRowCheck13556]

theorem rawRowCheck13557 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form4 = rawRow13557 := by decide +kernel

theorem rowCheck13557 : row13557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13557 := by decide +kernel

theorem rowEval13557 (x : Key → ℝ) : Integer.Sparse.eval row13557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13557, Integer.Sparse.eval_collectBalanced, rawRowCheck13557]

theorem rawRowCheck13558 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form4 = rawRow13558 := by decide +kernel

theorem rowCheck13558 : row13558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13558 := by decide +kernel

theorem rowEval13558 (x : Key → ℝ) : Integer.Sparse.eval row13558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13558, Integer.Sparse.eval_collectBalanced, rawRowCheck13558]

theorem rawRowCheck13559 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form4 = rawRow13559 := by decide +kernel

theorem rowCheck13559 : row13559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13559 := by decide +kernel

theorem rowEval13559 (x : Key → ℝ) : Integer.Sparse.eval row13559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13559, Integer.Sparse.eval_collectBalanced, rawRowCheck13559]

theorem rawRowCheck13560 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13560 := by decide +kernel

theorem rowCheck13560 : row13560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13560 := by decide +kernel

theorem rowEval13560 (x : Key → ℝ) : Integer.Sparse.eval row13560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13560, Integer.Sparse.eval_collectBalanced, rawRowCheck13560]

theorem rawRowCheck13561 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13561 := by decide +kernel

theorem rowCheck13561 : row13561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13561 := by decide +kernel

theorem rowEval13561 (x : Key → ℝ) : Integer.Sparse.eval row13561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13561, Integer.Sparse.eval_collectBalanced, rawRowCheck13561]

theorem rawRowCheck13562 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13562 := by decide +kernel

theorem rowCheck13562 : row13562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13562 := by decide +kernel

theorem rowEval13562 (x : Key → ℝ) : Integer.Sparse.eval row13562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13562, Integer.Sparse.eval_collectBalanced, rawRowCheck13562]

theorem rawRowCheck13563 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13563 := by decide +kernel

theorem rowCheck13563 : row13563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13563 := by decide +kernel

theorem rowEval13563 (x : Key → ℝ) : Integer.Sparse.eval row13563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13563, Integer.Sparse.eval_collectBalanced, rawRowCheck13563]

theorem rawRowCheck13564 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13564 := by decide +kernel

theorem rowCheck13564 : row13564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13564 := by decide +kernel

theorem rowEval13564 (x : Key → ℝ) : Integer.Sparse.eval row13564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13564, Integer.Sparse.eval_collectBalanced, rawRowCheck13564]

theorem rawRowCheck13565 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13565 := by decide +kernel

theorem rowCheck13565 : row13565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13565 := by decide +kernel

theorem rowEval13565 (x : Key → ℝ) : Integer.Sparse.eval row13565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13565, Integer.Sparse.eval_collectBalanced, rawRowCheck13565]

theorem rawRowCheck13566 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13566 := by decide +kernel

theorem rowCheck13566 : row13566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13566 := by decide +kernel

theorem rowEval13566 (x : Key → ℝ) : Integer.Sparse.eval row13566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13566, Integer.Sparse.eval_collectBalanced, rawRowCheck13566]

theorem rawRowCheck13567 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13567 := by decide +kernel

theorem rowCheck13567 : row13567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13567 := by decide +kernel

theorem rowEval13567 (x : Key → ℝ) : Integer.Sparse.eval row13567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13567, Integer.Sparse.eval_collectBalanced, rawRowCheck13567]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13485 x
  · exact rowEval13486 x
  · exact rowEval13487 x
  · exact rowEval13488 x
  · exact rowEval13489 x
  · exact rowEval13490 x
  · exact rowEval13491 x
  · exact rowEval13492 x
  · exact rowEval13493 x
  · exact rowEval13494 x
  · exact rowEval13495 x
  · exact rowEval13496 x
  · exact rowEval13497 x
  · exact rowEval13498 x
  · exact rowEval13499 x
  · exact rowEval13500 x
  · exact rowEval13501 x
  · exact rowEval13502 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

theorem entryCheck5_1 : entry5_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_1 k)) := by decide +kernel

theorem rowsSound5_1 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13503 x
  · exact rowEval13504 x
  · exact rowEval13505 x
  · exact rowEval13506 x
  · exact rowEval13507 x
  · exact rowEval13508 x
  · exact rowEval13509 x
  · exact rowEval13510 x
  · exact rowEval13511 x
  · exact rowEval13512 x
  · exact rowEval13513 x
  · exact rowEval13514 x
  · exact rowEval13515 x
  · exact rowEval13516 x
  · exact rowEval13517 x
  · exact rowEval13518 x
  · exact rowEval13519 x
  · exact rowEval13520 x

theorem entryEval5_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_1 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck5_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_1]

theorem entryCheck5_2 : entry5_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_2 k)) := by decide +kernel

theorem rowsSound5_2 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13521 x
  · exact rowEval13522 x
  · exact rowEval13523 x
  · exact rowEval13524 x
  · exact rowEval13525 x
  · exact rowEval13526 x
  · exact rowEval13527 x
  · exact rowEval13528 x
  · exact rowEval13529 x
  · exact rowEval13530 x
  · exact rowEval13531 x
  · exact rowEval13532 x
  · exact rowEval13533 x
  · exact rowEval13534 x
  · exact rowEval13535 x
  · exact rowEval13536 x
  · exact rowEval13537 x
  · exact rowEval13538 x

theorem entryEval5_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_2 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck5_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_2]

theorem entryCheck5_3 : entry5_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_3 k)) := by decide +kernel

theorem rowsSound5_3 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13539 x
  · exact rowEval13540 x
  · exact rowEval13541 x
  · exact rowEval13542 x
  · exact rowEval13543 x
  · exact rowEval13544 x
  · exact rowEval13545 x
  · exact rowEval13546 x
  · exact rowEval13547 x
  · exact rowEval13548 x
  · exact rowEval13549 x
  · exact rowEval13550 x
  · exact rowEval13551 x
  · exact rowEval13552 x
  · exact rowEval13553 x
  · exact rowEval13554 x
  · exact rowEval13555 x
  · exact rowEval13556 x

theorem entryEval5_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_3 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck5_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_3]

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13557 x
  · exact rowEval13558 x
  · exact rowEval13559 x
  · exact rowEval13560 x
  · exact rowEval13561 x
  · exact rowEval13562 x
  · exact rowEval13563 x
  · exact rowEval13564 x
  · exact rowEval13565 x
  · exact rowEval13566 x
  · exact rowEval13567 x
  · exact rowEval13568 x
  · exact rowEval13569 x
  · exact rowEval13570 x
  · exact rowEval13571 x
  · exact rowEval13572 x
  · exact rowEval13573 x
  · exact rowEval13574 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

theorem entryCheck5_5 : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

theorem rowsSound5_5 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13575 x
  · exact rowEval13576 x
  · exact rowEval13577 x
  · exact rowEval13578 x
  · exact rowEval13579 x
  · exact rowEval13580 x
  · exact rowEval13581 x
  · exact rowEval13582 x
  · exact rowEval13583 x
  · exact rowEval13584 x
  · exact rowEval13585 x
  · exact rowEval13586 x
  · exact rowEval13587 x
  · exact rowEval13588 x
  · exact rowEval13589 x
  · exact rowEval13590 x
  · exact rowEval13591 x
  · exact rowEval13592 x

theorem entryEval5_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_5 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck5_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval13895 x
  · exact rowEval13896 x
  · exact rowEval13897 x
  · exact rowEval13898 x
  · exact rowEval13899 x
  · exact rowEval13900 x
  · exact rowEval13901 x
  · exact rowEval13902 x
  · exact rowEval13903 x
  · exact rowEval13904 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14025 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14025 := by decide +kernel

theorem rowCheck14025 : row14025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14025 := by decide +kernel

theorem rowEval14025 (x : Key → ℝ) : Integer.Sparse.eval row14025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14025, Integer.Sparse.eval_collectBalanced, rawRowCheck14025]

theorem rawRowCheck14026 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14026 := by decide +kernel

theorem rowCheck14026 : row14026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14026 := by decide +kernel

theorem rowEval14026 (x : Key → ℝ) : Integer.Sparse.eval row14026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14026, Integer.Sparse.eval_collectBalanced, rawRowCheck14026]

theorem rawRowCheck14027 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14027 := by decide +kernel

theorem rowCheck14027 : row14027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14027 := by decide +kernel

theorem rowEval14027 (x : Key → ℝ) : Integer.Sparse.eval row14027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14027, Integer.Sparse.eval_collectBalanced, rawRowCheck14027]

theorem rawRowCheck14028 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14028 := by decide +kernel

theorem rowCheck14028 : row14028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14028 := by decide +kernel

theorem rowEval14028 (x : Key → ℝ) : Integer.Sparse.eval row14028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14028, Integer.Sparse.eval_collectBalanced, rawRowCheck14028]

theorem rawRowCheck14029 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14029 := by decide +kernel

theorem rowCheck14029 : row14029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14029 := by decide +kernel

theorem rowEval14029 (x : Key → ℝ) : Integer.Sparse.eval row14029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14029, Integer.Sparse.eval_collectBalanced, rawRowCheck14029]

theorem rawRowCheck14030 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14030 := by decide +kernel

theorem rowCheck14030 : row14030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14030 := by decide +kernel

theorem rowEval14030 (x : Key → ℝ) : Integer.Sparse.eval row14030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14030, Integer.Sparse.eval_collectBalanced, rawRowCheck14030]

theorem rawRowCheck14031 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14031 := by decide +kernel

theorem rowCheck14031 : row14031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14031 := by decide +kernel

theorem rowEval14031 (x : Key → ℝ) : Integer.Sparse.eval row14031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14031, Integer.Sparse.eval_collectBalanced, rawRowCheck14031]

theorem rawRowCheck14032 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14032 := by decide +kernel

theorem rowCheck14032 : row14032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14032 := by decide +kernel

theorem rowEval14032 (x : Key → ℝ) : Integer.Sparse.eval row14032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14032, Integer.Sparse.eval_collectBalanced, rawRowCheck14032]

theorem rawRowCheck14033 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14033 := by decide +kernel

theorem rowCheck14033 : row14033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14033 := by decide +kernel

theorem rowEval14033 (x : Key → ℝ) : Integer.Sparse.eval row14033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14033, Integer.Sparse.eval_collectBalanced, rawRowCheck14033]

theorem rawRowCheck14034 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14034 := by decide +kernel

theorem rowCheck14034 : row14034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14034 := by decide +kernel

theorem rowEval14034 (x : Key → ℝ) : Integer.Sparse.eval row14034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14034, Integer.Sparse.eval_collectBalanced, rawRowCheck14034]

theorem rawRowCheck14035 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14035 := by decide +kernel

theorem rowCheck14035 : row14035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14035 := by decide +kernel

theorem rowEval14035 (x : Key → ℝ) : Integer.Sparse.eval row14035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14035, Integer.Sparse.eval_collectBalanced, rawRowCheck14035]

theorem rawRowCheck14036 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14036 := by decide +kernel

theorem rowCheck14036 : row14036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14036 := by decide +kernel

theorem rowEval14036 (x : Key → ℝ) : Integer.Sparse.eval row14036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14036, Integer.Sparse.eval_collectBalanced, rawRowCheck14036]

theorem rawRowCheck14037 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14037 := by decide +kernel

theorem rowCheck14037 : row14037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14037 := by decide +kernel

theorem rowEval14037 (x : Key → ℝ) : Integer.Sparse.eval row14037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14037, Integer.Sparse.eval_collectBalanced, rawRowCheck14037]

theorem rawRowCheck14038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14038 := by decide +kernel

theorem rowCheck14038 : row14038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14038 := by decide +kernel

theorem rowEval14038 (x : Key → ℝ) : Integer.Sparse.eval row14038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14038, Integer.Sparse.eval_collectBalanced, rawRowCheck14038]

theorem rawRowCheck14039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14039 := by decide +kernel

theorem rowCheck14039 : row14039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14039 := by decide +kernel

theorem rowEval14039 (x : Key → ℝ) : Integer.Sparse.eval row14039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14039, Integer.Sparse.eval_collectBalanced, rawRowCheck14039]

theorem rawRowCheck14040 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14040 := by decide +kernel

theorem rowCheck14040 : row14040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14040 := by decide +kernel

theorem rowEval14040 (x : Key → ℝ) : Integer.Sparse.eval row14040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14040, Integer.Sparse.eval_collectBalanced, rawRowCheck14040]

theorem rawRowCheck14041 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5 = rawRow14041 := by decide +kernel

theorem rowCheck14041 : row14041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14041 := by decide +kernel

theorem rowEval14041 (x : Key → ℝ) : Integer.Sparse.eval row14041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14041, Integer.Sparse.eval_collectBalanced, rawRowCheck14041]

theorem rawRowCheck14042 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14042 := by decide +kernel

theorem rowCheck14042 : row14042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14042 := by decide +kernel

theorem rowEval14042 (x : Key → ℝ) : Integer.Sparse.eval row14042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14042, Integer.Sparse.eval_collectBalanced, rawRowCheck14042]

theorem rawRowCheck14043 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14043 := by decide +kernel

theorem rowCheck14043 : row14043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14043 := by decide +kernel

theorem rowEval14043 (x : Key → ℝ) : Integer.Sparse.eval row14043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14043, Integer.Sparse.eval_collectBalanced, rawRowCheck14043]

theorem rawRowCheck14044 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14044 := by decide +kernel

theorem rowCheck14044 : row14044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14044 := by decide +kernel

theorem rowEval14044 (x : Key → ℝ) : Integer.Sparse.eval row14044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14044, Integer.Sparse.eval_collectBalanced, rawRowCheck14044]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14025 x
  · exact rowEval14026 x
  · exact rowEval14027 x
  · exact rowEval14028 x
  · exact rowEval14029 x
  · exact rowEval14030 x
  · exact rowEval14031 x
  · exact rowEval14032 x
  · exact rowEval14033 x
  · exact rowEval14034 x
  · exact rowEval14035 x
  · exact rowEval14036 x
  · exact rowEval14037 x
  · exact rowEval14038 x
  · exact rowEval14039 x
  · exact rowEval14040 x
  · exact rowEval14041 x
  · exact rowEval14042 x
  · exact rowEval14043 x
  · exact rowEval14044 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14155 x
  · exact rowEval14156 x
  · exact rowEval14157 x
  · exact rowEval14158 x
  · exact rowEval14159 x
  · exact rowEval14160 x
  · exact rowEval14161 x
  · exact rowEval14162 x
  · exact rowEval14163 x
  · exact rowEval14164 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

theorem entryEvalRow5_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 5 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 5).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval5_0 B hB
  · exact entryEval5_1 B hB
  · exact entryEval5_2 B hB
  · exact entryEval5_3 B hB
  · exact entryEval5_4 B hB
  · exact entryEval5_5 B hB
  · exact (entryEval6_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_5_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_5 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5_e_oai
