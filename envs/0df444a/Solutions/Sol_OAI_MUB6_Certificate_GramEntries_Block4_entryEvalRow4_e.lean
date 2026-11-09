-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:46:07.547062+00:00
-- url     : https://prove2.me/submissions/f8438005-89b1-4091-b1e0-c48e2eb01858

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_4_e

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

theorem rawRowCheck14145 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow14145 := by decide +kernel

theorem rowCheck14145 : row14145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14145 := by decide +kernel

theorem rowEval14145 (x : Key → ℝ) : Integer.Sparse.eval row14145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14145, Integer.Sparse.eval_collectBalanced, rawRowCheck14145]

theorem rawRowCheck14146 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow14146 := by decide +kernel

theorem rowCheck14146 : row14146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14146 := by decide +kernel

theorem rowEval14146 (x : Key → ℝ) : Integer.Sparse.eval row14146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14146, Integer.Sparse.eval_collectBalanced, rawRowCheck14146]

theorem rawRowCheck14147 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow14147 := by decide +kernel

theorem rowCheck14147 : row14147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14147 := by decide +kernel

theorem rowEval14147 (x : Key → ℝ) : Integer.Sparse.eval row14147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14147, Integer.Sparse.eval_collectBalanced, rawRowCheck14147]

theorem rawRowCheck14148 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14148 := by decide +kernel

theorem rowCheck14148 : row14148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14148 := by decide +kernel

theorem rowEval14148 (x : Key → ℝ) : Integer.Sparse.eval row14148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14148, Integer.Sparse.eval_collectBalanced, rawRowCheck14148]

theorem rawRowCheck14149 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14149 := by decide +kernel

theorem rowCheck14149 : row14149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14149 := by decide +kernel

theorem rowEval14149 (x : Key → ℝ) : Integer.Sparse.eval row14149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14149, Integer.Sparse.eval_collectBalanced, rawRowCheck14149]

theorem rawRowCheck14150 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14150 := by decide +kernel

theorem rowCheck14150 : row14150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14150 := by decide +kernel

theorem rowEval14150 (x : Key → ℝ) : Integer.Sparse.eval row14150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14150, Integer.Sparse.eval_collectBalanced, rawRowCheck14150]

theorem rawRowCheck14151 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow14151 := by decide +kernel

theorem rowCheck14151 : row14151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14151 := by decide +kernel

theorem rowEval14151 (x : Key → ℝ) : Integer.Sparse.eval row14151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14151, Integer.Sparse.eval_collectBalanced, rawRowCheck14151]

theorem rawRowCheck14152 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow14152 := by decide +kernel

theorem rowCheck14152 : row14152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14152 := by decide +kernel

theorem rowEval14152 (x : Key → ℝ) : Integer.Sparse.eval row14152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14152, Integer.Sparse.eval_collectBalanced, rawRowCheck14152]

theorem rawRowCheck14153 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow14153 := by decide +kernel

theorem rowCheck14153 : row14153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14153 := by decide +kernel

theorem rowEval14153 (x : Key → ℝ) : Integer.Sparse.eval row14153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14153, Integer.Sparse.eval_collectBalanced, rawRowCheck14153]

theorem rawRowCheck14154 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow14154 := by decide +kernel

theorem rowCheck14154 : row14154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14154 := by decide +kernel

theorem rowEval14154 (x : Key → ℝ) : Integer.Sparse.eval row14154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14154, Integer.Sparse.eval_collectBalanced, rawRowCheck14154]

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

theorem rawRowCheck14681 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14681 := by decide +kernel

theorem rowCheck14681 : row14681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14681 := by decide +kernel

theorem rowEval14681 (x : Key → ℝ) : Integer.Sparse.eval row14681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14681, Integer.Sparse.eval_collectBalanced, rawRowCheck14681]

theorem rawRowCheck14682 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14682 := by decide +kernel

theorem rowCheck14682 : row14682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14682 := by decide +kernel

theorem rowEval14682 (x : Key → ℝ) : Integer.Sparse.eval row14682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14682, Integer.Sparse.eval_collectBalanced, rawRowCheck14682]

theorem rawRowCheck14683 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14683 := by decide +kernel

theorem rowCheck14683 : row14683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14683 := by decide +kernel

theorem rowEval14683 (x : Key → ℝ) : Integer.Sparse.eval row14683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14683, Integer.Sparse.eval_collectBalanced, rawRowCheck14683]

theorem rawRowCheck14684 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14684 := by decide +kernel

theorem rowCheck14684 : row14684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14684 := by decide +kernel

theorem rowEval14684 (x : Key → ℝ) : Integer.Sparse.eval row14684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14684, Integer.Sparse.eval_collectBalanced, rawRowCheck14684]

theorem rawRowCheck14685 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4 = rawRow14685 := by decide +kernel

theorem rowCheck14685 : row14685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14685 := by decide +kernel

theorem rowEval14685 (x : Key → ℝ) : Integer.Sparse.eval row14685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14685, Integer.Sparse.eval_collectBalanced, rawRowCheck14685]

theorem rawRowCheck14686 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4 = rawRow14686 := by decide +kernel

theorem rowCheck14686 : row14686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14686 := by decide +kernel

theorem rowEval14686 (x : Key → ℝ) : Integer.Sparse.eval row14686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14686, Integer.Sparse.eval_collectBalanced, rawRowCheck14686]

theorem rawRowCheck14687 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4 = rawRow14687 := by decide +kernel

theorem rowCheck14687 : row14687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14687 := by decide +kernel

theorem rowEval14687 (x : Key → ℝ) : Integer.Sparse.eval row14687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14687, Integer.Sparse.eval_collectBalanced, rawRowCheck14687]

theorem rawRowCheck14688 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4 = rawRow14688 := by decide +kernel

theorem rowCheck14688 : row14688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14688 := by decide +kernel

theorem rowEval14688 (x : Key → ℝ) : Integer.Sparse.eval row14688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14688, Integer.Sparse.eval_collectBalanced, rawRowCheck14688]

theorem rawRowCheck14689 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4 = rawRow14689 := by decide +kernel

theorem rowCheck14689 : row14689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14689 := by decide +kernel

theorem rowEval14689 (x : Key → ℝ) : Integer.Sparse.eval row14689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14689, Integer.Sparse.eval_collectBalanced, rawRowCheck14689]

theorem rawRowCheck14690 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4 = rawRow14690 := by decide +kernel

theorem rowCheck14690 : row14690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14690 := by decide +kernel

theorem rowEval14690 (x : Key → ℝ) : Integer.Sparse.eval row14690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14690, Integer.Sparse.eval_collectBalanced, rawRowCheck14690]

theorem rawRowCheck14691 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4 = rawRow14691 := by decide +kernel

theorem rowCheck14691 : row14691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14691 := by decide +kernel

theorem rowEval14691 (x : Key → ℝ) : Integer.Sparse.eval row14691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14691, Integer.Sparse.eval_collectBalanced, rawRowCheck14691]

theorem rawRowCheck14692 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4 = rawRow14692 := by decide +kernel

theorem rowCheck14692 : row14692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14692 := by decide +kernel

theorem rowEval14692 (x : Key → ℝ) : Integer.Sparse.eval row14692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14692, Integer.Sparse.eval_collectBalanced, rawRowCheck14692]

theorem rawRowCheck14693 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4 = rawRow14693 := by decide +kernel

theorem rowCheck14693 : row14693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14693 := by decide +kernel

theorem rowEval14693 (x : Key → ℝ) : Integer.Sparse.eval row14693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14693, Integer.Sparse.eval_collectBalanced, rawRowCheck14693]

theorem rawRowCheck14694 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14694 := by decide +kernel

theorem rowCheck14694 : row14694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14694 := by decide +kernel

theorem rowEval14694 (x : Key → ℝ) : Integer.Sparse.eval row14694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14694, Integer.Sparse.eval_collectBalanced, rawRowCheck14694]

theorem rawRowCheck14695 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14695 := by decide +kernel

theorem rowCheck14695 : row14695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14695 := by decide +kernel

theorem rowEval14695 (x : Key → ℝ) : Integer.Sparse.eval row14695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14695, Integer.Sparse.eval_collectBalanced, rawRowCheck14695]

theorem rawRowCheck14696 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14696 := by decide +kernel

theorem rowCheck14696 : row14696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14696 := by decide +kernel

theorem rowEval14696 (x : Key → ℝ) : Integer.Sparse.eval row14696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14696, Integer.Sparse.eval_collectBalanced, rawRowCheck14696]

theorem rawRowCheck14697 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14697 := by decide +kernel

theorem rowCheck14697 : row14697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14697 := by decide +kernel

theorem rowEval14697 (x : Key → ℝ) : Integer.Sparse.eval row14697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14697, Integer.Sparse.eval_collectBalanced, rawRowCheck14697]

theorem rawRowCheck14698 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4 = rawRow14698 := by decide +kernel

theorem rowCheck14698 : row14698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14698 := by decide +kernel

theorem rowEval14698 (x : Key → ℝ) : Integer.Sparse.eval row14698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14698, Integer.Sparse.eval_collectBalanced, rawRowCheck14698]

theorem rawRowCheck14699 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4 = rawRow14699 := by decide +kernel

theorem rowCheck14699 : row14699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14699 := by decide +kernel

theorem rowEval14699 (x : Key → ℝ) : Integer.Sparse.eval row14699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14699, Integer.Sparse.eval_collectBalanced, rawRowCheck14699]

theorem rawRowCheck14700 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4 = rawRow14700 := by decide +kernel

theorem rowCheck14700 : row14700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14700 := by decide +kernel

theorem rowEval14700 (x : Key → ℝ) : Integer.Sparse.eval row14700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck14700, Integer.Sparse.eval_collectBalanced, rawRowCheck14700]

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

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14681 x
  · exact rowEval14682 x
  · exact rowEval14683 x
  · exact rowEval14684 x
  · exact rowEval14685 x
  · exact rowEval14686 x
  · exact rowEval14687 x
  · exact rowEval14688 x
  · exact rowEval14689 x
  · exact rowEval14690 x
  · exact rowEval14691 x
  · exact rowEval14692 x
  · exact rowEval14693 x
  · exact rowEval14694 x
  · exact rowEval14695 x
  · exact rowEval14696 x
  · exact rowEval14697 x
  · exact rowEval14698 x
  · exact rowEval14699 x
  · exact rowEval14700 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

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

theorem rawRowCheck14934 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14934 := by decide +kernel

theorem rowCheck14934 : row14934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14934 := by decide +kernel

theorem rowEval14934 (x : Key → ℝ) : Integer.Sparse.eval row14934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14934, Integer.Sparse.eval_collectBalanced, rawRowCheck14934]

theorem rawRowCheck14935 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14935 := by decide +kernel

theorem rowCheck14935 : row14935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14935 := by decide +kernel

theorem rowEval14935 (x : Key → ℝ) : Integer.Sparse.eval row14935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14935, Integer.Sparse.eval_collectBalanced, rawRowCheck14935]

theorem rawRowCheck14936 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14936 := by decide +kernel

theorem rowCheck14936 : row14936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14936 := by decide +kernel

theorem rowEval14936 (x : Key → ℝ) : Integer.Sparse.eval row14936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14936, Integer.Sparse.eval_collectBalanced, rawRowCheck14936]

theorem rawRowCheck14937 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14937 := by decide +kernel

theorem rowCheck14937 : row14937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14937 := by decide +kernel

theorem rowEval14937 (x : Key → ℝ) : Integer.Sparse.eval row14937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14937, Integer.Sparse.eval_collectBalanced, rawRowCheck14937]

theorem rawRowCheck14938 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14938 := by decide +kernel

theorem rowCheck14938 : row14938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14938 := by decide +kernel

theorem rowEval14938 (x : Key → ℝ) : Integer.Sparse.eval row14938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14938, Integer.Sparse.eval_collectBalanced, rawRowCheck14938]

theorem rawRowCheck14939 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14939 := by decide +kernel

theorem rowCheck14939 : row14939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14939 := by decide +kernel

theorem rowEval14939 (x : Key → ℝ) : Integer.Sparse.eval row14939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14939, Integer.Sparse.eval_collectBalanced, rawRowCheck14939]

theorem rawRowCheck14940 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4 = rawRow14940 := by decide +kernel

theorem rowCheck14940 : row14940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14940 := by decide +kernel

theorem rowEval14940 (x : Key → ℝ) : Integer.Sparse.eval row14940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14940, Integer.Sparse.eval_collectBalanced, rawRowCheck14940]

theorem rawRowCheck14941 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4 = rawRow14941 := by decide +kernel

theorem rowCheck14941 : row14941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14941 := by decide +kernel

theorem rowEval14941 (x : Key → ℝ) : Integer.Sparse.eval row14941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14941, Integer.Sparse.eval_collectBalanced, rawRowCheck14941]

theorem rawRowCheck14942 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4 = rawRow14942 := by decide +kernel

theorem rowCheck14942 : row14942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14942 := by decide +kernel

theorem rowEval14942 (x : Key → ℝ) : Integer.Sparse.eval row14942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14942, Integer.Sparse.eval_collectBalanced, rawRowCheck14942]

theorem rawRowCheck14943 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14943 := by decide +kernel

theorem rowCheck14943 : row14943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14943 := by decide +kernel

theorem rowEval14943 (x : Key → ℝ) : Integer.Sparse.eval row14943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14943, Integer.Sparse.eval_collectBalanced, rawRowCheck14943]

theorem rawRowCheck14944 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14944 := by decide +kernel

theorem rowCheck14944 : row14944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14944 := by decide +kernel

theorem rowEval14944 (x : Key → ℝ) : Integer.Sparse.eval row14944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14944, Integer.Sparse.eval_collectBalanced, rawRowCheck14944]

theorem rawRowCheck14945 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14945 := by decide +kernel

theorem rowCheck14945 : row14945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14945 := by decide +kernel

theorem rowEval14945 (x : Key → ℝ) : Integer.Sparse.eval row14945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14945, Integer.Sparse.eval_collectBalanced, rawRowCheck14945]

theorem rawRowCheck14946 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14946 := by decide +kernel

theorem rowCheck14946 : row14946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14946 := by decide +kernel

theorem rowEval14946 (x : Key → ℝ) : Integer.Sparse.eval row14946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14946, Integer.Sparse.eval_collectBalanced, rawRowCheck14946]

theorem rawRowCheck14947 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14947 := by decide +kernel

theorem rowCheck14947 : row14947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14947 := by decide +kernel

theorem rowEval14947 (x : Key → ℝ) : Integer.Sparse.eval row14947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14947, Integer.Sparse.eval_collectBalanced, rawRowCheck14947]

theorem rawRowCheck14948 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14948 := by decide +kernel

theorem rowCheck14948 : row14948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14948 := by decide +kernel

theorem rowEval14948 (x : Key → ℝ) : Integer.Sparse.eval row14948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14948, Integer.Sparse.eval_collectBalanced, rawRowCheck14948]

theorem rawRowCheck14949 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14949 := by decide +kernel

theorem rowCheck14949 : row14949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14949 := by decide +kernel

theorem rowEval14949 (x : Key → ℝ) : Integer.Sparse.eval row14949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14949, Integer.Sparse.eval_collectBalanced, rawRowCheck14949]

theorem rawRowCheck14950 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14950 := by decide +kernel

theorem rowCheck14950 : row14950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14950 := by decide +kernel

theorem rowEval14950 (x : Key → ℝ) : Integer.Sparse.eval row14950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14950, Integer.Sparse.eval_collectBalanced, rawRowCheck14950]

theorem rawRowCheck14951 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14951 := by decide +kernel

theorem rowCheck14951 : row14951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14951 := by decide +kernel

theorem rowEval14951 (x : Key → ℝ) : Integer.Sparse.eval row14951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14951, Integer.Sparse.eval_collectBalanced, rawRowCheck14951]

theorem rawRowCheck14952 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14952 := by decide +kernel

theorem rowCheck14952 : row14952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14952 := by decide +kernel

theorem rowEval14952 (x : Key → ℝ) : Integer.Sparse.eval row14952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14952, Integer.Sparse.eval_collectBalanced, rawRowCheck14952]

theorem rawRowCheck14953 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14953 := by decide +kernel

theorem rowCheck14953 : row14953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14953 := by decide +kernel

theorem rowEval14953 (x : Key → ℝ) : Integer.Sparse.eval row14953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14953, Integer.Sparse.eval_collectBalanced, rawRowCheck14953]

theorem rawRowCheck14954 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14954 := by decide +kernel

theorem rowCheck14954 : row14954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14954 := by decide +kernel

theorem rowEval14954 (x : Key → ℝ) : Integer.Sparse.eval row14954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14954, Integer.Sparse.eval_collectBalanced, rawRowCheck14954]

theorem rawRowCheck14955 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14955 := by decide +kernel

theorem rowCheck14955 : row14955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14955 := by decide +kernel

theorem rowEval14955 (x : Key → ℝ) : Integer.Sparse.eval row14955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14955, Integer.Sparse.eval_collectBalanced, rawRowCheck14955]

theorem rawRowCheck14956 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14956 := by decide +kernel

theorem rowCheck14956 : row14956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14956 := by decide +kernel

theorem rowEval14956 (x : Key → ℝ) : Integer.Sparse.eval row14956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14956, Integer.Sparse.eval_collectBalanced, rawRowCheck14956]

theorem rawRowCheck14957 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14957 := by decide +kernel

theorem rowCheck14957 : row14957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14957 := by decide +kernel

theorem rowEval14957 (x : Key → ℝ) : Integer.Sparse.eval row14957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14957, Integer.Sparse.eval_collectBalanced, rawRowCheck14957]

theorem rawRowCheck14958 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14958 := by decide +kernel

theorem rowCheck14958 : row14958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14958 := by decide +kernel

theorem rowEval14958 (x : Key → ℝ) : Integer.Sparse.eval row14958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14958, Integer.Sparse.eval_collectBalanced, rawRowCheck14958]

theorem rawRowCheck14959 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14959 := by decide +kernel

theorem rowCheck14959 : row14959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14959 := by decide +kernel

theorem rowEval14959 (x : Key → ℝ) : Integer.Sparse.eval row14959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14959, Integer.Sparse.eval_collectBalanced, rawRowCheck14959]

theorem rawRowCheck14960 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14960 := by decide +kernel

theorem rowCheck14960 : row14960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14960 := by decide +kernel

theorem rowEval14960 (x : Key → ℝ) : Integer.Sparse.eval row14960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14960, Integer.Sparse.eval_collectBalanced, rawRowCheck14960]

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

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14934 x
  · exact rowEval14935 x
  · exact rowEval14936 x
  · exact rowEval14937 x
  · exact rowEval14938 x
  · exact rowEval14939 x
  · exact rowEval14940 x
  · exact rowEval14941 x
  · exact rowEval14942 x
  · exact rowEval14943 x
  · exact rowEval14944 x
  · exact rowEval14945 x
  · exact rowEval14946 x
  · exact rowEval14947 x
  · exact rowEval14948 x
  · exact rowEval14949 x
  · exact rowEval14950 x
  · exact rowEval14951 x
  · exact rowEval14952 x
  · exact rowEval14953 x
  · exact rowEval14954 x
  · exact rowEval14955 x
  · exact rowEval14956 x
  · exact rowEval14957 x
  · exact rowEval14958 x
  · exact rowEval14959 x
  · exact rowEval14960 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

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

theorem rawRowCheck13885 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4 = rawRow13885 := by decide +kernel

theorem rowCheck13885 : row13885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13885 := by decide +kernel

theorem rowEval13885 (x : Key → ℝ) : Integer.Sparse.eval row13885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13885, Integer.Sparse.eval_collectBalanced, rawRowCheck13885]

theorem rawRowCheck13886 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4 = rawRow13886 := by decide +kernel

theorem rowCheck13886 : row13886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13886 := by decide +kernel

theorem rowEval13886 (x : Key → ℝ) : Integer.Sparse.eval row13886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13886, Integer.Sparse.eval_collectBalanced, rawRowCheck13886]

theorem rawRowCheck13887 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4 = rawRow13887 := by decide +kernel

theorem rowCheck13887 : row13887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13887 := by decide +kernel

theorem rowEval13887 (x : Key → ℝ) : Integer.Sparse.eval row13887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13887, Integer.Sparse.eval_collectBalanced, rawRowCheck13887]

theorem rawRowCheck13888 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13888 := by decide +kernel

theorem rowCheck13888 : row13888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13888 := by decide +kernel

theorem rowEval13888 (x : Key → ℝ) : Integer.Sparse.eval row13888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13888, Integer.Sparse.eval_collectBalanced, rawRowCheck13888]

theorem rawRowCheck13889 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13889 := by decide +kernel

theorem rowCheck13889 : row13889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13889 := by decide +kernel

theorem rowEval13889 (x : Key → ℝ) : Integer.Sparse.eval row13889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13889, Integer.Sparse.eval_collectBalanced, rawRowCheck13889]

theorem rawRowCheck13890 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13890 := by decide +kernel

theorem rowCheck13890 : row13890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13890 := by decide +kernel

theorem rowEval13890 (x : Key → ℝ) : Integer.Sparse.eval row13890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13890, Integer.Sparse.eval_collectBalanced, rawRowCheck13890]

theorem rawRowCheck13891 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow13891 := by decide +kernel

theorem rowCheck13891 : row13891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13891 := by decide +kernel

theorem rowEval13891 (x : Key → ℝ) : Integer.Sparse.eval row13891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13891, Integer.Sparse.eval_collectBalanced, rawRowCheck13891]

theorem rawRowCheck13892 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow13892 := by decide +kernel

theorem rowCheck13892 : row13892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13892 := by decide +kernel

theorem rowEval13892 (x : Key → ℝ) : Integer.Sparse.eval row13892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13892, Integer.Sparse.eval_collectBalanced, rawRowCheck13892]

theorem rawRowCheck13893 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow13893 := by decide +kernel

theorem rowCheck13893 : row13893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13893 := by decide +kernel

theorem rowEval13893 (x : Key → ℝ) : Integer.Sparse.eval row13893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13893, Integer.Sparse.eval_collectBalanced, rawRowCheck13893]

theorem rawRowCheck13894 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow13894 := by decide +kernel

theorem rowCheck13894 : row13894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13894 := by decide +kernel

theorem rowEval13894 (x : Key → ℝ) : Integer.Sparse.eval row13894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13894, Integer.Sparse.eval_collectBalanced, rawRowCheck13894]

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

theorem rawRowCheck16779 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4 = rawRow16779 := by decide +kernel

theorem rowCheck16779 : row16779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16779 := by decide +kernel

theorem rowEval16779 (x : Key → ℝ) : Integer.Sparse.eval row16779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16779, Integer.Sparse.eval_collectBalanced, rawRowCheck16779]

theorem rawRowCheck16780 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4 = rawRow16780 := by decide +kernel

theorem rowCheck16780 : row16780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16780 := by decide +kernel

theorem rowEval16780 (x : Key → ℝ) : Integer.Sparse.eval row16780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16780, Integer.Sparse.eval_collectBalanced, rawRowCheck16780]

theorem rawRowCheck16781 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4 = rawRow16781 := by decide +kernel

theorem rowCheck16781 : row16781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16781 := by decide +kernel

theorem rowEval16781 (x : Key → ℝ) : Integer.Sparse.eval row16781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16781, Integer.Sparse.eval_collectBalanced, rawRowCheck16781]

theorem rawRowCheck16782 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16782 := by decide +kernel

theorem rowCheck16782 : row16782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16782 := by decide +kernel

theorem rowEval16782 (x : Key → ℝ) : Integer.Sparse.eval row16782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16782, Integer.Sparse.eval_collectBalanced, rawRowCheck16782]

theorem rawRowCheck16783 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16783 := by decide +kernel

theorem rowCheck16783 : row16783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16783 := by decide +kernel

theorem rowEval16783 (x : Key → ℝ) : Integer.Sparse.eval row16783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16783, Integer.Sparse.eval_collectBalanced, rawRowCheck16783]

theorem rawRowCheck16784 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16784 := by decide +kernel

theorem rowCheck16784 : row16784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16784 := by decide +kernel

theorem rowEval16784 (x : Key → ℝ) : Integer.Sparse.eval row16784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16784, Integer.Sparse.eval_collectBalanced, rawRowCheck16784]

theorem rawRowCheck16785 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16785 := by decide +kernel

theorem rowCheck16785 : row16785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16785 := by decide +kernel

theorem rowEval16785 (x : Key → ℝ) : Integer.Sparse.eval row16785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16785, Integer.Sparse.eval_collectBalanced, rawRowCheck16785]

theorem rawRowCheck16786 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16786 := by decide +kernel

theorem rowCheck16786 : row16786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16786 := by decide +kernel

theorem rowEval16786 (x : Key → ℝ) : Integer.Sparse.eval row16786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16786, Integer.Sparse.eval_collectBalanced, rawRowCheck16786]

theorem rawRowCheck16787 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16787 := by decide +kernel

theorem rowCheck16787 : row16787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16787 := by decide +kernel

theorem rowEval16787 (x : Key → ℝ) : Integer.Sparse.eval row16787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16787, Integer.Sparse.eval_collectBalanced, rawRowCheck16787]

theorem rawRowCheck16788 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow16788 := by decide +kernel

theorem rowCheck16788 : row16788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16788 := by decide +kernel

theorem rowEval16788 (x : Key → ℝ) : Integer.Sparse.eval row16788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16788, Integer.Sparse.eval_collectBalanced, rawRowCheck16788]

theorem rawRowCheck16789 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow16789 := by decide +kernel

theorem rowCheck16789 : row16789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16789 := by decide +kernel

theorem rowEval16789 (x : Key → ℝ) : Integer.Sparse.eval row16789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16789, Integer.Sparse.eval_collectBalanced, rawRowCheck16789]

theorem rawRowCheck16790 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow16790 := by decide +kernel

theorem rowCheck16790 : row16790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16790 := by decide +kernel

theorem rowEval16790 (x : Key → ℝ) : Integer.Sparse.eval row16790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16790, Integer.Sparse.eval_collectBalanced, rawRowCheck16790]

theorem rawRowCheck16791 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow16791 := by decide +kernel

theorem rowCheck16791 : row16791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16791 := by decide +kernel

theorem rowEval16791 (x : Key → ℝ) : Integer.Sparse.eval row16791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16791, Integer.Sparse.eval_collectBalanced, rawRowCheck16791]

theorem rawRowCheck16792 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow16792 := by decide +kernel

theorem rowCheck16792 : row16792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16792 := by decide +kernel

theorem rowEval16792 (x : Key → ℝ) : Integer.Sparse.eval row16792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16792, Integer.Sparse.eval_collectBalanced, rawRowCheck16792]

theorem rawRowCheck16793 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow16793 := by decide +kernel

theorem rowCheck16793 : row16793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16793 := by decide +kernel

theorem rowEval16793 (x : Key → ℝ) : Integer.Sparse.eval row16793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16793, Integer.Sparse.eval_collectBalanced, rawRowCheck16793]

theorem rawRowCheck16794 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow16794 := by decide +kernel

theorem rowCheck16794 : row16794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16794 := by decide +kernel

theorem rowEval16794 (x : Key → ℝ) : Integer.Sparse.eval row16794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16794, Integer.Sparse.eval_collectBalanced, rawRowCheck16794]

theorem rawRowCheck16795 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow16795 := by decide +kernel

theorem rowCheck16795 : row16795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16795 := by decide +kernel

theorem rowEval16795 (x : Key → ℝ) : Integer.Sparse.eval row16795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16795, Integer.Sparse.eval_collectBalanced, rawRowCheck16795]

theorem rawRowCheck16796 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow16796 := by decide +kernel

theorem rowCheck16796 : row16796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16796 := by decide +kernel

theorem rowEval16796 (x : Key → ℝ) : Integer.Sparse.eval row16796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16796, Integer.Sparse.eval_collectBalanced, rawRowCheck16796]

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

theorem rawRowCheck17111 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow17111 := by decide +kernel

theorem rowCheck17111 : row17111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17111 := by decide +kernel

theorem rowEval17111 (x : Key → ℝ) : Integer.Sparse.eval row17111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17111, Integer.Sparse.eval_collectBalanced, rawRowCheck17111]

theorem rawRowCheck17112 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow17112 := by decide +kernel

theorem rowCheck17112 : row17112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17112 := by decide +kernel

theorem rowEval17112 (x : Key → ℝ) : Integer.Sparse.eval row17112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17112, Integer.Sparse.eval_collectBalanced, rawRowCheck17112]

theorem rawRowCheck17113 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow17113 := by decide +kernel

theorem rowCheck17113 : row17113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17113 := by decide +kernel

theorem rowEval17113 (x : Key → ℝ) : Integer.Sparse.eval row17113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17113, Integer.Sparse.eval_collectBalanced, rawRowCheck17113]

theorem rawRowCheck17114 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow17114 := by decide +kernel

theorem rowCheck17114 : row17114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17114 := by decide +kernel

theorem rowEval17114 (x : Key → ℝ) : Integer.Sparse.eval row17114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17114, Integer.Sparse.eval_collectBalanced, rawRowCheck17114]

theorem rawRowCheck17115 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow17115 := by decide +kernel

theorem rowCheck17115 : row17115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17115 := by decide +kernel

theorem rowEval17115 (x : Key → ℝ) : Integer.Sparse.eval row17115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17115, Integer.Sparse.eval_collectBalanced, rawRowCheck17115]

theorem rawRowCheck17116 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow17116 := by decide +kernel

theorem rowCheck17116 : row17116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17116 := by decide +kernel

theorem rowEval17116 (x : Key → ℝ) : Integer.Sparse.eval row17116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17116, Integer.Sparse.eval_collectBalanced, rawRowCheck17116]

theorem rawRowCheck17117 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17117 := by decide +kernel

theorem rowCheck17117 : row17117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17117 := by decide +kernel

theorem rowEval17117 (x : Key → ℝ) : Integer.Sparse.eval row17117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17117, Integer.Sparse.eval_collectBalanced, rawRowCheck17117]

theorem rawRowCheck17118 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17118 := by decide +kernel

theorem rowCheck17118 : row17118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17118 := by decide +kernel

theorem rowEval17118 (x : Key → ℝ) : Integer.Sparse.eval row17118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17118, Integer.Sparse.eval_collectBalanced, rawRowCheck17118]

theorem rawRowCheck17119 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17119 := by decide +kernel

theorem rowCheck17119 : row17119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17119 := by decide +kernel

theorem rowEval17119 (x : Key → ℝ) : Integer.Sparse.eval row17119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17119, Integer.Sparse.eval_collectBalanced, rawRowCheck17119]

theorem rawRowCheck17120 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17120 := by decide +kernel

theorem rowCheck17120 : row17120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17120 := by decide +kernel

theorem rowEval17120 (x : Key → ℝ) : Integer.Sparse.eval row17120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17120, Integer.Sparse.eval_collectBalanced, rawRowCheck17120]

theorem rawRowCheck17121 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17121 := by decide +kernel

theorem rowCheck17121 : row17121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17121 := by decide +kernel

theorem rowEval17121 (x : Key → ℝ) : Integer.Sparse.eval row17121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17121, Integer.Sparse.eval_collectBalanced, rawRowCheck17121]

theorem rawRowCheck17122 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17122 := by decide +kernel

theorem rowCheck17122 : row17122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17122 := by decide +kernel

theorem rowEval17122 (x : Key → ℝ) : Integer.Sparse.eval row17122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17122, Integer.Sparse.eval_collectBalanced, rawRowCheck17122]

theorem rawRowCheck17123 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17123 := by decide +kernel

theorem rowCheck17123 : row17123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17123 := by decide +kernel

theorem rowEval17123 (x : Key → ℝ) : Integer.Sparse.eval row17123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17123, Integer.Sparse.eval_collectBalanced, rawRowCheck17123]

theorem rawRowCheck17124 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17124 := by decide +kernel

theorem rowCheck17124 : row17124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17124 := by decide +kernel

theorem rowEval17124 (x : Key → ℝ) : Integer.Sparse.eval row17124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17124, Integer.Sparse.eval_collectBalanced, rawRowCheck17124]

theorem rawRowCheck17125 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17125 := by decide +kernel

theorem rowCheck17125 : row17125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17125 := by decide +kernel

theorem rowEval17125 (x : Key → ℝ) : Integer.Sparse.eval row17125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17125, Integer.Sparse.eval_collectBalanced, rawRowCheck17125]

theorem rawRowCheck17126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17126 := by decide +kernel

theorem rowCheck17126 : row17126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17126 := by decide +kernel

theorem rowEval17126 (x : Key → ℝ) : Integer.Sparse.eval row17126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17126, Integer.Sparse.eval_collectBalanced, rawRowCheck17126]

theorem rawRowCheck17127 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17127 := by decide +kernel

theorem rowCheck17127 : row17127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17127 := by decide +kernel

theorem rowEval17127 (x : Key → ℝ) : Integer.Sparse.eval row17127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17127, Integer.Sparse.eval_collectBalanced, rawRowCheck17127]

theorem rawRowCheck17128 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17128 := by decide +kernel

theorem rowCheck17128 : row17128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17128 := by decide +kernel

theorem rowEval17128 (x : Key → ℝ) : Integer.Sparse.eval row17128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17128, Integer.Sparse.eval_collectBalanced, rawRowCheck17128]

theorem rawRowCheck17129 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17129 := by decide +kernel

theorem rowCheck17129 : row17129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17129 := by decide +kernel

theorem rowEval17129 (x : Key → ℝ) : Integer.Sparse.eval row17129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17129, Integer.Sparse.eval_collectBalanced, rawRowCheck17129]

theorem rawRowCheck17130 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17130 := by decide +kernel

theorem rowCheck17130 : row17130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17130 := by decide +kernel

theorem rowEval17130 (x : Key → ℝ) : Integer.Sparse.eval row17130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17130, Integer.Sparse.eval_collectBalanced, rawRowCheck17130]

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

theorem entryCheck17_4 : entry17_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_4 k)) := by decide +kernel

theorem rowsSound17_4 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval16779 x
  · exact rowEval16780 x
  · exact rowEval16781 x
  · exact rowEval16782 x
  · exact rowEval16783 x
  · exact rowEval16784 x
  · exact rowEval16785 x
  · exact rowEval16786 x
  · exact rowEval16787 x
  · exact rowEval16788 x
  · exact rowEval16789 x
  · exact rowEval16790 x
  · exact rowEval16791 x
  · exact rowEval16792 x
  · exact rowEval16793 x
  · exact rowEval16794 x
  · exact rowEval16795 x
  · exact rowEval16796 x

theorem entryEval17_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_4 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck17_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_4]

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

theorem rawRowCheck17451 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow17451 := by decide +kernel

theorem rowCheck17451 : row17451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17451 := by decide +kernel

theorem rowEval17451 (x : Key → ℝ) : Integer.Sparse.eval row17451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17451, Integer.Sparse.eval_collectBalanced, rawRowCheck17451]

theorem rawRowCheck17452 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow17452 := by decide +kernel

theorem rowCheck17452 : row17452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17452 := by decide +kernel

theorem rowEval17452 (x : Key → ℝ) : Integer.Sparse.eval row17452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17452, Integer.Sparse.eval_collectBalanced, rawRowCheck17452]

theorem rawRowCheck17453 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow17453 := by decide +kernel

theorem rowCheck17453 : row17453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17453 := by decide +kernel

theorem rowEval17453 (x : Key → ℝ) : Integer.Sparse.eval row17453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17453, Integer.Sparse.eval_collectBalanced, rawRowCheck17453]

theorem rawRowCheck17454 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17454 := by decide +kernel

theorem rowCheck17454 : row17454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17454 := by decide +kernel

theorem rowEval17454 (x : Key → ℝ) : Integer.Sparse.eval row17454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17454, Integer.Sparse.eval_collectBalanced, rawRowCheck17454]

theorem rawRowCheck17455 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17455 := by decide +kernel

theorem rowCheck17455 : row17455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17455 := by decide +kernel

theorem rowEval17455 (x : Key → ℝ) : Integer.Sparse.eval row17455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17455, Integer.Sparse.eval_collectBalanced, rawRowCheck17455]

theorem rawRowCheck17456 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17456 := by decide +kernel

theorem rowCheck17456 : row17456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17456 := by decide +kernel

theorem rowEval17456 (x : Key → ℝ) : Integer.Sparse.eval row17456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17456, Integer.Sparse.eval_collectBalanced, rawRowCheck17456]

theorem rawRowCheck17457 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17457 := by decide +kernel

theorem rowCheck17457 : row17457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17457 := by decide +kernel

theorem rowEval17457 (x : Key → ℝ) : Integer.Sparse.eval row17457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17457, Integer.Sparse.eval_collectBalanced, rawRowCheck17457]

theorem rawRowCheck17458 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17458 := by decide +kernel

theorem rowCheck17458 : row17458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17458 := by decide +kernel

theorem rowEval17458 (x : Key → ℝ) : Integer.Sparse.eval row17458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17458, Integer.Sparse.eval_collectBalanced, rawRowCheck17458]

theorem rawRowCheck17459 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17459 := by decide +kernel

theorem rowCheck17459 : row17459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17459 := by decide +kernel

theorem rowEval17459 (x : Key → ℝ) : Integer.Sparse.eval row17459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17459, Integer.Sparse.eval_collectBalanced, rawRowCheck17459]

theorem rawRowCheck17460 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow17460 := by decide +kernel

theorem rowCheck17460 : row17460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17460 := by decide +kernel

theorem rowEval17460 (x : Key → ℝ) : Integer.Sparse.eval row17460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17460, Integer.Sparse.eval_collectBalanced, rawRowCheck17460]

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

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17111 x
  · exact rowEval17112 x
  · exact rowEval17113 x
  · exact rowEval17114 x
  · exact rowEval17115 x
  · exact rowEval17116 x
  · exact rowEval17117 x
  · exact rowEval17118 x
  · exact rowEval17119 x
  · exact rowEval17120 x
  · exact rowEval17121 x
  · exact rowEval17122 x
  · exact rowEval17123 x
  · exact rowEval17124 x
  · exact rowEval17125 x
  · exact rowEval17126 x
  · exact rowEval17127 x
  · exact rowEval17128 x
  · exact rowEval17129 x
  · exact rowEval17130 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

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

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17451 x
  · exact rowEval17452 x
  · exact rowEval17453 x
  · exact rowEval17454 x
  · exact rowEval17455 x
  · exact rowEval17456 x
  · exact rowEval17457 x
  · exact rowEval17458 x
  · exact rowEval17459 x
  · exact rowEval17460 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

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

theorem rawRowCheck17683 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17683 := by decide +kernel

theorem rowCheck17683 : row17683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17683 := by decide +kernel

theorem rowEval17683 (x : Key → ℝ) : Integer.Sparse.eval row17683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17683, Integer.Sparse.eval_collectBalanced, rawRowCheck17683]

theorem rawRowCheck17684 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17684 := by decide +kernel

theorem rowCheck17684 : row17684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17684 := by decide +kernel

theorem rowEval17684 (x : Key → ℝ) : Integer.Sparse.eval row17684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17684, Integer.Sparse.eval_collectBalanced, rawRowCheck17684]

theorem rawRowCheck17685 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17685 := by decide +kernel

theorem rowCheck17685 : row17685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17685 := by decide +kernel

theorem rowEval17685 (x : Key → ℝ) : Integer.Sparse.eval row17685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17685, Integer.Sparse.eval_collectBalanced, rawRowCheck17685]

theorem rawRowCheck17686 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17686 := by decide +kernel

theorem rowCheck17686 : row17686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17686 := by decide +kernel

theorem rowEval17686 (x : Key → ℝ) : Integer.Sparse.eval row17686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17686, Integer.Sparse.eval_collectBalanced, rawRowCheck17686]

theorem rawRowCheck17687 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17687 := by decide +kernel

theorem rowCheck17687 : row17687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17687 := by decide +kernel

theorem rowEval17687 (x : Key → ℝ) : Integer.Sparse.eval row17687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17687, Integer.Sparse.eval_collectBalanced, rawRowCheck17687]

theorem rawRowCheck17688 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17688 := by decide +kernel

theorem rowCheck17688 : row17688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17688 := by decide +kernel

theorem rowEval17688 (x : Key → ℝ) : Integer.Sparse.eval row17688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17688, Integer.Sparse.eval_collectBalanced, rawRowCheck17688]

theorem rawRowCheck17689 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17689 := by decide +kernel

theorem rowCheck17689 : row17689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17689 := by decide +kernel

theorem rowEval17689 (x : Key → ℝ) : Integer.Sparse.eval row17689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17689, Integer.Sparse.eval_collectBalanced, rawRowCheck17689]

theorem rawRowCheck17690 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17690 := by decide +kernel

theorem rowCheck17690 : row17690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17690 := by decide +kernel

theorem rowEval17690 (x : Key → ℝ) : Integer.Sparse.eval row17690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17690, Integer.Sparse.eval_collectBalanced, rawRowCheck17690]

theorem rawRowCheck17691 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17691 := by decide +kernel

theorem rowCheck17691 : row17691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17691 := by decide +kernel

theorem rowEval17691 (x : Key → ℝ) : Integer.Sparse.eval row17691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17691, Integer.Sparse.eval_collectBalanced, rawRowCheck17691]

theorem rawRowCheck17692 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17692 := by decide +kernel

theorem rowCheck17692 : row17692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17692 := by decide +kernel

theorem rowEval17692 (x : Key → ℝ) : Integer.Sparse.eval row17692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17692, Integer.Sparse.eval_collectBalanced, rawRowCheck17692]

theorem rawRowCheck17693 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17693 := by decide +kernel

theorem rowCheck17693 : row17693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17693 := by decide +kernel

theorem rowEval17693 (x : Key → ℝ) : Integer.Sparse.eval row17693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17693, Integer.Sparse.eval_collectBalanced, rawRowCheck17693]

theorem rawRowCheck17694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17694 := by decide +kernel

theorem rowCheck17694 : row17694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17694 := by decide +kernel

theorem rowEval17694 (x : Key → ℝ) : Integer.Sparse.eval row17694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17694, Integer.Sparse.eval_collectBalanced, rawRowCheck17694]

theorem rawRowCheck17695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17695 := by decide +kernel

theorem rowCheck17695 : row17695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17695 := by decide +kernel

theorem rowEval17695 (x : Key → ℝ) : Integer.Sparse.eval row17695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17695, Integer.Sparse.eval_collectBalanced, rawRowCheck17695]

theorem rawRowCheck17696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17696 := by decide +kernel

theorem rowCheck17696 : row17696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17696 := by decide +kernel

theorem rowEval17696 (x : Key → ℝ) : Integer.Sparse.eval row17696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17696, Integer.Sparse.eval_collectBalanced, rawRowCheck17696]

theorem rawRowCheck17697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17697 := by decide +kernel

theorem rowCheck17697 : row17697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17697 := by decide +kernel

theorem rowEval17697 (x : Key → ℝ) : Integer.Sparse.eval row17697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17697, Integer.Sparse.eval_collectBalanced, rawRowCheck17697]

theorem rawRowCheck17698 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow17698 := by decide +kernel

theorem rowCheck17698 : row17698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17698 := by decide +kernel

theorem rowEval17698 (x : Key → ℝ) : Integer.Sparse.eval row17698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17698, Integer.Sparse.eval_collectBalanced, rawRowCheck17698]

theorem rawRowCheck17699 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow17699 := by decide +kernel

theorem rowCheck17699 : row17699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17699 := by decide +kernel

theorem rowEval17699 (x : Key → ℝ) : Integer.Sparse.eval row17699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17699, Integer.Sparse.eval_collectBalanced, rawRowCheck17699]

theorem rawRowCheck17700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow17700 := by decide +kernel

theorem rowCheck17700 : row17700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17700 := by decide +kernel

theorem rowEval17700 (x : Key → ℝ) : Integer.Sparse.eval row17700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17700, Integer.Sparse.eval_collectBalanced, rawRowCheck17700]

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

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17683 x
  · exact rowEval17684 x
  · exact rowEval17685 x
  · exact rowEval17686 x
  · exact rowEval17687 x
  · exact rowEval17688 x
  · exact rowEval17689 x
  · exact rowEval17690 x
  · exact rowEval17691 x
  · exact rowEval17692 x
  · exact rowEval17693 x
  · exact rowEval17694 x
  · exact rowEval17695 x
  · exact rowEval17696 x
  · exact rowEval17697 x
  · exact rowEval17698 x
  · exact rowEval17699 x
  · exact rowEval17700 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

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

theorem rawRowCheck18069 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow18069 := by decide +kernel

theorem rowCheck18069 : row18069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18069 := by decide +kernel

theorem rowEval18069 (x : Key → ℝ) : Integer.Sparse.eval row18069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18069, Integer.Sparse.eval_collectBalanced, rawRowCheck18069]

theorem rawRowCheck18070 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow18070 := by decide +kernel

theorem rowCheck18070 : row18070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18070 := by decide +kernel

theorem rowEval18070 (x : Key → ℝ) : Integer.Sparse.eval row18070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18070, Integer.Sparse.eval_collectBalanced, rawRowCheck18070]

theorem rawRowCheck18071 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow18071 := by decide +kernel

theorem rowCheck18071 : row18071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18071 := by decide +kernel

theorem rowEval18071 (x : Key → ℝ) : Integer.Sparse.eval row18071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18071, Integer.Sparse.eval_collectBalanced, rawRowCheck18071]

theorem rawRowCheck18072 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow18072 := by decide +kernel

theorem rowCheck18072 : row18072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18072 := by decide +kernel

theorem rowEval18072 (x : Key → ℝ) : Integer.Sparse.eval row18072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18072, Integer.Sparse.eval_collectBalanced, rawRowCheck18072]

theorem rawRowCheck18073 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow18073 := by decide +kernel

theorem rowCheck18073 : row18073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18073 := by decide +kernel

theorem rowEval18073 (x : Key → ℝ) : Integer.Sparse.eval row18073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18073, Integer.Sparse.eval_collectBalanced, rawRowCheck18073]

theorem rawRowCheck18074 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow18074 := by decide +kernel

theorem rowCheck18074 : row18074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18074 := by decide +kernel

theorem rowEval18074 (x : Key → ℝ) : Integer.Sparse.eval row18074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18074, Integer.Sparse.eval_collectBalanced, rawRowCheck18074]

theorem rawRowCheck18075 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18075 := by decide +kernel

theorem rowCheck18075 : row18075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18075 := by decide +kernel

theorem rowEval18075 (x : Key → ℝ) : Integer.Sparse.eval row18075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18075, Integer.Sparse.eval_collectBalanced, rawRowCheck18075]

theorem rawRowCheck18076 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18076 := by decide +kernel

theorem rowCheck18076 : row18076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18076 := by decide +kernel

theorem rowEval18076 (x : Key → ℝ) : Integer.Sparse.eval row18076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18076, Integer.Sparse.eval_collectBalanced, rawRowCheck18076]

theorem rawRowCheck18077 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18077 := by decide +kernel

theorem rowCheck18077 : row18077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18077 := by decide +kernel

theorem rowEval18077 (x : Key → ℝ) : Integer.Sparse.eval row18077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18077, Integer.Sparse.eval_collectBalanced, rawRowCheck18077]

theorem rawRowCheck18078 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18078 := by decide +kernel

theorem rowCheck18078 : row18078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18078 := by decide +kernel

theorem rowEval18078 (x : Key → ℝ) : Integer.Sparse.eval row18078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18078, Integer.Sparse.eval_collectBalanced, rawRowCheck18078]

theorem rawRowCheck18079 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18079 := by decide +kernel

theorem rowCheck18079 : row18079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18079 := by decide +kernel

theorem rowEval18079 (x : Key → ℝ) : Integer.Sparse.eval row18079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18079, Integer.Sparse.eval_collectBalanced, rawRowCheck18079]

theorem rawRowCheck18080 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18080 := by decide +kernel

theorem rowCheck18080 : row18080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18080 := by decide +kernel

theorem rowEval18080 (x : Key → ℝ) : Integer.Sparse.eval row18080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18080, Integer.Sparse.eval_collectBalanced, rawRowCheck18080]

theorem rawRowCheck18081 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4 = rawRow18081 := by decide +kernel

theorem rowCheck18081 : row18081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18081 := by decide +kernel

theorem rowEval18081 (x : Key → ℝ) : Integer.Sparse.eval row18081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18081, Integer.Sparse.eval_collectBalanced, rawRowCheck18081]

theorem rawRowCheck18082 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4 = rawRow18082 := by decide +kernel

theorem rowCheck18082 : row18082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18082 := by decide +kernel

theorem rowEval18082 (x : Key → ℝ) : Integer.Sparse.eval row18082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18082, Integer.Sparse.eval_collectBalanced, rawRowCheck18082]

theorem rawRowCheck18083 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4 = rawRow18083 := by decide +kernel

theorem rowCheck18083 : row18083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18083 := by decide +kernel

theorem rowEval18083 (x : Key → ℝ) : Integer.Sparse.eval row18083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18083, Integer.Sparse.eval_collectBalanced, rawRowCheck18083]

theorem rawRowCheck18084 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18084 := by decide +kernel

theorem rowCheck18084 : row18084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18084 := by decide +kernel

theorem rowEval18084 (x : Key → ℝ) : Integer.Sparse.eval row18084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18084, Integer.Sparse.eval_collectBalanced, rawRowCheck18084]

theorem rawRowCheck18085 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow18085 := by decide +kernel

theorem rowCheck18085 : row18085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18085 := by decide +kernel

theorem rowEval18085 (x : Key → ℝ) : Integer.Sparse.eval row18085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck18085, Integer.Sparse.eval_collectBalanced, rawRowCheck18085]

theorem rawRowCheck18086 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow18086 := by decide +kernel

theorem rowCheck18086 : row18086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18086 := by decide +kernel

theorem rowEval18086 (x : Key → ℝ) : Integer.Sparse.eval row18086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18086, Integer.Sparse.eval_collectBalanced, rawRowCheck18086]

theorem rawRowCheck18087 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow18087 := by decide +kernel

theorem rowCheck18087 : row18087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18087 := by decide +kernel

theorem rowEval18087 (x : Key → ℝ) : Integer.Sparse.eval row18087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18087, Integer.Sparse.eval_collectBalanced, rawRowCheck18087]

theorem rawRowCheck18088 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow18088 := by decide +kernel

theorem rowCheck18088 : row18088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18088 := by decide +kernel

theorem rowEval18088 (x : Key → ℝ) : Integer.Sparse.eval row18088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck18088, Integer.Sparse.eval_collectBalanced, rawRowCheck18088]

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

theorem entryCheck21_4 : entry21_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_4 k)) := by decide +kernel

theorem rowsSound21_4 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval18069 x
  · exact rowEval18070 x
  · exact rowEval18071 x
  · exact rowEval18072 x
  · exact rowEval18073 x
  · exact rowEval18074 x
  · exact rowEval18075 x
  · exact rowEval18076 x
  · exact rowEval18077 x
  · exact rowEval18078 x
  · exact rowEval18079 x
  · exact rowEval18080 x
  · exact rowEval18081 x
  · exact rowEval18082 x
  · exact rowEval18083 x
  · exact rowEval18084 x
  · exact rowEval18085 x
  · exact rowEval18086 x
  · exact rowEval18087 x
  · exact rowEval18088 x

theorem entryEval21_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_4 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck21_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_4]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13385 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13385 := by decide +kernel

theorem rowCheck13385 : row13385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13385 := by decide +kernel

theorem rowEval13385 (x : Key → ℝ) : Integer.Sparse.eval row13385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13385, Integer.Sparse.eval_collectBalanced, rawRowCheck13385]

theorem rawRowCheck13386 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13386 := by decide +kernel

theorem rowCheck13386 : row13386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13386 := by decide +kernel

theorem rowEval13386 (x : Key → ℝ) : Integer.Sparse.eval row13386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13386, Integer.Sparse.eval_collectBalanced, rawRowCheck13386]

theorem rawRowCheck13387 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13387 := by decide +kernel

theorem rowCheck13387 : row13387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13387 := by decide +kernel

theorem rowEval13387 (x : Key → ℝ) : Integer.Sparse.eval row13387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13387, Integer.Sparse.eval_collectBalanced, rawRowCheck13387]

theorem rawRowCheck13388 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13388 := by decide +kernel

theorem rowCheck13388 : row13388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13388 := by decide +kernel

theorem rowEval13388 (x : Key → ℝ) : Integer.Sparse.eval row13388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13388, Integer.Sparse.eval_collectBalanced, rawRowCheck13388]

theorem rawRowCheck13389 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13389 := by decide +kernel

theorem rowCheck13389 : row13389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13389 := by decide +kernel

theorem rowEval13389 (x : Key → ℝ) : Integer.Sparse.eval row13389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13389, Integer.Sparse.eval_collectBalanced, rawRowCheck13389]

theorem rawRowCheck13390 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13390 := by decide +kernel

theorem rowCheck13390 : row13390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13390 := by decide +kernel

theorem rowEval13390 (x : Key → ℝ) : Integer.Sparse.eval row13390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13390, Integer.Sparse.eval_collectBalanced, rawRowCheck13390]

theorem rawRowCheck13391 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13391 := by decide +kernel

theorem rowCheck13391 : row13391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13391 := by decide +kernel

theorem rowEval13391 (x : Key → ℝ) : Integer.Sparse.eval row13391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13391, Integer.Sparse.eval_collectBalanced, rawRowCheck13391]

theorem rawRowCheck13392 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13392 := by decide +kernel

theorem rowCheck13392 : row13392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13392 := by decide +kernel

theorem rowEval13392 (x : Key → ℝ) : Integer.Sparse.eval row13392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13392, Integer.Sparse.eval_collectBalanced, rawRowCheck13392]

theorem rawRowCheck13393 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13393 := by decide +kernel

theorem rowCheck13393 : row13393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13393 := by decide +kernel

theorem rowEval13393 (x : Key → ℝ) : Integer.Sparse.eval row13393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13393, Integer.Sparse.eval_collectBalanced, rawRowCheck13393]

theorem rawRowCheck13394 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13394 := by decide +kernel

theorem rowCheck13394 : row13394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13394 := by decide +kernel

theorem rowEval13394 (x : Key → ℝ) : Integer.Sparse.eval row13394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13394, Integer.Sparse.eval_collectBalanced, rawRowCheck13394]

theorem rawRowCheck13395 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13395 := by decide +kernel

theorem rowCheck13395 : row13395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13395 := by decide +kernel

theorem rowEval13395 (x : Key → ℝ) : Integer.Sparse.eval row13395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13395, Integer.Sparse.eval_collectBalanced, rawRowCheck13395]

theorem rawRowCheck13396 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13396 := by decide +kernel

theorem rowCheck13396 : row13396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13396 := by decide +kernel

theorem rowEval13396 (x : Key → ℝ) : Integer.Sparse.eval row13396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13396, Integer.Sparse.eval_collectBalanced, rawRowCheck13396]

theorem rawRowCheck13397 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13397 := by decide +kernel

theorem rowCheck13397 : row13397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13397 := by decide +kernel

theorem rowEval13397 (x : Key → ℝ) : Integer.Sparse.eval row13397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13397, Integer.Sparse.eval_collectBalanced, rawRowCheck13397]

theorem rawRowCheck13398 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13398 := by decide +kernel

theorem rowCheck13398 : row13398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13398 := by decide +kernel

theorem rowEval13398 (x : Key → ℝ) : Integer.Sparse.eval row13398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13398, Integer.Sparse.eval_collectBalanced, rawRowCheck13398]

theorem rawRowCheck13399 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13399 := by decide +kernel

theorem rowCheck13399 : row13399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13399 := by decide +kernel

theorem rowEval13399 (x : Key → ℝ) : Integer.Sparse.eval row13399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13399, Integer.Sparse.eval_collectBalanced, rawRowCheck13399]

theorem rawRowCheck13400 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13400 := by decide +kernel

theorem rowCheck13400 : row13400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13400 := by decide +kernel

theorem rowEval13400 (x : Key → ℝ) : Integer.Sparse.eval row13400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13400, Integer.Sparse.eval_collectBalanced, rawRowCheck13400]

theorem rawRowCheck13401 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13401 := by decide +kernel

theorem rowCheck13401 : row13401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13401 := by decide +kernel

theorem rowEval13401 (x : Key → ℝ) : Integer.Sparse.eval row13401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13401, Integer.Sparse.eval_collectBalanced, rawRowCheck13401]

theorem rawRowCheck13402 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13402 := by decide +kernel

theorem rowCheck13402 : row13402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13402 := by decide +kernel

theorem rowEval13402 (x : Key → ℝ) : Integer.Sparse.eval row13402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13402, Integer.Sparse.eval_collectBalanced, rawRowCheck13402]

theorem rawRowCheck13403 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13403 := by decide +kernel

theorem rowCheck13403 : row13403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13403 := by decide +kernel

theorem rowEval13403 (x : Key → ℝ) : Integer.Sparse.eval row13403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13403, Integer.Sparse.eval_collectBalanced, rawRowCheck13403]

theorem rawRowCheck13404 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13404 := by decide +kernel

theorem rowCheck13404 : row13404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13404 := by decide +kernel

theorem rowEval13404 (x : Key → ℝ) : Integer.Sparse.eval row13404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13404, Integer.Sparse.eval_collectBalanced, rawRowCheck13404]

theorem rawRowCheck13405 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13405 := by decide +kernel

theorem rowCheck13405 : row13405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13405 := by decide +kernel

theorem rowEval13405 (x : Key → ℝ) : Integer.Sparse.eval row13405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13405, Integer.Sparse.eval_collectBalanced, rawRowCheck13405]

theorem rawRowCheck13406 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13406 := by decide +kernel

theorem rowCheck13406 : row13406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13406 := by decide +kernel

theorem rowEval13406 (x : Key → ℝ) : Integer.Sparse.eval row13406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13406, Integer.Sparse.eval_collectBalanced, rawRowCheck13406]

theorem rawRowCheck13407 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13407 := by decide +kernel

theorem rowCheck13407 : row13407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13407 := by decide +kernel

theorem rowEval13407 (x : Key → ℝ) : Integer.Sparse.eval row13407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13407, Integer.Sparse.eval_collectBalanced, rawRowCheck13407]

theorem rawRowCheck13408 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13408 := by decide +kernel

theorem rowCheck13408 : row13408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13408 := by decide +kernel

theorem rowEval13408 (x : Key → ℝ) : Integer.Sparse.eval row13408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13408, Integer.Sparse.eval_collectBalanced, rawRowCheck13408]

theorem rawRowCheck13409 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1 = rawRow13409 := by decide +kernel

theorem rowCheck13409 : row13409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13409 := by decide +kernel

theorem rowEval13409 (x : Key → ℝ) : Integer.Sparse.eval row13409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13409, Integer.Sparse.eval_collectBalanced, rawRowCheck13409]

theorem rawRowCheck13410 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1 = rawRow13410 := by decide +kernel

theorem rowCheck13410 : row13410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13410 := by decide +kernel

theorem rowEval13410 (x : Key → ℝ) : Integer.Sparse.eval row13410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13410, Integer.Sparse.eval_collectBalanced, rawRowCheck13410]

theorem rawRowCheck13411 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1 = rawRow13411 := by decide +kernel

theorem rowCheck13411 : row13411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13411 := by decide +kernel

theorem rowEval13411 (x : Key → ℝ) : Integer.Sparse.eval row13411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13411, Integer.Sparse.eval_collectBalanced, rawRowCheck13411]

theorem rawRowCheck13412 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1 = rawRow13412 := by decide +kernel

theorem rowCheck13412 : row13412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13412 := by decide +kernel

theorem rowEval13412 (x : Key → ℝ) : Integer.Sparse.eval row13412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13412, Integer.Sparse.eval_collectBalanced, rawRowCheck13412]

theorem rawRowCheck13413 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1 = rawRow13413 := by decide +kernel

theorem rowCheck13413 : row13413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13413 := by decide +kernel

theorem rowEval13413 (x : Key → ℝ) : Integer.Sparse.eval row13413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13413, Integer.Sparse.eval_collectBalanced, rawRowCheck13413]

theorem rawRowCheck13414 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1 = rawRow13414 := by decide +kernel

theorem rowCheck13414 : row13414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13414 := by decide +kernel

theorem rowEval13414 (x : Key → ℝ) : Integer.Sparse.eval row13414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck13414, Integer.Sparse.eval_collectBalanced, rawRowCheck13414]

theorem rawRowCheck13415 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1 = rawRow13415 := by decide +kernel

theorem rowCheck13415 : row13415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13415 := by decide +kernel

theorem rowEval13415 (x : Key → ℝ) : Integer.Sparse.eval row13415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13415, Integer.Sparse.eval_collectBalanced, rawRowCheck13415]

theorem rawRowCheck13416 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1 = rawRow13416 := by decide +kernel

theorem rowCheck13416 : row13416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13416 := by decide +kernel

theorem rowEval13416 (x : Key → ℝ) : Integer.Sparse.eval row13416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13416, Integer.Sparse.eval_collectBalanced, rawRowCheck13416]

theorem rawRowCheck13417 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1 = rawRow13417 := by decide +kernel

theorem rowCheck13417 : row13417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13417 := by decide +kernel

theorem rowEval13417 (x : Key → ℝ) : Integer.Sparse.eval row13417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13417, Integer.Sparse.eval_collectBalanced, rawRowCheck13417]

theorem rawRowCheck13418 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13418 := by decide +kernel

theorem rowCheck13418 : row13418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13418 := by decide +kernel

theorem rowEval13418 (x : Key → ℝ) : Integer.Sparse.eval row13418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13418, Integer.Sparse.eval_collectBalanced, rawRowCheck13418]

theorem rawRowCheck13419 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13419 := by decide +kernel

theorem rowCheck13419 : row13419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13419 := by decide +kernel

theorem rowEval13419 (x : Key → ℝ) : Integer.Sparse.eval row13419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13419, Integer.Sparse.eval_collectBalanced, rawRowCheck13419]

theorem rawRowCheck13420 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13420 := by decide +kernel

theorem rowCheck13420 : row13420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13420 := by decide +kernel

theorem rowEval13420 (x : Key → ℝ) : Integer.Sparse.eval row13420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13420, Integer.Sparse.eval_collectBalanced, rawRowCheck13420]

theorem rawRowCheck13421 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13421 := by decide +kernel

theorem rowCheck13421 : row13421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13421 := by decide +kernel

theorem rowEval13421 (x : Key → ℝ) : Integer.Sparse.eval row13421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13421, Integer.Sparse.eval_collectBalanced, rawRowCheck13421]

theorem rawRowCheck13422 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13422 := by decide +kernel

theorem rowCheck13422 : row13422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13422 := by decide +kernel

theorem rowEval13422 (x : Key → ℝ) : Integer.Sparse.eval row13422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13422, Integer.Sparse.eval_collectBalanced, rawRowCheck13422]

theorem rawRowCheck13423 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13423 := by decide +kernel

theorem rowCheck13423 : row13423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13423 := by decide +kernel

theorem rowEval13423 (x : Key → ℝ) : Integer.Sparse.eval row13423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13423, Integer.Sparse.eval_collectBalanced, rawRowCheck13423]

theorem rawRowCheck13424 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13424 := by decide +kernel

theorem rowCheck13424 : row13424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13424 := by decide +kernel

theorem rowEval13424 (x : Key → ℝ) : Integer.Sparse.eval row13424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13424, Integer.Sparse.eval_collectBalanced, rawRowCheck13424]

theorem rawRowCheck13425 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13425 := by decide +kernel

theorem rowCheck13425 : row13425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13425 := by decide +kernel

theorem rowEval13425 (x : Key → ℝ) : Integer.Sparse.eval row13425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13425, Integer.Sparse.eval_collectBalanced, rawRowCheck13425]

theorem rawRowCheck13426 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13426 := by decide +kernel

theorem rowCheck13426 : row13426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13426 := by decide +kernel

theorem rowEval13426 (x : Key → ℝ) : Integer.Sparse.eval row13426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13426, Integer.Sparse.eval_collectBalanced, rawRowCheck13426]

theorem rawRowCheck13427 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13427 := by decide +kernel

theorem rowCheck13427 : row13427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13427 := by decide +kernel

theorem rowEval13427 (x : Key → ℝ) : Integer.Sparse.eval row13427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13427, Integer.Sparse.eval_collectBalanced, rawRowCheck13427]

theorem rawRowCheck13428 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13428 := by decide +kernel

theorem rowCheck13428 : row13428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13428 := by decide +kernel

theorem rowEval13428 (x : Key → ℝ) : Integer.Sparse.eval row13428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13428, Integer.Sparse.eval_collectBalanced, rawRowCheck13428]

theorem rawRowCheck13429 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2 = rawRow13429 := by decide +kernel

theorem rowCheck13429 : row13429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13429 := by decide +kernel

theorem rowEval13429 (x : Key → ℝ) : Integer.Sparse.eval row13429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13429, Integer.Sparse.eval_collectBalanced, rawRowCheck13429]

theorem rawRowCheck13430 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2 = rawRow13430 := by decide +kernel

theorem rowCheck13430 : row13430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13430 := by decide +kernel

theorem rowEval13430 (x : Key → ℝ) : Integer.Sparse.eval row13430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13430, Integer.Sparse.eval_collectBalanced, rawRowCheck13430]

theorem rawRowCheck13431 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2 = rawRow13431 := by decide +kernel

theorem rowCheck13431 : row13431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13431 := by decide +kernel

theorem rowEval13431 (x : Key → ℝ) : Integer.Sparse.eval row13431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13431, Integer.Sparse.eval_collectBalanced, rawRowCheck13431]

theorem rawRowCheck13432 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2 = rawRow13432 := by decide +kernel

theorem rowCheck13432 : row13432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13432 := by decide +kernel

theorem rowEval13432 (x : Key → ℝ) : Integer.Sparse.eval row13432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13432, Integer.Sparse.eval_collectBalanced, rawRowCheck13432]

theorem rawRowCheck13433 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2 = rawRow13433 := by decide +kernel

theorem rowCheck13433 : row13433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13433 := by decide +kernel

theorem rowEval13433 (x : Key → ℝ) : Integer.Sparse.eval row13433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13433, Integer.Sparse.eval_collectBalanced, rawRowCheck13433]

theorem rawRowCheck13434 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2 = rawRow13434 := by decide +kernel

theorem rowCheck13434 : row13434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13434 := by decide +kernel

theorem rowEval13434 (x : Key → ℝ) : Integer.Sparse.eval row13434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck13434, Integer.Sparse.eval_collectBalanced, rawRowCheck13434]

theorem rawRowCheck13435 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2 = rawRow13435 := by decide +kernel

theorem rowCheck13435 : row13435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13435 := by decide +kernel

theorem rowEval13435 (x : Key → ℝ) : Integer.Sparse.eval row13435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13435, Integer.Sparse.eval_collectBalanced, rawRowCheck13435]

theorem rawRowCheck13436 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2 = rawRow13436 := by decide +kernel

theorem rowCheck13436 : row13436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13436 := by decide +kernel

theorem rowEval13436 (x : Key → ℝ) : Integer.Sparse.eval row13436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13436, Integer.Sparse.eval_collectBalanced, rawRowCheck13436]

theorem rawRowCheck13437 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2 = rawRow13437 := by decide +kernel

theorem rowCheck13437 : row13437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13437 := by decide +kernel

theorem rowEval13437 (x : Key → ℝ) : Integer.Sparse.eval row13437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13437, Integer.Sparse.eval_collectBalanced, rawRowCheck13437]

theorem rawRowCheck13438 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13438 := by decide +kernel

theorem rowCheck13438 : row13438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13438 := by decide +kernel

theorem rowEval13438 (x : Key → ℝ) : Integer.Sparse.eval row13438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13438, Integer.Sparse.eval_collectBalanced, rawRowCheck13438]

theorem rawRowCheck13439 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13439 := by decide +kernel

theorem rowCheck13439 : row13439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13439 := by decide +kernel

theorem rowEval13439 (x : Key → ℝ) : Integer.Sparse.eval row13439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13439, Integer.Sparse.eval_collectBalanced, rawRowCheck13439]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck13440 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13440 := by decide +kernel

theorem rowCheck13440 : row13440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13440 := by decide +kernel

theorem rowEval13440 (x : Key → ℝ) : Integer.Sparse.eval row13440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13440, Integer.Sparse.eval_collectBalanced, rawRowCheck13440]

theorem rawRowCheck13441 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13441 := by decide +kernel

theorem rowCheck13441 : row13441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13441 := by decide +kernel

theorem rowEval13441 (x : Key → ℝ) : Integer.Sparse.eval row13441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13441, Integer.Sparse.eval_collectBalanced, rawRowCheck13441]

theorem rawRowCheck13442 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13442 := by decide +kernel

theorem rowCheck13442 : row13442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13442 := by decide +kernel

theorem rowEval13442 (x : Key → ℝ) : Integer.Sparse.eval row13442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13442, Integer.Sparse.eval_collectBalanced, rawRowCheck13442]

theorem rawRowCheck13443 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13443 := by decide +kernel

theorem rowCheck13443 : row13443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13443 := by decide +kernel

theorem rowEval13443 (x : Key → ℝ) : Integer.Sparse.eval row13443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13443, Integer.Sparse.eval_collectBalanced, rawRowCheck13443]

theorem rawRowCheck13444 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13444 := by decide +kernel

theorem rowCheck13444 : row13444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13444 := by decide +kernel

theorem rowEval13444 (x : Key → ℝ) : Integer.Sparse.eval row13444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13444, Integer.Sparse.eval_collectBalanced, rawRowCheck13444]

theorem rawRowCheck13445 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13445 := by decide +kernel

theorem rowCheck13445 : row13445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13445 := by decide +kernel

theorem rowEval13445 (x : Key → ℝ) : Integer.Sparse.eval row13445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13445, Integer.Sparse.eval_collectBalanced, rawRowCheck13445]

theorem rawRowCheck13446 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13446 := by decide +kernel

theorem rowCheck13446 : row13446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13446 := by decide +kernel

theorem rowEval13446 (x : Key → ℝ) : Integer.Sparse.eval row13446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13446, Integer.Sparse.eval_collectBalanced, rawRowCheck13446]

theorem rawRowCheck13447 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13447 := by decide +kernel

theorem rowCheck13447 : row13447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13447 := by decide +kernel

theorem rowEval13447 (x : Key → ℝ) : Integer.Sparse.eval row13447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13447, Integer.Sparse.eval_collectBalanced, rawRowCheck13447]

theorem rawRowCheck13448 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13448 := by decide +kernel

theorem rowCheck13448 : row13448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13448 := by decide +kernel

theorem rowEval13448 (x : Key → ℝ) : Integer.Sparse.eval row13448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13448, Integer.Sparse.eval_collectBalanced, rawRowCheck13448]

theorem rawRowCheck13449 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3 = rawRow13449 := by decide +kernel

theorem rowCheck13449 : row13449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13449 := by decide +kernel

theorem rowEval13449 (x : Key → ℝ) : Integer.Sparse.eval row13449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13449, Integer.Sparse.eval_collectBalanced, rawRowCheck13449]

theorem rawRowCheck13450 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3 = rawRow13450 := by decide +kernel

theorem rowCheck13450 : row13450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13450 := by decide +kernel

theorem rowEval13450 (x : Key → ℝ) : Integer.Sparse.eval row13450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13450, Integer.Sparse.eval_collectBalanced, rawRowCheck13450]

theorem rawRowCheck13451 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3 = rawRow13451 := by decide +kernel

theorem rowCheck13451 : row13451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13451 := by decide +kernel

theorem rowEval13451 (x : Key → ℝ) : Integer.Sparse.eval row13451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13451, Integer.Sparse.eval_collectBalanced, rawRowCheck13451]

theorem rawRowCheck13452 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3 = rawRow13452 := by decide +kernel

theorem rowCheck13452 : row13452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13452 := by decide +kernel

theorem rowEval13452 (x : Key → ℝ) : Integer.Sparse.eval row13452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13452, Integer.Sparse.eval_collectBalanced, rawRowCheck13452]

theorem rawRowCheck13453 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3 = rawRow13453 := by decide +kernel

theorem rowCheck13453 : row13453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13453 := by decide +kernel

theorem rowEval13453 (x : Key → ℝ) : Integer.Sparse.eval row13453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13453, Integer.Sparse.eval_collectBalanced, rawRowCheck13453]

theorem rawRowCheck13454 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3 = rawRow13454 := by decide +kernel

theorem rowCheck13454 : row13454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13454 := by decide +kernel

theorem rowEval13454 (x : Key → ℝ) : Integer.Sparse.eval row13454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck13454, Integer.Sparse.eval_collectBalanced, rawRowCheck13454]

theorem rawRowCheck13455 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3 = rawRow13455 := by decide +kernel

theorem rowCheck13455 : row13455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13455 := by decide +kernel

theorem rowEval13455 (x : Key → ℝ) : Integer.Sparse.eval row13455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13455, Integer.Sparse.eval_collectBalanced, rawRowCheck13455]

theorem rawRowCheck13456 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3 = rawRow13456 := by decide +kernel

theorem rowCheck13456 : row13456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13456 := by decide +kernel

theorem rowEval13456 (x : Key → ℝ) : Integer.Sparse.eval row13456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13456, Integer.Sparse.eval_collectBalanced, rawRowCheck13456]

theorem rawRowCheck13457 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3 = rawRow13457 := by decide +kernel

theorem rowCheck13457 : row13457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13457 := by decide +kernel

theorem rowEval13457 (x : Key → ℝ) : Integer.Sparse.eval row13457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13457, Integer.Sparse.eval_collectBalanced, rawRowCheck13457]

theorem rawRowCheck13458 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13458 := by decide +kernel

theorem rowCheck13458 : row13458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13458 := by decide +kernel

theorem rowEval13458 (x : Key → ℝ) : Integer.Sparse.eval row13458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13458, Integer.Sparse.eval_collectBalanced, rawRowCheck13458]

theorem rawRowCheck13459 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13459 := by decide +kernel

theorem rowCheck13459 : row13459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13459 := by decide +kernel

theorem rowEval13459 (x : Key → ℝ) : Integer.Sparse.eval row13459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13459, Integer.Sparse.eval_collectBalanced, rawRowCheck13459]

theorem rawRowCheck13460 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13460 := by decide +kernel

theorem rowCheck13460 : row13460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13460 := by decide +kernel

theorem rowEval13460 (x : Key → ℝ) : Integer.Sparse.eval row13460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13460, Integer.Sparse.eval_collectBalanced, rawRowCheck13460]

theorem rawRowCheck13461 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3 = rawRow13461 := by decide +kernel

theorem rowCheck13461 : row13461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13461 := by decide +kernel

theorem rowEval13461 (x : Key → ℝ) : Integer.Sparse.eval row13461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13461, Integer.Sparse.eval_collectBalanced, rawRowCheck13461]

theorem rawRowCheck13462 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3 = rawRow13462 := by decide +kernel

theorem rowCheck13462 : row13462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13462 := by decide +kernel

theorem rowEval13462 (x : Key → ℝ) : Integer.Sparse.eval row13462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13462, Integer.Sparse.eval_collectBalanced, rawRowCheck13462]

theorem rawRowCheck13463 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3 = rawRow13463 := by decide +kernel

theorem rowCheck13463 : row13463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13463 := by decide +kernel

theorem rowEval13463 (x : Key → ℝ) : Integer.Sparse.eval row13463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck13463, Integer.Sparse.eval_collectBalanced, rawRowCheck13463]

theorem rawRowCheck13464 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3 = rawRow13464 := by decide +kernel

theorem rowCheck13464 : row13464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13464 := by decide +kernel

theorem rowEval13464 (x : Key → ℝ) : Integer.Sparse.eval row13464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form3) x := by
  rw [rowCheck13464, Integer.Sparse.eval_collectBalanced, rawRowCheck13464]

theorem rawRowCheck13465 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow13465 := by decide +kernel

theorem rowCheck13465 : row13465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13465 := by decide +kernel

theorem rowEval13465 (x : Key → ℝ) : Integer.Sparse.eval row13465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13465, Integer.Sparse.eval_collectBalanced, rawRowCheck13465]

theorem rawRowCheck13466 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow13466 := by decide +kernel

theorem rowCheck13466 : row13466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13466 := by decide +kernel

theorem rowEval13466 (x : Key → ℝ) : Integer.Sparse.eval row13466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13466, Integer.Sparse.eval_collectBalanced, rawRowCheck13466]

theorem rawRowCheck13467 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow13467 := by decide +kernel

theorem rowCheck13467 : row13467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13467 := by decide +kernel

theorem rowEval13467 (x : Key → ℝ) : Integer.Sparse.eval row13467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13467, Integer.Sparse.eval_collectBalanced, rawRowCheck13467]

theorem rawRowCheck13468 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow13468 := by decide +kernel

theorem rowCheck13468 : row13468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13468 := by decide +kernel

theorem rowEval13468 (x : Key → ℝ) : Integer.Sparse.eval row13468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13468, Integer.Sparse.eval_collectBalanced, rawRowCheck13468]

theorem rawRowCheck13469 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow13469 := by decide +kernel

theorem rowCheck13469 : row13469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13469 := by decide +kernel

theorem rowEval13469 (x : Key → ℝ) : Integer.Sparse.eval row13469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13469, Integer.Sparse.eval_collectBalanced, rawRowCheck13469]

theorem rawRowCheck13470 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow13470 := by decide +kernel

theorem rowCheck13470 : row13470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13470 := by decide +kernel

theorem rowEval13470 (x : Key → ℝ) : Integer.Sparse.eval row13470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13470, Integer.Sparse.eval_collectBalanced, rawRowCheck13470]

theorem rawRowCheck13471 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow13471 := by decide +kernel

theorem rowCheck13471 : row13471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13471 := by decide +kernel

theorem rowEval13471 (x : Key → ℝ) : Integer.Sparse.eval row13471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13471, Integer.Sparse.eval_collectBalanced, rawRowCheck13471]

theorem rawRowCheck13472 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow13472 := by decide +kernel

theorem rowCheck13472 : row13472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13472 := by decide +kernel

theorem rowEval13472 (x : Key → ℝ) : Integer.Sparse.eval row13472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13472, Integer.Sparse.eval_collectBalanced, rawRowCheck13472]

theorem rawRowCheck13473 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow13473 := by decide +kernel

theorem rowCheck13473 : row13473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13473 := by decide +kernel

theorem rowEval13473 (x : Key → ℝ) : Integer.Sparse.eval row13473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13473, Integer.Sparse.eval_collectBalanced, rawRowCheck13473]

theorem rawRowCheck13474 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow13474 := by decide +kernel

theorem rowCheck13474 : row13474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13474 := by decide +kernel

theorem rowEval13474 (x : Key → ℝ) : Integer.Sparse.eval row13474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck13474, Integer.Sparse.eval_collectBalanced, rawRowCheck13474]

theorem rawRowCheck13475 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow13475 := by decide +kernel

theorem rowCheck13475 : row13475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13475 := by decide +kernel

theorem rowEval13475 (x : Key → ℝ) : Integer.Sparse.eval row13475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13475, Integer.Sparse.eval_collectBalanced, rawRowCheck13475]

theorem rawRowCheck13476 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow13476 := by decide +kernel

theorem rowCheck13476 : row13476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13476 := by decide +kernel

theorem rowEval13476 (x : Key → ℝ) : Integer.Sparse.eval row13476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13476, Integer.Sparse.eval_collectBalanced, rawRowCheck13476]

theorem rawRowCheck13477 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow13477 := by decide +kernel

theorem rowCheck13477 : row13477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13477 := by decide +kernel

theorem rowEval13477 (x : Key → ℝ) : Integer.Sparse.eval row13477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13477, Integer.Sparse.eval_collectBalanced, rawRowCheck13477]

theorem rawRowCheck13478 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13478 := by decide +kernel

theorem rowCheck13478 : row13478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13478 := by decide +kernel

theorem rowEval13478 (x : Key → ℝ) : Integer.Sparse.eval row13478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13478, Integer.Sparse.eval_collectBalanced, rawRowCheck13478]

theorem rawRowCheck13479 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13479 := by decide +kernel

theorem rowCheck13479 : row13479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13479 := by decide +kernel

theorem rowEval13479 (x : Key → ℝ) : Integer.Sparse.eval row13479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13479, Integer.Sparse.eval_collectBalanced, rawRowCheck13479]

theorem rawRowCheck13480 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13480 := by decide +kernel

theorem rowCheck13480 : row13480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13480 := by decide +kernel

theorem rowEval13480 (x : Key → ℝ) : Integer.Sparse.eval row13480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13480, Integer.Sparse.eval_collectBalanced, rawRowCheck13480]

theorem rawRowCheck13481 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4 = rawRow13481 := by decide +kernel

theorem rowCheck13481 : row13481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13481 := by decide +kernel

theorem rowEval13481 (x : Key → ℝ) : Integer.Sparse.eval row13481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13481, Integer.Sparse.eval_collectBalanced, rawRowCheck13481]

theorem rawRowCheck13482 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4 = rawRow13482 := by decide +kernel

theorem rowCheck13482 : row13482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13482 := by decide +kernel

theorem rowEval13482 (x : Key → ℝ) : Integer.Sparse.eval row13482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13482, Integer.Sparse.eval_collectBalanced, rawRowCheck13482]

theorem rawRowCheck13483 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4 = rawRow13483 := by decide +kernel

theorem rowCheck13483 : row13483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13483 := by decide +kernel

theorem rowEval13483 (x : Key → ℝ) : Integer.Sparse.eval row13483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck13483, Integer.Sparse.eval_collectBalanced, rawRowCheck13483]

theorem rawRowCheck13484 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4 = rawRow13484 := by decide +kernel

theorem rowCheck13484 : row13484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13484 := by decide +kernel

theorem rowEval13484 (x : Key → ℝ) : Integer.Sparse.eval row13484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck13484, Integer.Sparse.eval_collectBalanced, rawRowCheck13484]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13385 x
  · exact rowEval13386 x
  · exact rowEval13387 x
  · exact rowEval13388 x
  · exact rowEval13389 x
  · exact rowEval13390 x
  · exact rowEval13391 x
  · exact rowEval13392 x
  · exact rowEval13393 x
  · exact rowEval13394 x
  · exact rowEval13395 x
  · exact rowEval13396 x
  · exact rowEval13397 x
  · exact rowEval13398 x
  · exact rowEval13399 x
  · exact rowEval13400 x
  · exact rowEval13401 x
  · exact rowEval13402 x
  · exact rowEval13403 x
  · exact rowEval13404 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval13405 x
  · exact rowEval13406 x
  · exact rowEval13407 x
  · exact rowEval13408 x
  · exact rowEval13409 x
  · exact rowEval13410 x
  · exact rowEval13411 x
  · exact rowEval13412 x
  · exact rowEval13413 x
  · exact rowEval13414 x
  · exact rowEval13415 x
  · exact rowEval13416 x
  · exact rowEval13417 x
  · exact rowEval13418 x
  · exact rowEval13419 x
  · exact rowEval13420 x
  · exact rowEval13421 x
  · exact rowEval13422 x
  · exact rowEval13423 x
  · exact rowEval13424 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval13425 x
  · exact rowEval13426 x
  · exact rowEval13427 x
  · exact rowEval13428 x
  · exact rowEval13429 x
  · exact rowEval13430 x
  · exact rowEval13431 x
  · exact rowEval13432 x
  · exact rowEval13433 x
  · exact rowEval13434 x
  · exact rowEval13435 x
  · exact rowEval13436 x
  · exact rowEval13437 x
  · exact rowEval13438 x
  · exact rowEval13439 x
  · exact rowEval13440 x
  · exact rowEval13441 x
  · exact rowEval13442 x
  · exact rowEval13443 x
  · exact rowEval13444 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval13445 x
  · exact rowEval13446 x
  · exact rowEval13447 x
  · exact rowEval13448 x
  · exact rowEval13449 x
  · exact rowEval13450 x
  · exact rowEval13451 x
  · exact rowEval13452 x
  · exact rowEval13453 x
  · exact rowEval13454 x
  · exact rowEval13455 x
  · exact rowEval13456 x
  · exact rowEval13457 x
  · exact rowEval13458 x
  · exact rowEval13459 x
  · exact rowEval13460 x
  · exact rowEval13461 x
  · exact rowEval13462 x
  · exact rowEval13463 x
  · exact rowEval13464 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13465 x
  · exact rowEval13466 x
  · exact rowEval13467 x
  · exact rowEval13468 x
  · exact rowEval13469 x
  · exact rowEval13470 x
  · exact rowEval13471 x
  · exact rowEval13472 x
  · exact rowEval13473 x
  · exact rowEval13474 x
  · exact rowEval13475 x
  · exact rowEval13476 x
  · exact rowEval13477 x
  · exact rowEval13478 x
  · exact rowEval13479 x
  · exact rowEval13480 x
  · exact rowEval13481 x
  · exact rowEval13482 x
  · exact rowEval13483 x
  · exact rowEval13484 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block4

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

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval13885 x
  · exact rowEval13886 x
  · exact rowEval13887 x
  · exact rowEval13888 x
  · exact rowEval13889 x
  · exact rowEval13890 x
  · exact rowEval13891 x
  · exact rowEval13892 x
  · exact rowEval13893 x
  · exact rowEval13894 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

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

theorem rawRowCheck14005 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14005 := by decide +kernel

theorem rowCheck14005 : row14005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14005 := by decide +kernel

theorem rowEval14005 (x : Key → ℝ) : Integer.Sparse.eval row14005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14005, Integer.Sparse.eval_collectBalanced, rawRowCheck14005]

theorem rawRowCheck14006 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14006 := by decide +kernel

theorem rowCheck14006 : row14006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14006 := by decide +kernel

theorem rowEval14006 (x : Key → ℝ) : Integer.Sparse.eval row14006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14006, Integer.Sparse.eval_collectBalanced, rawRowCheck14006]

theorem rawRowCheck14007 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14007 := by decide +kernel

theorem rowCheck14007 : row14007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14007 := by decide +kernel

theorem rowEval14007 (x : Key → ℝ) : Integer.Sparse.eval row14007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14007, Integer.Sparse.eval_collectBalanced, rawRowCheck14007]

theorem rawRowCheck14008 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14008 := by decide +kernel

theorem rowCheck14008 : row14008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14008 := by decide +kernel

theorem rowEval14008 (x : Key → ℝ) : Integer.Sparse.eval row14008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14008, Integer.Sparse.eval_collectBalanced, rawRowCheck14008]

theorem rawRowCheck14009 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4 = rawRow14009 := by decide +kernel

theorem rowCheck14009 : row14009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14009 := by decide +kernel

theorem rowEval14009 (x : Key → ℝ) : Integer.Sparse.eval row14009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14009, Integer.Sparse.eval_collectBalanced, rawRowCheck14009]

theorem rawRowCheck14010 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4 = rawRow14010 := by decide +kernel

theorem rowCheck14010 : row14010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14010 := by decide +kernel

theorem rowEval14010 (x : Key → ℝ) : Integer.Sparse.eval row14010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14010, Integer.Sparse.eval_collectBalanced, rawRowCheck14010]

theorem rawRowCheck14011 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4 = rawRow14011 := by decide +kernel

theorem rowCheck14011 : row14011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14011 := by decide +kernel

theorem rowEval14011 (x : Key → ℝ) : Integer.Sparse.eval row14011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14011, Integer.Sparse.eval_collectBalanced, rawRowCheck14011]

theorem rawRowCheck14012 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4 = rawRow14012 := by decide +kernel

theorem rowCheck14012 : row14012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14012 := by decide +kernel

theorem rowEval14012 (x : Key → ℝ) : Integer.Sparse.eval row14012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14012, Integer.Sparse.eval_collectBalanced, rawRowCheck14012]

theorem rawRowCheck14013 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4 = rawRow14013 := by decide +kernel

theorem rowCheck14013 : row14013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14013 := by decide +kernel

theorem rowEval14013 (x : Key → ℝ) : Integer.Sparse.eval row14013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14013, Integer.Sparse.eval_collectBalanced, rawRowCheck14013]

theorem rawRowCheck14014 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4 = rawRow14014 := by decide +kernel

theorem rowCheck14014 : row14014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14014 := by decide +kernel

theorem rowEval14014 (x : Key → ℝ) : Integer.Sparse.eval row14014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck14014, Integer.Sparse.eval_collectBalanced, rawRowCheck14014]

theorem rawRowCheck14015 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4 = rawRow14015 := by decide +kernel

theorem rowCheck14015 : row14015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14015 := by decide +kernel

theorem rowEval14015 (x : Key → ℝ) : Integer.Sparse.eval row14015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14015, Integer.Sparse.eval_collectBalanced, rawRowCheck14015]

theorem rawRowCheck14016 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4 = rawRow14016 := by decide +kernel

theorem rowCheck14016 : row14016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14016 := by decide +kernel

theorem rowEval14016 (x : Key → ℝ) : Integer.Sparse.eval row14016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14016, Integer.Sparse.eval_collectBalanced, rawRowCheck14016]

theorem rawRowCheck14017 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4 = rawRow14017 := by decide +kernel

theorem rowCheck14017 : row14017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14017 := by decide +kernel

theorem rowEval14017 (x : Key → ℝ) : Integer.Sparse.eval row14017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14017, Integer.Sparse.eval_collectBalanced, rawRowCheck14017]

theorem rawRowCheck14018 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14018 := by decide +kernel

theorem rowCheck14018 : row14018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14018 := by decide +kernel

theorem rowEval14018 (x : Key → ℝ) : Integer.Sparse.eval row14018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14018, Integer.Sparse.eval_collectBalanced, rawRowCheck14018]

theorem rawRowCheck14019 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14019 := by decide +kernel

theorem rowCheck14019 : row14019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14019 := by decide +kernel

theorem rowEval14019 (x : Key → ℝ) : Integer.Sparse.eval row14019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14019, Integer.Sparse.eval_collectBalanced, rawRowCheck14019]

theorem rawRowCheck14020 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14020 := by decide +kernel

theorem rowCheck14020 : row14020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14020 := by decide +kernel

theorem rowEval14020 (x : Key → ℝ) : Integer.Sparse.eval row14020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14020, Integer.Sparse.eval_collectBalanced, rawRowCheck14020]

theorem rawRowCheck14021 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4 = rawRow14021 := by decide +kernel

theorem rowCheck14021 : row14021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14021 := by decide +kernel

theorem rowEval14021 (x : Key → ℝ) : Integer.Sparse.eval row14021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14021, Integer.Sparse.eval_collectBalanced, rawRowCheck14021]

theorem rawRowCheck14022 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4 = rawRow14022 := by decide +kernel

theorem rowCheck14022 : row14022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14022 := by decide +kernel

theorem rowEval14022 (x : Key → ℝ) : Integer.Sparse.eval row14022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14022, Integer.Sparse.eval_collectBalanced, rawRowCheck14022]

theorem rawRowCheck14023 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4 = rawRow14023 := by decide +kernel

theorem rowCheck14023 : row14023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14023 := by decide +kernel

theorem rowEval14023 (x : Key → ℝ) : Integer.Sparse.eval row14023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck14023, Integer.Sparse.eval_collectBalanced, rawRowCheck14023]

theorem rawRowCheck14024 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4 = rawRow14024 := by decide +kernel

theorem rowCheck14024 : row14024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14024 := by decide +kernel

theorem rowEval14024 (x : Key → ℝ) : Integer.Sparse.eval row14024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form4) x := by
  rw [rowCheck14024, Integer.Sparse.eval_collectBalanced, rawRowCheck14024]

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

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14005 x
  · exact rowEval14006 x
  · exact rowEval14007 x
  · exact rowEval14008 x
  · exact rowEval14009 x
  · exact rowEval14010 x
  · exact rowEval14011 x
  · exact rowEval14012 x
  · exact rowEval14013 x
  · exact rowEval14014 x
  · exact rowEval14015 x
  · exact rowEval14016 x
  · exact rowEval14017 x
  · exact rowEval14018 x
  · exact rowEval14019 x
  · exact rowEval14020 x
  · exact rowEval14021 x
  · exact rowEval14022 x
  · exact rowEval14023 x
  · exact rowEval14024 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

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

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14145 x
  · exact rowEval14146 x
  · exact rowEval14147 x
  · exact rowEval14148 x
  · exact rowEval14149 x
  · exact rowEval14150 x
  · exact rowEval14151 x
  · exact rowEval14152 x
  · exact rowEval14153 x
  · exact rowEval14154 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

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

theorem entryEvalRow4_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 4).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4_e_oai
