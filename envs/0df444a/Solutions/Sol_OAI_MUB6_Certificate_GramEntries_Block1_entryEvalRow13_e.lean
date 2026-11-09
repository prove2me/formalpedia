-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:24:50.408922+00:00
-- url     : https://prove2.me/submissions/8ab7a236-81e0-4456-858d-56ca32d2171f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval15_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval18_13_e

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

theorem rawRowCheck2490 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2490 := by decide +kernel

theorem rowCheck2490 : row2490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2490 := by decide +kernel

theorem rowEval2490 (x : Key → ℝ) : Integer.Sparse.eval row2490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2490, Integer.Sparse.eval_collectBalanced, rawRowCheck2490]

theorem rawRowCheck2491 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2491 := by decide +kernel

theorem rowCheck2491 : row2491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2491 := by decide +kernel

theorem rowEval2491 (x : Key → ℝ) : Integer.Sparse.eval row2491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2491, Integer.Sparse.eval_collectBalanced, rawRowCheck2491]

theorem rawRowCheck2492 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2492 := by decide +kernel

theorem rowCheck2492 : row2492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2492 := by decide +kernel

theorem rowEval2492 (x : Key → ℝ) : Integer.Sparse.eval row2492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2492, Integer.Sparse.eval_collectBalanced, rawRowCheck2492]

theorem rawRowCheck2493 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2493 := by decide +kernel

theorem rowCheck2493 : row2493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2493 := by decide +kernel

theorem rowEval2493 (x : Key → ℝ) : Integer.Sparse.eval row2493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2493, Integer.Sparse.eval_collectBalanced, rawRowCheck2493]

theorem rawRowCheck2494 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow2494 := by decide +kernel

theorem rowCheck2494 : row2494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2494 := by decide +kernel

theorem rowEval2494 (x : Key → ℝ) : Integer.Sparse.eval row2494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2494, Integer.Sparse.eval_collectBalanced, rawRowCheck2494]

theorem rawRowCheck2495 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow2495 := by decide +kernel

theorem rowCheck2495 : row2495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2495 := by decide +kernel

theorem rowEval2495 (x : Key → ℝ) : Integer.Sparse.eval row2495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2495, Integer.Sparse.eval_collectBalanced, rawRowCheck2495]

theorem rawRowCheck2496 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow2496 := by decide +kernel

theorem rowCheck2496 : row2496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2496 := by decide +kernel

theorem rowEval2496 (x : Key → ℝ) : Integer.Sparse.eval row2496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2496, Integer.Sparse.eval_collectBalanced, rawRowCheck2496]

theorem rawRowCheck2497 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2497 := by decide +kernel

theorem rowCheck2497 : row2497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2497 := by decide +kernel

theorem rowEval2497 (x : Key → ℝ) : Integer.Sparse.eval row2497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2497, Integer.Sparse.eval_collectBalanced, rawRowCheck2497]

theorem rawRowCheck2498 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2498 := by decide +kernel

theorem rowCheck2498 : row2498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2498 := by decide +kernel

theorem rowEval2498 (x : Key → ℝ) : Integer.Sparse.eval row2498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2498, Integer.Sparse.eval_collectBalanced, rawRowCheck2498]

theorem rawRowCheck2499 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2499 := by decide +kernel

theorem rowCheck2499 : row2499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2499 := by decide +kernel

theorem rowEval2499 (x : Key → ℝ) : Integer.Sparse.eval row2499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2499, Integer.Sparse.eval_collectBalanced, rawRowCheck2499]

theorem rawRowCheck2500 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow2500 := by decide +kernel

theorem rowCheck2500 : row2500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2500 := by decide +kernel

theorem rowEval2500 (x : Key → ℝ) : Integer.Sparse.eval row2500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2500, Integer.Sparse.eval_collectBalanced, rawRowCheck2500]

theorem rawRowCheck2501 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow2501 := by decide +kernel

theorem rowCheck2501 : row2501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2501 := by decide +kernel

theorem rowEval2501 (x : Key → ℝ) : Integer.Sparse.eval row2501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2501, Integer.Sparse.eval_collectBalanced, rawRowCheck2501]

theorem rawRowCheck2502 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow2502 := by decide +kernel

theorem rowCheck2502 : row2502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2502 := by decide +kernel

theorem rowEval2502 (x : Key → ℝ) : Integer.Sparse.eval row2502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2502, Integer.Sparse.eval_collectBalanced, rawRowCheck2502]

theorem rawRowCheck2503 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow2503 := by decide +kernel

theorem rowCheck2503 : row2503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2503 := by decide +kernel

theorem rowEval2503 (x : Key → ℝ) : Integer.Sparse.eval row2503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2503, Integer.Sparse.eval_collectBalanced, rawRowCheck2503]

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

theorem rawRowCheck2518 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2518 := by decide +kernel

theorem rowCheck2518 : row2518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2518 := by decide +kernel

theorem rowEval2518 (x : Key → ℝ) : Integer.Sparse.eval row2518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2518, Integer.Sparse.eval_collectBalanced, rawRowCheck2518]

theorem rawRowCheck2519 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2519 := by decide +kernel

theorem rowCheck2519 : row2519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2519 := by decide +kernel

theorem rowEval2519 (x : Key → ℝ) : Integer.Sparse.eval row2519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2519, Integer.Sparse.eval_collectBalanced, rawRowCheck2519]

theorem rawRowCheck2520 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2520 := by decide +kernel

theorem rowCheck2520 : row2520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2520 := by decide +kernel

theorem rowEval2520 (x : Key → ℝ) : Integer.Sparse.eval row2520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2520, Integer.Sparse.eval_collectBalanced, rawRowCheck2520]

theorem rawRowCheck2521 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2521 := by decide +kernel

theorem rowCheck2521 : row2521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2521 := by decide +kernel

theorem rowEval2521 (x : Key → ℝ) : Integer.Sparse.eval row2521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2521, Integer.Sparse.eval_collectBalanced, rawRowCheck2521]

theorem rawRowCheck2522 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3 = rawRow2522 := by decide +kernel

theorem rowCheck2522 : row2522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2522 := by decide +kernel

theorem rowEval2522 (x : Key → ℝ) : Integer.Sparse.eval row2522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form3) x := by
  rw [rowCheck2522, Integer.Sparse.eval_collectBalanced, rawRowCheck2522]

theorem rawRowCheck2523 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3 = rawRow2523 := by decide +kernel

theorem rowCheck2523 : row2523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2523 := by decide +kernel

theorem rowEval2523 (x : Key → ℝ) : Integer.Sparse.eval row2523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2523, Integer.Sparse.eval_collectBalanced, rawRowCheck2523]

theorem rawRowCheck2524 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3 = rawRow2524 := by decide +kernel

theorem rowCheck2524 : row2524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2524 := by decide +kernel

theorem rowEval2524 (x : Key → ℝ) : Integer.Sparse.eval row2524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2524, Integer.Sparse.eval_collectBalanced, rawRowCheck2524]

theorem rawRowCheck2525 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2525 := by decide +kernel

theorem rowCheck2525 : row2525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2525 := by decide +kernel

theorem rowEval2525 (x : Key → ℝ) : Integer.Sparse.eval row2525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2525, Integer.Sparse.eval_collectBalanced, rawRowCheck2525]

theorem rawRowCheck2526 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2526 := by decide +kernel

theorem rowCheck2526 : row2526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2526 := by decide +kernel

theorem rowEval2526 (x : Key → ℝ) : Integer.Sparse.eval row2526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2526, Integer.Sparse.eval_collectBalanced, rawRowCheck2526]

theorem rawRowCheck2527 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2527 := by decide +kernel

theorem rowCheck2527 : row2527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2527 := by decide +kernel

theorem rowEval2527 (x : Key → ℝ) : Integer.Sparse.eval row2527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2527, Integer.Sparse.eval_collectBalanced, rawRowCheck2527]

theorem rawRowCheck2528 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow2528 := by decide +kernel

theorem rowCheck2528 : row2528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2528 := by decide +kernel

theorem rowEval2528 (x : Key → ℝ) : Integer.Sparse.eval row2528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2528, Integer.Sparse.eval_collectBalanced, rawRowCheck2528]

theorem rawRowCheck2529 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3 = rawRow2529 := by decide +kernel

theorem rowCheck2529 : row2529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2529 := by decide +kernel

theorem rowEval2529 (x : Key → ℝ) : Integer.Sparse.eval row2529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2529, Integer.Sparse.eval_collectBalanced, rawRowCheck2529]

theorem rawRowCheck2530 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3 = rawRow2530 := by decide +kernel

theorem rowCheck2530 : row2530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2530 := by decide +kernel

theorem rowEval2530 (x : Key → ℝ) : Integer.Sparse.eval row2530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck2530, Integer.Sparse.eval_collectBalanced, rawRowCheck2530]

theorem rawRowCheck2531 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3 = rawRow2531 := by decide +kernel

theorem rowCheck2531 : row2531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2531 := by decide +kernel

theorem rowEval2531 (x : Key → ℝ) : Integer.Sparse.eval row2531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck2531, Integer.Sparse.eval_collectBalanced, rawRowCheck2531]

theorem rawRowCheck2532 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2532 := by decide +kernel

theorem rowCheck2532 : row2532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2532 := by decide +kernel

theorem rowEval2532 (x : Key → ℝ) : Integer.Sparse.eval row2532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2532, Integer.Sparse.eval_collectBalanced, rawRowCheck2532]

theorem rawRowCheck2533 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2533 := by decide +kernel

theorem rowCheck2533 : row2533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2533 := by decide +kernel

theorem rowEval2533 (x : Key → ℝ) : Integer.Sparse.eval row2533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2533, Integer.Sparse.eval_collectBalanced, rawRowCheck2533]

theorem rawRowCheck2534 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2534 := by decide +kernel

theorem rowCheck2534 : row2534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2534 := by decide +kernel

theorem rowEval2534 (x : Key → ℝ) : Integer.Sparse.eval row2534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2534, Integer.Sparse.eval_collectBalanced, rawRowCheck2534]

theorem rawRowCheck2535 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2535 := by decide +kernel

theorem rowCheck2535 : row2535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2535 := by decide +kernel

theorem rowEval2535 (x : Key → ℝ) : Integer.Sparse.eval row2535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2535, Integer.Sparse.eval_collectBalanced, rawRowCheck2535]

theorem rawRowCheck2536 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4 = rawRow2536 := by decide +kernel

theorem rowCheck2536 : row2536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2536 := by decide +kernel

theorem rowEval2536 (x : Key → ℝ) : Integer.Sparse.eval row2536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form4) x := by
  rw [rowCheck2536, Integer.Sparse.eval_collectBalanced, rawRowCheck2536]

theorem rawRowCheck2537 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4 = rawRow2537 := by decide +kernel

theorem rowCheck2537 : row2537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2537 := by decide +kernel

theorem rowEval2537 (x : Key → ℝ) : Integer.Sparse.eval row2537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2537, Integer.Sparse.eval_collectBalanced, rawRowCheck2537]

theorem rawRowCheck2538 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4 = rawRow2538 := by decide +kernel

theorem rowCheck2538 : row2538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2538 := by decide +kernel

theorem rowEval2538 (x : Key → ℝ) : Integer.Sparse.eval row2538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2538, Integer.Sparse.eval_collectBalanced, rawRowCheck2538]

theorem rawRowCheck2539 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2539 := by decide +kernel

theorem rowCheck2539 : row2539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2539 := by decide +kernel

theorem rowEval2539 (x : Key → ℝ) : Integer.Sparse.eval row2539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2539, Integer.Sparse.eval_collectBalanced, rawRowCheck2539]

theorem rawRowCheck2540 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2540 := by decide +kernel

theorem rowCheck2540 : row2540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2540 := by decide +kernel

theorem rowEval2540 (x : Key → ℝ) : Integer.Sparse.eval row2540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2540, Integer.Sparse.eval_collectBalanced, rawRowCheck2540]

theorem rawRowCheck2541 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2541 := by decide +kernel

theorem rowCheck2541 : row2541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2541 := by decide +kernel

theorem rowEval2541 (x : Key → ℝ) : Integer.Sparse.eval row2541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2541, Integer.Sparse.eval_collectBalanced, rawRowCheck2541]

theorem rawRowCheck2542 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow2542 := by decide +kernel

theorem rowCheck2542 : row2542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2542 := by decide +kernel

theorem rowEval2542 (x : Key → ℝ) : Integer.Sparse.eval row2542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2542, Integer.Sparse.eval_collectBalanced, rawRowCheck2542]

theorem rawRowCheck2543 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4 = rawRow2543 := by decide +kernel

theorem rowCheck2543 : row2543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2543 := by decide +kernel

theorem rowEval2543 (x : Key → ℝ) : Integer.Sparse.eval row2543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2543, Integer.Sparse.eval_collectBalanced, rawRowCheck2543]

theorem rawRowCheck2544 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4 = rawRow2544 := by decide +kernel

theorem rowCheck2544 : row2544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2544 := by decide +kernel

theorem rowEval2544 (x : Key → ℝ) : Integer.Sparse.eval row2544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck2544, Integer.Sparse.eval_collectBalanced, rawRowCheck2544]

theorem rawRowCheck2545 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4 = rawRow2545 := by decide +kernel

theorem rowCheck2545 : row2545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2545 := by decide +kernel

theorem rowEval2545 (x : Key → ℝ) : Integer.Sparse.eval row2545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck2545, Integer.Sparse.eval_collectBalanced, rawRowCheck2545]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck2560 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2560 := by decide +kernel

theorem rowCheck2560 : row2560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2560 := by decide +kernel

theorem rowEval2560 (x : Key → ℝ) : Integer.Sparse.eval row2560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2560, Integer.Sparse.eval_collectBalanced, rawRowCheck2560]

theorem rawRowCheck2561 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2561 := by decide +kernel

theorem rowCheck2561 : row2561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2561 := by decide +kernel

theorem rowEval2561 (x : Key → ℝ) : Integer.Sparse.eval row2561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2561, Integer.Sparse.eval_collectBalanced, rawRowCheck2561]

theorem rawRowCheck2562 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2562 := by decide +kernel

theorem rowCheck2562 : row2562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2562 := by decide +kernel

theorem rowEval2562 (x : Key → ℝ) : Integer.Sparse.eval row2562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2562, Integer.Sparse.eval_collectBalanced, rawRowCheck2562]

theorem rawRowCheck2563 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2563 := by decide +kernel

theorem rowCheck2563 : row2563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2563 := by decide +kernel

theorem rowEval2563 (x : Key → ℝ) : Integer.Sparse.eval row2563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2563, Integer.Sparse.eval_collectBalanced, rawRowCheck2563]

theorem rawRowCheck2564 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6 = rawRow2564 := by decide +kernel

theorem rowCheck2564 : row2564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2564 := by decide +kernel

theorem rowEval2564 (x : Key → ℝ) : Integer.Sparse.eval row2564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck2564, Integer.Sparse.eval_collectBalanced, rawRowCheck2564]

theorem rawRowCheck2565 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6 = rawRow2565 := by decide +kernel

theorem rowCheck2565 : row2565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2565 := by decide +kernel

theorem rowEval2565 (x : Key → ℝ) : Integer.Sparse.eval row2565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2565, Integer.Sparse.eval_collectBalanced, rawRowCheck2565]

theorem rawRowCheck2566 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6 = rawRow2566 := by decide +kernel

theorem rowCheck2566 : row2566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2566 := by decide +kernel

theorem rowEval2566 (x : Key → ℝ) : Integer.Sparse.eval row2566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2566, Integer.Sparse.eval_collectBalanced, rawRowCheck2566]

theorem rawRowCheck2567 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2567 := by decide +kernel

theorem rowCheck2567 : row2567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2567 := by decide +kernel

theorem rowEval2567 (x : Key → ℝ) : Integer.Sparse.eval row2567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2567, Integer.Sparse.eval_collectBalanced, rawRowCheck2567]

theorem rawRowCheck2568 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2568 := by decide +kernel

theorem rowCheck2568 : row2568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2568 := by decide +kernel

theorem rowEval2568 (x : Key → ℝ) : Integer.Sparse.eval row2568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2568, Integer.Sparse.eval_collectBalanced, rawRowCheck2568]

theorem rawRowCheck2569 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2569 := by decide +kernel

theorem rowCheck2569 : row2569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2569 := by decide +kernel

theorem rowEval2569 (x : Key → ℝ) : Integer.Sparse.eval row2569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2569, Integer.Sparse.eval_collectBalanced, rawRowCheck2569]

theorem rawRowCheck2570 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow2570 := by decide +kernel

theorem rowCheck2570 : row2570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2570 := by decide +kernel

theorem rowEval2570 (x : Key → ℝ) : Integer.Sparse.eval row2570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2570, Integer.Sparse.eval_collectBalanced, rawRowCheck2570]

theorem rawRowCheck2571 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6 = rawRow2571 := by decide +kernel

theorem rowCheck2571 : row2571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2571 := by decide +kernel

theorem rowEval2571 (x : Key → ℝ) : Integer.Sparse.eval row2571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2571, Integer.Sparse.eval_collectBalanced, rawRowCheck2571]

theorem rawRowCheck2572 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6 = rawRow2572 := by decide +kernel

theorem rowCheck2572 : row2572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2572 := by decide +kernel

theorem rowEval2572 (x : Key → ℝ) : Integer.Sparse.eval row2572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck2572, Integer.Sparse.eval_collectBalanced, rawRowCheck2572]

theorem rawRowCheck2573 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6 = rawRow2573 := by decide +kernel

theorem rowCheck2573 : row2573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2573 := by decide +kernel

theorem rowEval2573 (x : Key → ℝ) : Integer.Sparse.eval row2573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck2573, Integer.Sparse.eval_collectBalanced, rawRowCheck2573]

theorem rawRowCheck2574 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2574 := by decide +kernel

theorem rowCheck2574 : row2574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2574 := by decide +kernel

theorem rowEval2574 (x : Key → ℝ) : Integer.Sparse.eval row2574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2574, Integer.Sparse.eval_collectBalanced, rawRowCheck2574]

theorem rawRowCheck2575 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2575 := by decide +kernel

theorem rowCheck2575 : row2575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2575 := by decide +kernel

theorem rowEval2575 (x : Key → ℝ) : Integer.Sparse.eval row2575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2575, Integer.Sparse.eval_collectBalanced, rawRowCheck2575]

theorem rawRowCheck2576 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2576 := by decide +kernel

theorem rowCheck2576 : row2576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2576 := by decide +kernel

theorem rowEval2576 (x : Key → ℝ) : Integer.Sparse.eval row2576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2576, Integer.Sparse.eval_collectBalanced, rawRowCheck2576]

theorem rawRowCheck2577 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2577 := by decide +kernel

theorem rowCheck2577 : row2577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2577 := by decide +kernel

theorem rowEval2577 (x : Key → ℝ) : Integer.Sparse.eval row2577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2577, Integer.Sparse.eval_collectBalanced, rawRowCheck2577]

theorem rawRowCheck2578 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7 = rawRow2578 := by decide +kernel

theorem rowCheck2578 : row2578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2578 := by decide +kernel

theorem rowEval2578 (x : Key → ℝ) : Integer.Sparse.eval row2578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2578, Integer.Sparse.eval_collectBalanced, rawRowCheck2578]

theorem rawRowCheck2579 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7 = rawRow2579 := by decide +kernel

theorem rowCheck2579 : row2579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2579 := by decide +kernel

theorem rowEval2579 (x : Key → ℝ) : Integer.Sparse.eval row2579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2579, Integer.Sparse.eval_collectBalanced, rawRowCheck2579]

theorem rawRowCheck2580 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7 = rawRow2580 := by decide +kernel

theorem rowCheck2580 : row2580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2580 := by decide +kernel

theorem rowEval2580 (x : Key → ℝ) : Integer.Sparse.eval row2580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2580, Integer.Sparse.eval_collectBalanced, rawRowCheck2580]

theorem rawRowCheck2581 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2581 := by decide +kernel

theorem rowCheck2581 : row2581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2581 := by decide +kernel

theorem rowEval2581 (x : Key → ℝ) : Integer.Sparse.eval row2581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2581, Integer.Sparse.eval_collectBalanced, rawRowCheck2581]

theorem rawRowCheck2582 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2582 := by decide +kernel

theorem rowCheck2582 : row2582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2582 := by decide +kernel

theorem rowEval2582 (x : Key → ℝ) : Integer.Sparse.eval row2582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2582, Integer.Sparse.eval_collectBalanced, rawRowCheck2582]

theorem rawRowCheck2583 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2583 := by decide +kernel

theorem rowCheck2583 : row2583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2583 := by decide +kernel

theorem rowEval2583 (x : Key → ℝ) : Integer.Sparse.eval row2583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2583, Integer.Sparse.eval_collectBalanced, rawRowCheck2583]

theorem rawRowCheck2584 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow2584 := by decide +kernel

theorem rowCheck2584 : row2584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2584 := by decide +kernel

theorem rowEval2584 (x : Key → ℝ) : Integer.Sparse.eval row2584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2584, Integer.Sparse.eval_collectBalanced, rawRowCheck2584]

theorem rawRowCheck2585 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7 = rawRow2585 := by decide +kernel

theorem rowCheck2585 : row2585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2585 := by decide +kernel

theorem rowEval2585 (x : Key → ℝ) : Integer.Sparse.eval row2585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2585, Integer.Sparse.eval_collectBalanced, rawRowCheck2585]

theorem rawRowCheck2586 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7 = rawRow2586 := by decide +kernel

theorem rowCheck2586 : row2586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2586 := by decide +kernel

theorem rowEval2586 (x : Key → ℝ) : Integer.Sparse.eval row2586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2586, Integer.Sparse.eval_collectBalanced, rawRowCheck2586]

theorem rawRowCheck2587 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7 = rawRow2587 := by decide +kernel

theorem rowCheck2587 : row2587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2587 := by decide +kernel

theorem rowEval2587 (x : Key → ℝ) : Integer.Sparse.eval row2587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2587, Integer.Sparse.eval_collectBalanced, rawRowCheck2587]

theorem rawRowCheck2588 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2588 := by decide +kernel

theorem rowCheck2588 : row2588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2588 := by decide +kernel

theorem rowEval2588 (x : Key → ℝ) : Integer.Sparse.eval row2588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2588, Integer.Sparse.eval_collectBalanced, rawRowCheck2588]

theorem rawRowCheck2589 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2589 := by decide +kernel

theorem rowCheck2589 : row2589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2589 := by decide +kernel

theorem rowEval2589 (x : Key → ℝ) : Integer.Sparse.eval row2589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2589, Integer.Sparse.eval_collectBalanced, rawRowCheck2589]

theorem rawRowCheck2590 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2590 := by decide +kernel

theorem rowCheck2590 : row2590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2590 := by decide +kernel

theorem rowEval2590 (x : Key → ℝ) : Integer.Sparse.eval row2590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2590, Integer.Sparse.eval_collectBalanced, rawRowCheck2590]

theorem rawRowCheck2591 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2591 := by decide +kernel

theorem rowCheck2591 : row2591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2591 := by decide +kernel

theorem rowEval2591 (x : Key → ℝ) : Integer.Sparse.eval row2591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2591, Integer.Sparse.eval_collectBalanced, rawRowCheck2591]

theorem rawRowCheck2592 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8 = rawRow2592 := by decide +kernel

theorem rowCheck2592 : row2592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2592 := by decide +kernel

theorem rowEval2592 (x : Key → ℝ) : Integer.Sparse.eval row2592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2592, Integer.Sparse.eval_collectBalanced, rawRowCheck2592]

theorem rawRowCheck2593 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8 = rawRow2593 := by decide +kernel

theorem rowCheck2593 : row2593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2593 := by decide +kernel

theorem rowEval2593 (x : Key → ℝ) : Integer.Sparse.eval row2593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2593, Integer.Sparse.eval_collectBalanced, rawRowCheck2593]

theorem rawRowCheck2594 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8 = rawRow2594 := by decide +kernel

theorem rowCheck2594 : row2594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2594 := by decide +kernel

theorem rowEval2594 (x : Key → ℝ) : Integer.Sparse.eval row2594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2594, Integer.Sparse.eval_collectBalanced, rawRowCheck2594]

theorem rawRowCheck2595 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2595 := by decide +kernel

theorem rowCheck2595 : row2595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2595 := by decide +kernel

theorem rowEval2595 (x : Key → ℝ) : Integer.Sparse.eval row2595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2595, Integer.Sparse.eval_collectBalanced, rawRowCheck2595]

theorem rawRowCheck2596 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2596 := by decide +kernel

theorem rowCheck2596 : row2596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2596 := by decide +kernel

theorem rowEval2596 (x : Key → ℝ) : Integer.Sparse.eval row2596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2596, Integer.Sparse.eval_collectBalanced, rawRowCheck2596]

theorem rawRowCheck2597 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2597 := by decide +kernel

theorem rowCheck2597 : row2597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2597 := by decide +kernel

theorem rowEval2597 (x : Key → ℝ) : Integer.Sparse.eval row2597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2597, Integer.Sparse.eval_collectBalanced, rawRowCheck2597]

theorem rawRowCheck2598 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow2598 := by decide +kernel

theorem rowCheck2598 : row2598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2598 := by decide +kernel

theorem rowEval2598 (x : Key → ℝ) : Integer.Sparse.eval row2598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2598, Integer.Sparse.eval_collectBalanced, rawRowCheck2598]

theorem rawRowCheck2599 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8 = rawRow2599 := by decide +kernel

theorem rowCheck2599 : row2599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2599 := by decide +kernel

theorem rowEval2599 (x : Key → ℝ) : Integer.Sparse.eval row2599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2599, Integer.Sparse.eval_collectBalanced, rawRowCheck2599]

theorem rawRowCheck2600 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8 = rawRow2600 := by decide +kernel

theorem rowCheck2600 : row2600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2600 := by decide +kernel

theorem rowEval2600 (x : Key → ℝ) : Integer.Sparse.eval row2600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2600, Integer.Sparse.eval_collectBalanced, rawRowCheck2600]

theorem rawRowCheck2601 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8 = rawRow2601 := by decide +kernel

theorem rowCheck2601 : row2601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2601 := by decide +kernel

theorem rowEval2601 (x : Key → ℝ) : Integer.Sparse.eval row2601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2601, Integer.Sparse.eval_collectBalanced, rawRowCheck2601]

theorem rawRowCheck2602 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2602 := by decide +kernel

theorem rowCheck2602 : row2602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2602 := by decide +kernel

theorem rowEval2602 (x : Key → ℝ) : Integer.Sparse.eval row2602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2602, Integer.Sparse.eval_collectBalanced, rawRowCheck2602]

theorem rawRowCheck2603 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2603 := by decide +kernel

theorem rowCheck2603 : row2603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2603 := by decide +kernel

theorem rowEval2603 (x : Key → ℝ) : Integer.Sparse.eval row2603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2603, Integer.Sparse.eval_collectBalanced, rawRowCheck2603]

theorem rawRowCheck2604 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2604 := by decide +kernel

theorem rowCheck2604 : row2604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2604 := by decide +kernel

theorem rowEval2604 (x : Key → ℝ) : Integer.Sparse.eval row2604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2604, Integer.Sparse.eval_collectBalanced, rawRowCheck2604]

theorem rawRowCheck2605 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2605 := by decide +kernel

theorem rowCheck2605 : row2605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2605 := by decide +kernel

theorem rowEval2605 (x : Key → ℝ) : Integer.Sparse.eval row2605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2605, Integer.Sparse.eval_collectBalanced, rawRowCheck2605]

theorem rawRowCheck2606 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9 = rawRow2606 := by decide +kernel

theorem rowCheck2606 : row2606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2606 := by decide +kernel

theorem rowEval2606 (x : Key → ℝ) : Integer.Sparse.eval row2606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2606, Integer.Sparse.eval_collectBalanced, rawRowCheck2606]

theorem rawRowCheck2607 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9 = rawRow2607 := by decide +kernel

theorem rowCheck2607 : row2607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2607 := by decide +kernel

theorem rowEval2607 (x : Key → ℝ) : Integer.Sparse.eval row2607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2607, Integer.Sparse.eval_collectBalanced, rawRowCheck2607]

theorem rawRowCheck2608 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9 = rawRow2608 := by decide +kernel

theorem rowCheck2608 : row2608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2608 := by decide +kernel

theorem rowEval2608 (x : Key → ℝ) : Integer.Sparse.eval row2608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2608, Integer.Sparse.eval_collectBalanced, rawRowCheck2608]

theorem rawRowCheck2609 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2609 := by decide +kernel

theorem rowCheck2609 : row2609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2609 := by decide +kernel

theorem rowEval2609 (x : Key → ℝ) : Integer.Sparse.eval row2609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2609, Integer.Sparse.eval_collectBalanced, rawRowCheck2609]

theorem rawRowCheck2610 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2610 := by decide +kernel

theorem rowCheck2610 : row2610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2610 := by decide +kernel

theorem rowEval2610 (x : Key → ℝ) : Integer.Sparse.eval row2610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2610, Integer.Sparse.eval_collectBalanced, rawRowCheck2610]

theorem rawRowCheck2611 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2611 := by decide +kernel

theorem rowCheck2611 : row2611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2611 := by decide +kernel

theorem rowEval2611 (x : Key → ℝ) : Integer.Sparse.eval row2611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2611, Integer.Sparse.eval_collectBalanced, rawRowCheck2611]

theorem rawRowCheck2612 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2612 := by decide +kernel

theorem rowCheck2612 : row2612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2612 := by decide +kernel

theorem rowEval2612 (x : Key → ℝ) : Integer.Sparse.eval row2612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2612, Integer.Sparse.eval_collectBalanced, rawRowCheck2612]

theorem rawRowCheck2613 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9 = rawRow2613 := by decide +kernel

theorem rowCheck2613 : row2613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2613 := by decide +kernel

theorem rowEval2613 (x : Key → ℝ) : Integer.Sparse.eval row2613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2613, Integer.Sparse.eval_collectBalanced, rawRowCheck2613]

theorem rawRowCheck2614 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9 = rawRow2614 := by decide +kernel

theorem rowCheck2614 : row2614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2614 := by decide +kernel

theorem rowEval2614 (x : Key → ℝ) : Integer.Sparse.eval row2614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2614, Integer.Sparse.eval_collectBalanced, rawRowCheck2614]

theorem rawRowCheck2615 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9 = rawRow2615 := by decide +kernel

theorem rowCheck2615 : row2615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2615 := by decide +kernel

theorem rowEval2615 (x : Key → ℝ) : Integer.Sparse.eval row2615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2615, Integer.Sparse.eval_collectBalanced, rawRowCheck2615]

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

theorem rawRowCheck2630 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2630 := by decide +kernel

theorem rowCheck2630 : row2630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2630 := by decide +kernel

theorem rowEval2630 (x : Key → ℝ) : Integer.Sparse.eval row2630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2630, Integer.Sparse.eval_collectBalanced, rawRowCheck2630]

theorem rawRowCheck2631 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2631 := by decide +kernel

theorem rowCheck2631 : row2631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2631 := by decide +kernel

theorem rowEval2631 (x : Key → ℝ) : Integer.Sparse.eval row2631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2631, Integer.Sparse.eval_collectBalanced, rawRowCheck2631]

theorem rawRowCheck2632 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2632 := by decide +kernel

theorem rowCheck2632 : row2632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2632 := by decide +kernel

theorem rowEval2632 (x : Key → ℝ) : Integer.Sparse.eval row2632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2632, Integer.Sparse.eval_collectBalanced, rawRowCheck2632]

theorem rawRowCheck2633 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2633 := by decide +kernel

theorem rowCheck2633 : row2633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2633 := by decide +kernel

theorem rowEval2633 (x : Key → ℝ) : Integer.Sparse.eval row2633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2633, Integer.Sparse.eval_collectBalanced, rawRowCheck2633]

theorem rawRowCheck2634 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11 = rawRow2634 := by decide +kernel

theorem rowCheck2634 : row2634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2634 := by decide +kernel

theorem rowEval2634 (x : Key → ℝ) : Integer.Sparse.eval row2634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2634, Integer.Sparse.eval_collectBalanced, rawRowCheck2634]

theorem rawRowCheck2635 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11 = rawRow2635 := by decide +kernel

theorem rowCheck2635 : row2635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2635 := by decide +kernel

theorem rowEval2635 (x : Key → ℝ) : Integer.Sparse.eval row2635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2635, Integer.Sparse.eval_collectBalanced, rawRowCheck2635]

theorem rawRowCheck2636 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11 = rawRow2636 := by decide +kernel

theorem rowCheck2636 : row2636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2636 := by decide +kernel

theorem rowEval2636 (x : Key → ℝ) : Integer.Sparse.eval row2636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2636, Integer.Sparse.eval_collectBalanced, rawRowCheck2636]

theorem rawRowCheck2637 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2637 := by decide +kernel

theorem rowCheck2637 : row2637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2637 := by decide +kernel

theorem rowEval2637 (x : Key → ℝ) : Integer.Sparse.eval row2637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2637, Integer.Sparse.eval_collectBalanced, rawRowCheck2637]

theorem rawRowCheck2638 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2638 := by decide +kernel

theorem rowCheck2638 : row2638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2638 := by decide +kernel

theorem rowEval2638 (x : Key → ℝ) : Integer.Sparse.eval row2638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2638, Integer.Sparse.eval_collectBalanced, rawRowCheck2638]

theorem rawRowCheck2639 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2639 := by decide +kernel

theorem rowCheck2639 : row2639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2639 := by decide +kernel

theorem rowEval2639 (x : Key → ℝ) : Integer.Sparse.eval row2639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2639, Integer.Sparse.eval_collectBalanced, rawRowCheck2639]

theorem rawRowCheck2640 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2640 := by decide +kernel

theorem rowCheck2640 : row2640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2640 := by decide +kernel

theorem rowEval2640 (x : Key → ℝ) : Integer.Sparse.eval row2640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2640, Integer.Sparse.eval_collectBalanced, rawRowCheck2640]

theorem rawRowCheck2641 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11 = rawRow2641 := by decide +kernel

theorem rowCheck2641 : row2641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2641 := by decide +kernel

theorem rowEval2641 (x : Key → ℝ) : Integer.Sparse.eval row2641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2641, Integer.Sparse.eval_collectBalanced, rawRowCheck2641]

theorem rawRowCheck2642 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11 = rawRow2642 := by decide +kernel

theorem rowCheck2642 : row2642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2642 := by decide +kernel

theorem rowEval2642 (x : Key → ℝ) : Integer.Sparse.eval row2642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2642, Integer.Sparse.eval_collectBalanced, rawRowCheck2642]

theorem rawRowCheck2643 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11 = rawRow2643 := by decide +kernel

theorem rowCheck2643 : row2643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2643 := by decide +kernel

theorem rowEval2643 (x : Key → ℝ) : Integer.Sparse.eval row2643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2643, Integer.Sparse.eval_collectBalanced, rawRowCheck2643]

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

theorem rawRowCheck2658 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form13 = rawRow2658 := by decide +kernel

theorem rowCheck2658 : row2658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2658 := by decide +kernel

theorem rowEval2658 (x : Key → ℝ) : Integer.Sparse.eval row2658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck2658, Integer.Sparse.eval_collectBalanced, rawRowCheck2658]

theorem rawRowCheck2659 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form13 = rawRow2659 := by decide +kernel

theorem rowCheck2659 : row2659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2659 := by decide +kernel

theorem rowEval2659 (x : Key → ℝ) : Integer.Sparse.eval row2659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2659, Integer.Sparse.eval_collectBalanced, rawRowCheck2659]

theorem rawRowCheck2660 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form13 = rawRow2660 := by decide +kernel

theorem rowCheck2660 : row2660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2660 := by decide +kernel

theorem rowEval2660 (x : Key → ℝ) : Integer.Sparse.eval row2660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2660, Integer.Sparse.eval_collectBalanced, rawRowCheck2660]

theorem rawRowCheck2661 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form13 = rawRow2661 := by decide +kernel

theorem rowCheck2661 : row2661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2661 := by decide +kernel

theorem rowEval2661 (x : Key → ℝ) : Integer.Sparse.eval row2661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2661, Integer.Sparse.eval_collectBalanced, rawRowCheck2661]

theorem rawRowCheck2662 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form13 = rawRow2662 := by decide +kernel

theorem rowCheck2662 : row2662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2662 := by decide +kernel

theorem rowEval2662 (x : Key → ℝ) : Integer.Sparse.eval row2662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block1.form13) x := by
  rw [rowCheck2662, Integer.Sparse.eval_collectBalanced, rawRowCheck2662]

theorem rawRowCheck2663 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form13 = rawRow2663 := by decide +kernel

theorem rowCheck2663 : row2663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2663 := by decide +kernel

theorem rowEval2663 (x : Key → ℝ) : Integer.Sparse.eval row2663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2663, Integer.Sparse.eval_collectBalanced, rawRowCheck2663]

theorem rawRowCheck2664 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form13 = rawRow2664 := by decide +kernel

theorem rowCheck2664 : row2664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2664 := by decide +kernel

theorem rowEval2664 (x : Key → ℝ) : Integer.Sparse.eval row2664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2664, Integer.Sparse.eval_collectBalanced, rawRowCheck2664]

theorem rawRowCheck2665 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form13 = rawRow2665 := by decide +kernel

theorem rowCheck2665 : row2665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2665 := by decide +kernel

theorem rowEval2665 (x : Key → ℝ) : Integer.Sparse.eval row2665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2665, Integer.Sparse.eval_collectBalanced, rawRowCheck2665]

theorem rawRowCheck2666 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form13 = rawRow2666 := by decide +kernel

theorem rowCheck2666 : row2666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2666 := by decide +kernel

theorem rowEval2666 (x : Key → ℝ) : Integer.Sparse.eval row2666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2666, Integer.Sparse.eval_collectBalanced, rawRowCheck2666]

theorem rawRowCheck2667 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form13 = rawRow2667 := by decide +kernel

theorem rowCheck2667 : row2667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2667 := by decide +kernel

theorem rowEval2667 (x : Key → ℝ) : Integer.Sparse.eval row2667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2667, Integer.Sparse.eval_collectBalanced, rawRowCheck2667]

theorem rawRowCheck2668 : GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form13 = rawRow2668 := by decide +kernel

theorem rowCheck2668 : row2668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2668 := by decide +kernel

theorem rowEval2668 (x : Key → ℝ) : Integer.Sparse.eval row2668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, -1, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2668, Integer.Sparse.eval_collectBalanced, rawRowCheck2668]

theorem rawRowCheck2669 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form13 = rawRow2669 := by decide +kernel

theorem rowCheck2669 : row2669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2669 := by decide +kernel

theorem rowEval2669 (x : Key → ℝ) : Integer.Sparse.eval row2669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2669, Integer.Sparse.eval_collectBalanced, rawRowCheck2669]

theorem rawRowCheck2670 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form13 = rawRow2670 := by decide +kernel

theorem rowCheck2670 : row2670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2670 := by decide +kernel

theorem rowEval2670 (x : Key → ℝ) : Integer.Sparse.eval row2670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck2670, Integer.Sparse.eval_collectBalanced, rawRowCheck2670]

theorem rawRowCheck2671 : GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form13 = rawRow2671 := by decide +kernel

theorem rowCheck2671 : row2671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2671 := by decide +kernel

theorem rowEval2671 (x : Key → ℝ) : Integer.Sparse.eval row2671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck2671, Integer.Sparse.eval_collectBalanced, rawRowCheck2671]

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

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2490 x
  · exact rowEval2491 x
  · exact rowEval2492 x
  · exact rowEval2493 x
  · exact rowEval2494 x
  · exact rowEval2495 x
  · exact rowEval2496 x
  · exact rowEval2497 x
  · exact rowEval2498 x
  · exact rowEval2499 x
  · exact rowEval2500 x
  · exact rowEval2501 x
  · exact rowEval2502 x
  · exact rowEval2503 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

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

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2518 x
  · exact rowEval2519 x
  · exact rowEval2520 x
  · exact rowEval2521 x
  · exact rowEval2522 x
  · exact rowEval2523 x
  · exact rowEval2524 x
  · exact rowEval2525 x
  · exact rowEval2526 x
  · exact rowEval2527 x
  · exact rowEval2528 x
  · exact rowEval2529 x
  · exact rowEval2530 x
  · exact rowEval2531 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2532 x
  · exact rowEval2533 x
  · exact rowEval2534 x
  · exact rowEval2535 x
  · exact rowEval2536 x
  · exact rowEval2537 x
  · exact rowEval2538 x
  · exact rowEval2539 x
  · exact rowEval2540 x
  · exact rowEval2541 x
  · exact rowEval2542 x
  · exact rowEval2543 x
  · exact rowEval2544 x
  · exact rowEval2545 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

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

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2560 x
  · exact rowEval2561 x
  · exact rowEval2562 x
  · exact rowEval2563 x
  · exact rowEval2564 x
  · exact rowEval2565 x
  · exact rowEval2566 x
  · exact rowEval2567 x
  · exact rowEval2568 x
  · exact rowEval2569 x
  · exact rowEval2570 x
  · exact rowEval2571 x
  · exact rowEval2572 x
  · exact rowEval2573 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2574 x
  · exact rowEval2575 x
  · exact rowEval2576 x
  · exact rowEval2577 x
  · exact rowEval2578 x
  · exact rowEval2579 x
  · exact rowEval2580 x
  · exact rowEval2581 x
  · exact rowEval2582 x
  · exact rowEval2583 x
  · exact rowEval2584 x
  · exact rowEval2585 x
  · exact rowEval2586 x
  · exact rowEval2587 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2588 x
  · exact rowEval2589 x
  · exact rowEval2590 x
  · exact rowEval2591 x
  · exact rowEval2592 x
  · exact rowEval2593 x
  · exact rowEval2594 x
  · exact rowEval2595 x
  · exact rowEval2596 x
  · exact rowEval2597 x
  · exact rowEval2598 x
  · exact rowEval2599 x
  · exact rowEval2600 x
  · exact rowEval2601 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

theorem entryCheck13_9 : entry13_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_9 k)) := by decide +kernel

theorem rowsSound13_9 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2602 x
  · exact rowEval2603 x
  · exact rowEval2604 x
  · exact rowEval2605 x
  · exact rowEval2606 x
  · exact rowEval2607 x
  · exact rowEval2608 x
  · exact rowEval2609 x
  · exact rowEval2610 x
  · exact rowEval2611 x
  · exact rowEval2612 x
  · exact rowEval2613 x
  · exact rowEval2614 x
  · exact rowEval2615 x

theorem entryEval13_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_9 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck13_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_9]

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

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2630 x
  · exact rowEval2631 x
  · exact rowEval2632 x
  · exact rowEval2633 x
  · exact rowEval2634 x
  · exact rowEval2635 x
  · exact rowEval2636 x
  · exact rowEval2637 x
  · exact rowEval2638 x
  · exact rowEval2639 x
  · exact rowEval2640 x
  · exact rowEval2641 x
  · exact rowEval2642 x
  · exact rowEval2643 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

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

theorem entryCheck13_13 : entry13_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_13 k)) := by decide +kernel

theorem rowsSound13_13 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval2658 x
  · exact rowEval2659 x
  · exact rowEval2660 x
  · exact rowEval2661 x
  · exact rowEval2662 x
  · exact rowEval2663 x
  · exact rowEval2664 x
  · exact rowEval2665 x
  · exact rowEval2666 x
  · exact rowEval2667 x
  · exact rowEval2668 x
  · exact rowEval2669 x
  · exact rowEval2670 x
  · exact rowEval2671 x

theorem entryEval13_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_13 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck13_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_13]

end MUB6.Certificate.GramEntries.Block1

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

theorem rawRowCheck3632 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3632 := by decide +kernel

theorem rowCheck3632 : row3632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3632 := by decide +kernel

theorem rowEval3632 (x : Key → ℝ) : Integer.Sparse.eval row3632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3632, Integer.Sparse.eval_collectBalanced, rawRowCheck3632]

theorem rawRowCheck3633 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3633 := by decide +kernel

theorem rowCheck3633 : row3633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3633 := by decide +kernel

theorem rowEval3633 (x : Key → ℝ) : Integer.Sparse.eval row3633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3633, Integer.Sparse.eval_collectBalanced, rawRowCheck3633]

theorem rawRowCheck3634 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3634 := by decide +kernel

theorem rowCheck3634 : row3634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3634 := by decide +kernel

theorem rowEval3634 (x : Key → ℝ) : Integer.Sparse.eval row3634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3634, Integer.Sparse.eval_collectBalanced, rawRowCheck3634]

theorem rawRowCheck3635 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3635 := by decide +kernel

theorem rowCheck3635 : row3635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3635 := by decide +kernel

theorem rowEval3635 (x : Key → ℝ) : Integer.Sparse.eval row3635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3635, Integer.Sparse.eval_collectBalanced, rawRowCheck3635]

theorem rawRowCheck3636 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3636 := by decide +kernel

theorem rowCheck3636 : row3636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3636 := by decide +kernel

theorem rowEval3636 (x : Key → ℝ) : Integer.Sparse.eval row3636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3636, Integer.Sparse.eval_collectBalanced, rawRowCheck3636]

theorem rawRowCheck3637 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3637 := by decide +kernel

theorem rowCheck3637 : row3637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3637 := by decide +kernel

theorem rowEval3637 (x : Key → ℝ) : Integer.Sparse.eval row3637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3637, Integer.Sparse.eval_collectBalanced, rawRowCheck3637]

theorem rawRowCheck3638 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3638 := by decide +kernel

theorem rowCheck3638 : row3638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3638 := by decide +kernel

theorem rowEval3638 (x : Key → ℝ) : Integer.Sparse.eval row3638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3638, Integer.Sparse.eval_collectBalanced, rawRowCheck3638]

theorem rawRowCheck3639 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3639 := by decide +kernel

theorem rowCheck3639 : row3639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3639 := by decide +kernel

theorem rowEval3639 (x : Key → ℝ) : Integer.Sparse.eval row3639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3639, Integer.Sparse.eval_collectBalanced, rawRowCheck3639]

theorem rawRowCheck3640 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3640 := by decide +kernel

theorem rowCheck3640 : row3640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3640 := by decide +kernel

theorem rowEval3640 (x : Key → ℝ) : Integer.Sparse.eval row3640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3640, Integer.Sparse.eval_collectBalanced, rawRowCheck3640]

theorem rawRowCheck3641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3641 := by decide +kernel

theorem rowCheck3641 : row3641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3641 := by decide +kernel

theorem rowEval3641 (x : Key → ℝ) : Integer.Sparse.eval row3641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3641, Integer.Sparse.eval_collectBalanced, rawRowCheck3641]

theorem rawRowCheck3642 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3642 := by decide +kernel

theorem rowCheck3642 : row3642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3642 := by decide +kernel

theorem rowEval3642 (x : Key → ℝ) : Integer.Sparse.eval row3642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3642, Integer.Sparse.eval_collectBalanced, rawRowCheck3642]

theorem rawRowCheck3643 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3643 := by decide +kernel

theorem rowCheck3643 : row3643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3643 := by decide +kernel

theorem rowEval3643 (x : Key → ℝ) : Integer.Sparse.eval row3643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3643, Integer.Sparse.eval_collectBalanced, rawRowCheck3643]

theorem rawRowCheck3644 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3644 := by decide +kernel

theorem rowCheck3644 : row3644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3644 := by decide +kernel

theorem rowEval3644 (x : Key → ℝ) : Integer.Sparse.eval row3644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3644, Integer.Sparse.eval_collectBalanced, rawRowCheck3644]

theorem rawRowCheck3645 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3645 := by decide +kernel

theorem rowCheck3645 : row3645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3645 := by decide +kernel

theorem rowEval3645 (x : Key → ℝ) : Integer.Sparse.eval row3645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3645, Integer.Sparse.eval_collectBalanced, rawRowCheck3645]

theorem rawRowCheck3646 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3646 := by decide +kernel

theorem rowCheck3646 : row3646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3646 := by decide +kernel

theorem rowEval3646 (x : Key → ℝ) : Integer.Sparse.eval row3646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3646, Integer.Sparse.eval_collectBalanced, rawRowCheck3646]

theorem rawRowCheck3647 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3647 := by decide +kernel

theorem rowCheck3647 : row3647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3647 := by decide +kernel

theorem rowEval3647 (x : Key → ℝ) : Integer.Sparse.eval row3647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3647, Integer.Sparse.eval_collectBalanced, rawRowCheck3647]

theorem rawRowCheck3648 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3648 := by decide +kernel

theorem rowCheck3648 : row3648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3648 := by decide +kernel

theorem rowEval3648 (x : Key → ℝ) : Integer.Sparse.eval row3648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3648, Integer.Sparse.eval_collectBalanced, rawRowCheck3648]

theorem rawRowCheck3649 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3649 := by decide +kernel

theorem rowCheck3649 : row3649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3649 := by decide +kernel

theorem rowEval3649 (x : Key → ℝ) : Integer.Sparse.eval row3649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3649, Integer.Sparse.eval_collectBalanced, rawRowCheck3649]

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

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval3632 x
  · exact rowEval3633 x
  · exact rowEval3634 x
  · exact rowEval3635 x
  · exact rowEval3636 x
  · exact rowEval3637 x
  · exact rowEval3638 x
  · exact rowEval3639 x
  · exact rowEval3640 x
  · exact rowEval3641 x
  · exact rowEval3642 x
  · exact rowEval3643 x
  · exact rowEval3644 x
  · exact rowEval3645 x
  · exact rowEval3646 x
  · exact rowEval3647 x
  · exact rowEval3648 x
  · exact rowEval3649 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

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

theorem rawRowCheck4738 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form13 = rawRow4738 := by decide +kernel

theorem rowCheck4738 : row4738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4738 := by decide +kernel

theorem rowEval4738 (x : Key → ℝ) : Integer.Sparse.eval row4738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4738, Integer.Sparse.eval_collectBalanced, rawRowCheck4738]

theorem rawRowCheck4739 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form13 = rawRow4739 := by decide +kernel

theorem rowCheck4739 : row4739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4739 := by decide +kernel

theorem rowEval4739 (x : Key → ℝ) : Integer.Sparse.eval row4739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4739, Integer.Sparse.eval_collectBalanced, rawRowCheck4739]

theorem rawRowCheck4740 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form13 = rawRow4740 := by decide +kernel

theorem rowCheck4740 : row4740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4740 := by decide +kernel

theorem rowEval4740 (x : Key → ℝ) : Integer.Sparse.eval row4740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4740, Integer.Sparse.eval_collectBalanced, rawRowCheck4740]

theorem rawRowCheck4741 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form13 = rawRow4741 := by decide +kernel

theorem rowCheck4741 : row4741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4741 := by decide +kernel

theorem rowEval4741 (x : Key → ℝ) : Integer.Sparse.eval row4741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4741, Integer.Sparse.eval_collectBalanced, rawRowCheck4741]

theorem rawRowCheck4742 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form13 = rawRow4742 := by decide +kernel

theorem rowCheck4742 : row4742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4742 := by decide +kernel

theorem rowEval4742 (x : Key → ℝ) : Integer.Sparse.eval row4742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4742, Integer.Sparse.eval_collectBalanced, rawRowCheck4742]

theorem rawRowCheck4743 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form13 = rawRow4743 := by decide +kernel

theorem rowCheck4743 : row4743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4743 := by decide +kernel

theorem rowEval4743 (x : Key → ℝ) : Integer.Sparse.eval row4743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4743, Integer.Sparse.eval_collectBalanced, rawRowCheck4743]

theorem rawRowCheck4744 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form13 = rawRow4744 := by decide +kernel

theorem rowCheck4744 : row4744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4744 := by decide +kernel

theorem rowEval4744 (x : Key → ℝ) : Integer.Sparse.eval row4744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4744, Integer.Sparse.eval_collectBalanced, rawRowCheck4744]

theorem rawRowCheck4745 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4745 := by decide +kernel

theorem rowCheck4745 : row4745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4745 := by decide +kernel

theorem rowEval4745 (x : Key → ℝ) : Integer.Sparse.eval row4745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4745, Integer.Sparse.eval_collectBalanced, rawRowCheck4745]

theorem rawRowCheck4746 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4746 := by decide +kernel

theorem rowCheck4746 : row4746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4746 := by decide +kernel

theorem rowEval4746 (x : Key → ℝ) : Integer.Sparse.eval row4746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4746, Integer.Sparse.eval_collectBalanced, rawRowCheck4746]

theorem rawRowCheck4747 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4747 := by decide +kernel

theorem rowCheck4747 : row4747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4747 := by decide +kernel

theorem rowEval4747 (x : Key → ℝ) : Integer.Sparse.eval row4747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4747, Integer.Sparse.eval_collectBalanced, rawRowCheck4747]

theorem rawRowCheck4748 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form13 = rawRow4748 := by decide +kernel

theorem rowCheck4748 : row4748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4748 := by decide +kernel

theorem rowEval4748 (x : Key → ℝ) : Integer.Sparse.eval row4748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4748, Integer.Sparse.eval_collectBalanced, rawRowCheck4748]

theorem rawRowCheck4749 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4749 := by decide +kernel

theorem rowCheck4749 : row4749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4749 := by decide +kernel

theorem rowEval4749 (x : Key → ℝ) : Integer.Sparse.eval row4749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4749, Integer.Sparse.eval_collectBalanced, rawRowCheck4749]

theorem rawRowCheck4750 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4750 := by decide +kernel

theorem rowCheck4750 : row4750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4750 := by decide +kernel

theorem rowEval4750 (x : Key → ℝ) : Integer.Sparse.eval row4750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4750, Integer.Sparse.eval_collectBalanced, rawRowCheck4750]

theorem rawRowCheck4751 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4751 := by decide +kernel

theorem rowCheck4751 : row4751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4751 := by decide +kernel

theorem rowEval4751 (x : Key → ℝ) : Integer.Sparse.eval row4751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4751, Integer.Sparse.eval_collectBalanced, rawRowCheck4751]

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

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval4738 x
  · exact rowEval4739 x
  · exact rowEval4740 x
  · exact rowEval4741 x
  · exact rowEval4742 x
  · exact rowEval4743 x
  · exact rowEval4744 x
  · exact rowEval4745 x
  · exact rowEval4746 x
  · exact rowEval4747 x
  · exact rowEval4748 x
  · exact rowEval4749 x
  · exact rowEval4750 x
  · exact rowEval4751 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

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

theorem rawRowCheck5004 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5004 := by decide +kernel

theorem rowCheck5004 : row5004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5004 := by decide +kernel

theorem rowEval5004 (x : Key → ℝ) : Integer.Sparse.eval row5004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5004, Integer.Sparse.eval_collectBalanced, rawRowCheck5004]

theorem rawRowCheck5005 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5005 := by decide +kernel

theorem rowCheck5005 : row5005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5005 := by decide +kernel

theorem rowEval5005 (x : Key → ℝ) : Integer.Sparse.eval row5005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5005, Integer.Sparse.eval_collectBalanced, rawRowCheck5005]

theorem rawRowCheck5006 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5006 := by decide +kernel

theorem rowCheck5006 : row5006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5006 := by decide +kernel

theorem rowEval5006 (x : Key → ℝ) : Integer.Sparse.eval row5006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5006, Integer.Sparse.eval_collectBalanced, rawRowCheck5006]

theorem rawRowCheck5007 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5007 := by decide +kernel

theorem rowCheck5007 : row5007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5007 := by decide +kernel

theorem rowEval5007 (x : Key → ℝ) : Integer.Sparse.eval row5007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5007, Integer.Sparse.eval_collectBalanced, rawRowCheck5007]

theorem rawRowCheck5008 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5008 := by decide +kernel

theorem rowCheck5008 : row5008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5008 := by decide +kernel

theorem rowEval5008 (x : Key → ℝ) : Integer.Sparse.eval row5008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5008, Integer.Sparse.eval_collectBalanced, rawRowCheck5008]

theorem rawRowCheck5009 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5009 := by decide +kernel

theorem rowCheck5009 : row5009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5009 := by decide +kernel

theorem rowEval5009 (x : Key → ℝ) : Integer.Sparse.eval row5009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5009, Integer.Sparse.eval_collectBalanced, rawRowCheck5009]

theorem rawRowCheck5010 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5010 := by decide +kernel

theorem rowCheck5010 : row5010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5010 := by decide +kernel

theorem rowEval5010 (x : Key → ℝ) : Integer.Sparse.eval row5010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5010, Integer.Sparse.eval_collectBalanced, rawRowCheck5010]

theorem rawRowCheck5011 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5011 := by decide +kernel

theorem rowCheck5011 : row5011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5011 := by decide +kernel

theorem rowEval5011 (x : Key → ℝ) : Integer.Sparse.eval row5011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5011, Integer.Sparse.eval_collectBalanced, rawRowCheck5011]

theorem rawRowCheck5012 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5012 := by decide +kernel

theorem rowCheck5012 : row5012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5012 := by decide +kernel

theorem rowEval5012 (x : Key → ℝ) : Integer.Sparse.eval row5012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5012, Integer.Sparse.eval_collectBalanced, rawRowCheck5012]

theorem rawRowCheck5013 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5013 := by decide +kernel

theorem rowCheck5013 : row5013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5013 := by decide +kernel

theorem rowEval5013 (x : Key → ℝ) : Integer.Sparse.eval row5013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5013, Integer.Sparse.eval_collectBalanced, rawRowCheck5013]

theorem rawRowCheck5014 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5014 := by decide +kernel

theorem rowCheck5014 : row5014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5014 := by decide +kernel

theorem rowEval5014 (x : Key → ℝ) : Integer.Sparse.eval row5014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5014, Integer.Sparse.eval_collectBalanced, rawRowCheck5014]

theorem rawRowCheck5015 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5015 := by decide +kernel

theorem rowCheck5015 : row5015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5015 := by decide +kernel

theorem rowEval5015 (x : Key → ℝ) : Integer.Sparse.eval row5015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5015, Integer.Sparse.eval_collectBalanced, rawRowCheck5015]

theorem rawRowCheck5016 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5016 := by decide +kernel

theorem rowCheck5016 : row5016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5016 := by decide +kernel

theorem rowEval5016 (x : Key → ℝ) : Integer.Sparse.eval row5016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5016, Integer.Sparse.eval_collectBalanced, rawRowCheck5016]

theorem rawRowCheck5017 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5017 := by decide +kernel

theorem rowCheck5017 : row5017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5017 := by decide +kernel

theorem rowEval5017 (x : Key → ℝ) : Integer.Sparse.eval row5017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5017, Integer.Sparse.eval_collectBalanced, rawRowCheck5017]

theorem rawRowCheck5018 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5018 := by decide +kernel

theorem rowCheck5018 : row5018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5018 := by decide +kernel

theorem rowEval5018 (x : Key → ℝ) : Integer.Sparse.eval row5018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5018, Integer.Sparse.eval_collectBalanced, rawRowCheck5018]

theorem rawRowCheck5019 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5019 := by decide +kernel

theorem rowCheck5019 : row5019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5019 := by decide +kernel

theorem rowEval5019 (x : Key → ℝ) : Integer.Sparse.eval row5019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5019, Integer.Sparse.eval_collectBalanced, rawRowCheck5019]

theorem rawRowCheck5020 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5020 := by decide +kernel

theorem rowCheck5020 : row5020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5020 := by decide +kernel

theorem rowEval5020 (x : Key → ℝ) : Integer.Sparse.eval row5020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5020, Integer.Sparse.eval_collectBalanced, rawRowCheck5020]

theorem rawRowCheck5021 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5021 := by decide +kernel

theorem rowCheck5021 : row5021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5021 := by decide +kernel

theorem rowEval5021 (x : Key → ℝ) : Integer.Sparse.eval row5021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5021, Integer.Sparse.eval_collectBalanced, rawRowCheck5021]

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

theorem entryCheck20_13 : entry20_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form20.terms k).coefficient) (rows20_13 k)) := by decide +kernel

theorem rowsSound20_13 (k : Fin GramFunctions.Block1.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form20.terms k).tag (GramFunctions.Block1.form20.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval5004 x
  · exact rowEval5005 x
  · exact rowEval5006 x
  · exact rowEval5007 x
  · exact rowEval5008 x
  · exact rowEval5009 x
  · exact rowEval5010 x
  · exact rowEval5011 x
  · exact rowEval5012 x
  · exact rowEval5013 x
  · exact rowEval5014 x
  · exact rowEval5015 x
  · exact rowEval5016 x
  · exact rowEval5017 x
  · exact rowEval5018 x
  · exact rowEval5019 x
  · exact rowEval5020 x
  · exact rowEval5021 x

theorem entryEval20_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_13 (GramNormalization.eval B) = GramFunctions.Block1.form20.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck20_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form20 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_13]

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

theorem entryEvalRow13_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 13 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 13).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval13_0 B hB
  · exact entryEval13_1 B hB
  · exact entryEval13_2 B hB
  · exact entryEval13_3 B hB
  · exact entryEval13_4 B hB
  · exact entryEval13_5 B hB
  · exact entryEval13_6 B hB
  · exact entryEval13_7 B hB
  · exact entryEval13_8 B hB
  · exact entryEval13_9 B hB
  · exact entryEval13_10 B hB
  · exact entryEval13_11 B hB
  · exact entryEval13_12 B hB
  · exact entryEval13_13 B hB
  · exact (entryEval14_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_13_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_13 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e_oai
