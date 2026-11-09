-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:57:14.876543+00:00
-- url     : https://prove2.me/submissions/9c4ec389-d3cd-4a59-bcad-f8b1fc04ab0a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval2_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_2_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck126 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form0 = rawRow126 := by decide +kernel

theorem rowCheck126 : row126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow126 := by decide +kernel

theorem rowEval126 (x : Key → ℝ) : Integer.Sparse.eval row126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck126, Integer.Sparse.eval_collectBalanced, rawRowCheck126]

theorem rawRowCheck127 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form0 = rawRow127 := by decide +kernel

theorem rowCheck127 : row127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow127 := by decide +kernel

theorem rowEval127 (x : Key → ℝ) : Integer.Sparse.eval row127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck127, Integer.Sparse.eval_collectBalanced, rawRowCheck127]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck128 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form0 = rawRow128 := by decide +kernel

theorem rowCheck128 : row128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow128 := by decide +kernel

theorem rowEval128 (x : Key → ℝ) : Integer.Sparse.eval row128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck128, Integer.Sparse.eval_collectBalanced, rawRowCheck128]

theorem rawRowCheck129 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form0 = rawRow129 := by decide +kernel

theorem rowCheck129 : row129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow129 := by decide +kernel

theorem rowEval129 (x : Key → ℝ) : Integer.Sparse.eval row129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck129, Integer.Sparse.eval_collectBalanced, rawRowCheck129]

theorem rawRowCheck130 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form0 = rawRow130 := by decide +kernel

theorem rowCheck130 : row130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow130 := by decide +kernel

theorem rowEval130 (x : Key → ℝ) : Integer.Sparse.eval row130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck130, Integer.Sparse.eval_collectBalanced, rawRowCheck130]

theorem rawRowCheck131 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form0 = rawRow131 := by decide +kernel

theorem rowCheck131 : row131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow131 := by decide +kernel

theorem rowEval131 (x : Key → ℝ) : Integer.Sparse.eval row131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck131, Integer.Sparse.eval_collectBalanced, rawRowCheck131]

theorem rawRowCheck132 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form0 = rawRow132 := by decide +kernel

theorem rowCheck132 : row132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow132 := by decide +kernel

theorem rowEval132 (x : Key → ℝ) : Integer.Sparse.eval row132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck132, Integer.Sparse.eval_collectBalanced, rawRowCheck132]

theorem rawRowCheck133 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow133 := by decide +kernel

theorem rowCheck133 : row133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow133 := by decide +kernel

theorem rowEval133 (x : Key → ℝ) : Integer.Sparse.eval row133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck133, Integer.Sparse.eval_collectBalanced, rawRowCheck133]

theorem rawRowCheck134 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow134 := by decide +kernel

theorem rowCheck134 : row134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow134 := by decide +kernel

theorem rowEval134 (x : Key → ℝ) : Integer.Sparse.eval row134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck134, Integer.Sparse.eval_collectBalanced, rawRowCheck134]

theorem rawRowCheck135 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow135 := by decide +kernel

theorem rowCheck135 : row135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow135 := by decide +kernel

theorem rowEval135 (x : Key → ℝ) : Integer.Sparse.eval row135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck135, Integer.Sparse.eval_collectBalanced, rawRowCheck135]

theorem rawRowCheck136 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form0 = rawRow136 := by decide +kernel

theorem rowCheck136 : row136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow136 := by decide +kernel

theorem rowEval136 (x : Key → ℝ) : Integer.Sparse.eval row136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck136, Integer.Sparse.eval_collectBalanced, rawRowCheck136]

theorem rawRowCheck137 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form0 = rawRow137 := by decide +kernel

theorem rowCheck137 : row137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow137 := by decide +kernel

theorem rowEval137 (x : Key → ℝ) : Integer.Sparse.eval row137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck137, Integer.Sparse.eval_collectBalanced, rawRowCheck137]

theorem rawRowCheck138 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form0 = rawRow138 := by decide +kernel

theorem rowCheck138 : row138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow138 := by decide +kernel

theorem rowEval138 (x : Key → ℝ) : Integer.Sparse.eval row138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck138, Integer.Sparse.eval_collectBalanced, rawRowCheck138]

theorem rawRowCheck139 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form0 = rawRow139 := by decide +kernel

theorem rowCheck139 : row139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow139 := by decide +kernel

theorem rowEval139 (x : Key → ℝ) : Integer.Sparse.eval row139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck139, Integer.Sparse.eval_collectBalanced, rawRowCheck139]

theorem rawRowCheck140 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form0 = rawRow140 := by decide +kernel

theorem rowCheck140 : row140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow140 := by decide +kernel

theorem rowEval140 (x : Key → ℝ) : Integer.Sparse.eval row140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck140, Integer.Sparse.eval_collectBalanced, rawRowCheck140]

theorem rawRowCheck141 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form0 = rawRow141 := by decide +kernel

theorem rowCheck141 : row141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow141 := by decide +kernel

theorem rowEval141 (x : Key → ℝ) : Integer.Sparse.eval row141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck141, Integer.Sparse.eval_collectBalanced, rawRowCheck141]

theorem rawRowCheck142 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form0 = rawRow142 := by decide +kernel

theorem rowCheck142 : row142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow142 := by decide +kernel

theorem rowEval142 (x : Key → ℝ) : Integer.Sparse.eval row142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck142, Integer.Sparse.eval_collectBalanced, rawRowCheck142]

theorem rawRowCheck143 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form0 = rawRow143 := by decide +kernel

theorem rowCheck143 : row143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow143 := by decide +kernel

theorem rowEval143 (x : Key → ℝ) : Integer.Sparse.eval row143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck143, Integer.Sparse.eval_collectBalanced, rawRowCheck143]

theorem rawRowCheck144 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form0 = rawRow144 := by decide +kernel

theorem rowCheck144 : row144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow144 := by decide +kernel

theorem rowEval144 (x : Key → ℝ) : Integer.Sparse.eval row144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck144, Integer.Sparse.eval_collectBalanced, rawRowCheck144]

theorem rawRowCheck145 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form0 = rawRow145 := by decide +kernel

theorem rowCheck145 : row145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow145 := by decide +kernel

theorem rowEval145 (x : Key → ℝ) : Integer.Sparse.eval row145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck145, Integer.Sparse.eval_collectBalanced, rawRowCheck145]

theorem rawRowCheck146 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form0 = rawRow146 := by decide +kernel

theorem rowCheck146 : row146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow146 := by decide +kernel

theorem rowEval146 (x : Key → ℝ) : Integer.Sparse.eval row146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck146, Integer.Sparse.eval_collectBalanced, rawRowCheck146]

theorem rawRowCheck147 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form0 = rawRow147 := by decide +kernel

theorem rowCheck147 : row147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow147 := by decide +kernel

theorem rowEval147 (x : Key → ℝ) : Integer.Sparse.eval row147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck147, Integer.Sparse.eval_collectBalanced, rawRowCheck147]

theorem rawRowCheck148 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form0 = rawRow148 := by decide +kernel

theorem rowCheck148 : row148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow148 := by decide +kernel

theorem rowEval148 (x : Key → ℝ) : Integer.Sparse.eval row148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck148, Integer.Sparse.eval_collectBalanced, rawRowCheck148]

theorem rawRowCheck149 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form0 = rawRow149 := by decide +kernel

theorem rowCheck149 : row149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow149 := by decide +kernel

theorem rowEval149 (x : Key → ℝ) : Integer.Sparse.eval row149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck149, Integer.Sparse.eval_collectBalanced, rawRowCheck149]

theorem rawRowCheck150 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form0 = rawRow150 := by decide +kernel

theorem rowCheck150 : row150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow150 := by decide +kernel

theorem rowEval150 (x : Key → ℝ) : Integer.Sparse.eval row150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck150, Integer.Sparse.eval_collectBalanced, rawRowCheck150]

theorem rawRowCheck151 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form0 = rawRow151 := by decide +kernel

theorem rowCheck151 : row151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow151 := by decide +kernel

theorem rowEval151 (x : Key → ℝ) : Integer.Sparse.eval row151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck151, Integer.Sparse.eval_collectBalanced, rawRowCheck151]

theorem rawRowCheck152 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form0 = rawRow152 := by decide +kernel

theorem rowCheck152 : row152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow152 := by decide +kernel

theorem rowEval152 (x : Key → ℝ) : Integer.Sparse.eval row152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck152, Integer.Sparse.eval_collectBalanced, rawRowCheck152]

theorem rawRowCheck153 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form0 = rawRow153 := by decide +kernel

theorem rowCheck153 : row153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow153 := by decide +kernel

theorem rowEval153 (x : Key → ℝ) : Integer.Sparse.eval row153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck153, Integer.Sparse.eval_collectBalanced, rawRowCheck153]

theorem rawRowCheck154 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form0 = rawRow154 := by decide +kernel

theorem rowCheck154 : row154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow154 := by decide +kernel

theorem rowEval154 (x : Key → ℝ) : Integer.Sparse.eval row154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck154, Integer.Sparse.eval_collectBalanced, rawRowCheck154]

theorem rawRowCheck155 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form0 = rawRow155 := by decide +kernel

theorem rowCheck155 : row155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow155 := by decide +kernel

theorem rowEval155 (x : Key → ℝ) : Integer.Sparse.eval row155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck155, Integer.Sparse.eval_collectBalanced, rawRowCheck155]

theorem rawRowCheck156 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form0 = rawRow156 := by decide +kernel

theorem rowCheck156 : row156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow156 := by decide +kernel

theorem rowEval156 (x : Key → ℝ) : Integer.Sparse.eval row156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck156, Integer.Sparse.eval_collectBalanced, rawRowCheck156]

theorem rawRowCheck157 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form0 = rawRow157 := by decide +kernel

theorem rowCheck157 : row157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow157 := by decide +kernel

theorem rowEval157 (x : Key → ℝ) : Integer.Sparse.eval row157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck157, Integer.Sparse.eval_collectBalanced, rawRowCheck157]

theorem rawRowCheck158 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow158 := by decide +kernel

theorem rowCheck158 : row158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow158 := by decide +kernel

theorem rowEval158 (x : Key → ℝ) : Integer.Sparse.eval row158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck158, Integer.Sparse.eval_collectBalanced, rawRowCheck158]

theorem rawRowCheck159 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow159 := by decide +kernel

theorem rowCheck159 : row159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow159 := by decide +kernel

theorem rowEval159 (x : Key → ℝ) : Integer.Sparse.eval row159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck159, Integer.Sparse.eval_collectBalanced, rawRowCheck159]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck160 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow160 := by decide +kernel

theorem rowCheck160 : row160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow160 := by decide +kernel

theorem rowEval160 (x : Key → ℝ) : Integer.Sparse.eval row160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck160, Integer.Sparse.eval_collectBalanced, rawRowCheck160]

theorem rawRowCheck161 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow161 := by decide +kernel

theorem rowCheck161 : row161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow161 := by decide +kernel

theorem rowEval161 (x : Key → ℝ) : Integer.Sparse.eval row161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck161, Integer.Sparse.eval_collectBalanced, rawRowCheck161]

theorem rawRowCheck162 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow162 := by decide +kernel

theorem rowCheck162 : row162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow162 := by decide +kernel

theorem rowEval162 (x : Key → ℝ) : Integer.Sparse.eval row162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck162, Integer.Sparse.eval_collectBalanced, rawRowCheck162]

theorem rawRowCheck163 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow163 := by decide +kernel

theorem rowCheck163 : row163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow163 := by decide +kernel

theorem rowEval163 (x : Key → ℝ) : Integer.Sparse.eval row163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck163, Integer.Sparse.eval_collectBalanced, rawRowCheck163]

theorem rawRowCheck164 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form0 = rawRow164 := by decide +kernel

theorem rowCheck164 : row164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow164 := by decide +kernel

theorem rowEval164 (x : Key → ℝ) : Integer.Sparse.eval row164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck164, Integer.Sparse.eval_collectBalanced, rawRowCheck164]

theorem rawRowCheck165 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form0 = rawRow165 := by decide +kernel

theorem rowCheck165 : row165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow165 := by decide +kernel

theorem rowEval165 (x : Key → ℝ) : Integer.Sparse.eval row165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck165, Integer.Sparse.eval_collectBalanced, rawRowCheck165]

theorem rawRowCheck166 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form0 = rawRow166 := by decide +kernel

theorem rowCheck166 : row166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow166 := by decide +kernel

theorem rowEval166 (x : Key → ℝ) : Integer.Sparse.eval row166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck166, Integer.Sparse.eval_collectBalanced, rawRowCheck166]

theorem rawRowCheck167 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form0 = rawRow167 := by decide +kernel

theorem rowCheck167 : row167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow167 := by decide +kernel

theorem rowEval167 (x : Key → ℝ) : Integer.Sparse.eval row167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck167, Integer.Sparse.eval_collectBalanced, rawRowCheck167]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck210 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form2 = rawRow210 := by decide +kernel

theorem rowCheck210 : row210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow210 := by decide +kernel

theorem rowEval210 (x : Key → ℝ) : Integer.Sparse.eval row210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck210, Integer.Sparse.eval_collectBalanced, rawRowCheck210]

theorem rawRowCheck211 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form2 = rawRow211 := by decide +kernel

theorem rowCheck211 : row211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow211 := by decide +kernel

theorem rowEval211 (x : Key → ℝ) : Integer.Sparse.eval row211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck211, Integer.Sparse.eval_collectBalanced, rawRowCheck211]

theorem rawRowCheck212 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form2 = rawRow212 := by decide +kernel

theorem rowCheck212 : row212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow212 := by decide +kernel

theorem rowEval212 (x : Key → ℝ) : Integer.Sparse.eval row212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck212, Integer.Sparse.eval_collectBalanced, rawRowCheck212]

theorem rawRowCheck213 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form2 = rawRow213 := by decide +kernel

theorem rowCheck213 : row213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow213 := by decide +kernel

theorem rowEval213 (x : Key → ℝ) : Integer.Sparse.eval row213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck213, Integer.Sparse.eval_collectBalanced, rawRowCheck213]

theorem rawRowCheck214 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form2 = rawRow214 := by decide +kernel

theorem rowCheck214 : row214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow214 := by decide +kernel

theorem rowEval214 (x : Key → ℝ) : Integer.Sparse.eval row214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck214, Integer.Sparse.eval_collectBalanced, rawRowCheck214]

theorem rawRowCheck215 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form2 = rawRow215 := by decide +kernel

theorem rowCheck215 : row215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow215 := by decide +kernel

theorem rowEval215 (x : Key → ℝ) : Integer.Sparse.eval row215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck215, Integer.Sparse.eval_collectBalanced, rawRowCheck215]

theorem rawRowCheck216 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form2 = rawRow216 := by decide +kernel

theorem rowCheck216 : row216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow216 := by decide +kernel

theorem rowEval216 (x : Key → ℝ) : Integer.Sparse.eval row216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck216, Integer.Sparse.eval_collectBalanced, rawRowCheck216]

theorem rawRowCheck217 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form2 = rawRow217 := by decide +kernel

theorem rowCheck217 : row217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow217 := by decide +kernel

theorem rowEval217 (x : Key → ℝ) : Integer.Sparse.eval row217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck217, Integer.Sparse.eval_collectBalanced, rawRowCheck217]

theorem rawRowCheck218 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form2 = rawRow218 := by decide +kernel

theorem rowCheck218 : row218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow218 := by decide +kernel

theorem rowEval218 (x : Key → ℝ) : Integer.Sparse.eval row218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck218, Integer.Sparse.eval_collectBalanced, rawRowCheck218]

theorem rawRowCheck219 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form2 = rawRow219 := by decide +kernel

theorem rowCheck219 : row219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow219 := by decide +kernel

theorem rowEval219 (x : Key → ℝ) : Integer.Sparse.eval row219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck219, Integer.Sparse.eval_collectBalanced, rawRowCheck219]

theorem rawRowCheck220 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form2 = rawRow220 := by decide +kernel

theorem rowCheck220 : row220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow220 := by decide +kernel

theorem rowEval220 (x : Key → ℝ) : Integer.Sparse.eval row220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck220, Integer.Sparse.eval_collectBalanced, rawRowCheck220]

theorem rawRowCheck221 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form2 = rawRow221 := by decide +kernel

theorem rowCheck221 : row221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow221 := by decide +kernel

theorem rowEval221 (x : Key → ℝ) : Integer.Sparse.eval row221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck221, Integer.Sparse.eval_collectBalanced, rawRowCheck221]

theorem rawRowCheck222 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form2 = rawRow222 := by decide +kernel

theorem rowCheck222 : row222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow222 := by decide +kernel

theorem rowEval222 (x : Key → ℝ) : Integer.Sparse.eval row222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck222, Integer.Sparse.eval_collectBalanced, rawRowCheck222]

theorem rawRowCheck223 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form2 = rawRow223 := by decide +kernel

theorem rowCheck223 : row223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow223 := by decide +kernel

theorem rowEval223 (x : Key → ℝ) : Integer.Sparse.eval row223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck223, Integer.Sparse.eval_collectBalanced, rawRowCheck223]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck224 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form2 = rawRow224 := by decide +kernel

theorem rowCheck224 : row224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow224 := by decide +kernel

theorem rowEval224 (x : Key → ℝ) : Integer.Sparse.eval row224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck224, Integer.Sparse.eval_collectBalanced, rawRowCheck224]

theorem rawRowCheck225 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form2 = rawRow225 := by decide +kernel

theorem rowCheck225 : row225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow225 := by decide +kernel

theorem rowEval225 (x : Key → ℝ) : Integer.Sparse.eval row225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck225, Integer.Sparse.eval_collectBalanced, rawRowCheck225]

theorem rawRowCheck226 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form2 = rawRow226 := by decide +kernel

theorem rowCheck226 : row226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow226 := by decide +kernel

theorem rowEval226 (x : Key → ℝ) : Integer.Sparse.eval row226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck226, Integer.Sparse.eval_collectBalanced, rawRowCheck226]

theorem rawRowCheck227 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form2 = rawRow227 := by decide +kernel

theorem rowCheck227 : row227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow227 := by decide +kernel

theorem rowEval227 (x : Key → ℝ) : Integer.Sparse.eval row227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck227, Integer.Sparse.eval_collectBalanced, rawRowCheck227]

theorem rawRowCheck228 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form2 = rawRow228 := by decide +kernel

theorem rowCheck228 : row228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow228 := by decide +kernel

theorem rowEval228 (x : Key → ℝ) : Integer.Sparse.eval row228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck228, Integer.Sparse.eval_collectBalanced, rawRowCheck228]

theorem rawRowCheck229 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form2 = rawRow229 := by decide +kernel

theorem rowCheck229 : row229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow229 := by decide +kernel

theorem rowEval229 (x : Key → ℝ) : Integer.Sparse.eval row229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck229, Integer.Sparse.eval_collectBalanced, rawRowCheck229]

theorem rawRowCheck230 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form2 = rawRow230 := by decide +kernel

theorem rowCheck230 : row230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow230 := by decide +kernel

theorem rowEval230 (x : Key → ℝ) : Integer.Sparse.eval row230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck230, Integer.Sparse.eval_collectBalanced, rawRowCheck230]

theorem rawRowCheck231 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form2 = rawRow231 := by decide +kernel

theorem rowCheck231 : row231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow231 := by decide +kernel

theorem rowEval231 (x : Key → ℝ) : Integer.Sparse.eval row231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck231, Integer.Sparse.eval_collectBalanced, rawRowCheck231]

theorem rawRowCheck232 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form2 = rawRow232 := by decide +kernel

theorem rowCheck232 : row232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow232 := by decide +kernel

theorem rowEval232 (x : Key → ℝ) : Integer.Sparse.eval row232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck232, Integer.Sparse.eval_collectBalanced, rawRowCheck232]

theorem rawRowCheck233 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form2 = rawRow233 := by decide +kernel

theorem rowCheck233 : row233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow233 := by decide +kernel

theorem rowEval233 (x : Key → ℝ) : Integer.Sparse.eval row233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck233, Integer.Sparse.eval_collectBalanced, rawRowCheck233]

theorem rawRowCheck234 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form2 = rawRow234 := by decide +kernel

theorem rowCheck234 : row234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow234 := by decide +kernel

theorem rowEval234 (x : Key → ℝ) : Integer.Sparse.eval row234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form2) x := by
  rw [rowCheck234, Integer.Sparse.eval_collectBalanced, rawRowCheck234]

theorem rawRowCheck235 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form2 = rawRow235 := by decide +kernel

theorem rowCheck235 : row235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow235 := by decide +kernel

theorem rowEval235 (x : Key → ℝ) : Integer.Sparse.eval row235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck235, Integer.Sparse.eval_collectBalanced, rawRowCheck235]

theorem rawRowCheck236 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form2 = rawRow236 := by decide +kernel

theorem rowCheck236 : row236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow236 := by decide +kernel

theorem rowEval236 (x : Key → ℝ) : Integer.Sparse.eval row236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck236, Integer.Sparse.eval_collectBalanced, rawRowCheck236]

theorem rawRowCheck237 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form2 = rawRow237 := by decide +kernel

theorem rowCheck237 : row237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow237 := by decide +kernel

theorem rowEval237 (x : Key → ℝ) : Integer.Sparse.eval row237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck237, Integer.Sparse.eval_collectBalanced, rawRowCheck237]

theorem rawRowCheck238 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form2 = rawRow238 := by decide +kernel

theorem rowCheck238 : row238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow238 := by decide +kernel

theorem rowEval238 (x : Key → ℝ) : Integer.Sparse.eval row238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck238, Integer.Sparse.eval_collectBalanced, rawRowCheck238]

theorem rawRowCheck239 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form2 = rawRow239 := by decide +kernel

theorem rowCheck239 : row239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow239 := by decide +kernel

theorem rowEval239 (x : Key → ℝ) : Integer.Sparse.eval row239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck239, Integer.Sparse.eval_collectBalanced, rawRowCheck239]

theorem rawRowCheck240 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form2 = rawRow240 := by decide +kernel

theorem rowCheck240 : row240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow240 := by decide +kernel

theorem rowEval240 (x : Key → ℝ) : Integer.Sparse.eval row240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck240, Integer.Sparse.eval_collectBalanced, rawRowCheck240]

theorem rawRowCheck241 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form2 = rawRow241 := by decide +kernel

theorem rowCheck241 : row241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow241 := by decide +kernel

theorem rowEval241 (x : Key → ℝ) : Integer.Sparse.eval row241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck241, Integer.Sparse.eval_collectBalanced, rawRowCheck241]

theorem rawRowCheck242 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form2 = rawRow242 := by decide +kernel

theorem rowCheck242 : row242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow242 := by decide +kernel

theorem rowEval242 (x : Key → ℝ) : Integer.Sparse.eval row242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck242, Integer.Sparse.eval_collectBalanced, rawRowCheck242]

theorem rawRowCheck243 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form2 = rawRow243 := by decide +kernel

theorem rowCheck243 : row243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow243 := by decide +kernel

theorem rowEval243 (x : Key → ℝ) : Integer.Sparse.eval row243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck243, Integer.Sparse.eval_collectBalanced, rawRowCheck243]

theorem rawRowCheck244 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form2 = rawRow244 := by decide +kernel

theorem rowCheck244 : row244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow244 := by decide +kernel

theorem rowEval244 (x : Key → ℝ) : Integer.Sparse.eval row244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck244, Integer.Sparse.eval_collectBalanced, rawRowCheck244]

theorem rawRowCheck245 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form2 = rawRow245 := by decide +kernel

theorem rowCheck245 : row245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow245 := by decide +kernel

theorem rowEval245 (x : Key → ℝ) : Integer.Sparse.eval row245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck245, Integer.Sparse.eval_collectBalanced, rawRowCheck245]

theorem rawRowCheck246 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form2 = rawRow246 := by decide +kernel

theorem rowCheck246 : row246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow246 := by decide +kernel

theorem rowEval246 (x : Key → ℝ) : Integer.Sparse.eval row246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck246, Integer.Sparse.eval_collectBalanced, rawRowCheck246]

theorem rawRowCheck247 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form2 = rawRow247 := by decide +kernel

theorem rowCheck247 : row247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow247 := by decide +kernel

theorem rowEval247 (x : Key → ℝ) : Integer.Sparse.eval row247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck247, Integer.Sparse.eval_collectBalanced, rawRowCheck247]

theorem rawRowCheck248 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form2 = rawRow248 := by decide +kernel

theorem rowCheck248 : row248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow248 := by decide +kernel

theorem rowEval248 (x : Key → ℝ) : Integer.Sparse.eval row248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck248, Integer.Sparse.eval_collectBalanced, rawRowCheck248]

theorem rawRowCheck249 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form2 = rawRow249 := by decide +kernel

theorem rowCheck249 : row249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow249 := by decide +kernel

theorem rowEval249 (x : Key → ℝ) : Integer.Sparse.eval row249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck249, Integer.Sparse.eval_collectBalanced, rawRowCheck249]

theorem rawRowCheck250 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form2 = rawRow250 := by decide +kernel

theorem rowCheck250 : row250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow250 := by decide +kernel

theorem rowEval250 (x : Key → ℝ) : Integer.Sparse.eval row250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck250, Integer.Sparse.eval_collectBalanced, rawRowCheck250]

theorem rawRowCheck251 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form2 = rawRow251 := by decide +kernel

theorem rowCheck251 : row251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow251 := by decide +kernel

theorem rowEval251 (x : Key → ℝ) : Integer.Sparse.eval row251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck251, Integer.Sparse.eval_collectBalanced, rawRowCheck251]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block0.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form2.terms k).tag (GramFunctions.Block0.form2.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval126 x
  · exact rowEval127 x
  · exact rowEval128 x
  · exact rowEval129 x
  · exact rowEval130 x
  · exact rowEval131 x
  · exact rowEval132 x
  · exact rowEval133 x
  · exact rowEval134 x
  · exact rowEval135 x
  · exact rowEval136 x
  · exact rowEval137 x
  · exact rowEval138 x
  · exact rowEval139 x
  · exact rowEval140 x
  · exact rowEval141 x
  · exact rowEval142 x
  · exact rowEval143 x
  · exact rowEval144 x
  · exact rowEval145 x
  · exact rowEval146 x
  · exact rowEval147 x
  · exact rowEval148 x
  · exact rowEval149 x
  · exact rowEval150 x
  · exact rowEval151 x
  · exact rowEval152 x
  · exact rowEval153 x
  · exact rowEval154 x
  · exact rowEval155 x
  · exact rowEval156 x
  · exact rowEval157 x
  · exact rowEval158 x
  · exact rowEval159 x
  · exact rowEval160 x
  · exact rowEval161 x
  · exact rowEval162 x
  · exact rowEval163 x
  · exact rowEval164 x
  · exact rowEval165 x
  · exact rowEval166 x
  · exact rowEval167 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block0.form2.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form2 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block0.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form2.terms k).tag (GramFunctions.Block0.form2.terms k).charge GramFunctions.Block0.form2) x := by
  fin_cases k
  · exact rowEval210 x
  · exact rowEval211 x
  · exact rowEval212 x
  · exact rowEval213 x
  · exact rowEval214 x
  · exact rowEval215 x
  · exact rowEval216 x
  · exact rowEval217 x
  · exact rowEval218 x
  · exact rowEval219 x
  · exact rowEval220 x
  · exact rowEval221 x
  · exact rowEval222 x
  · exact rowEval223 x
  · exact rowEval224 x
  · exact rowEval225 x
  · exact rowEval226 x
  · exact rowEval227 x
  · exact rowEval228 x
  · exact rowEval229 x
  · exact rowEval230 x
  · exact rowEval231 x
  · exact rowEval232 x
  · exact rowEval233 x
  · exact rowEval234 x
  · exact rowEval235 x
  · exact rowEval236 x
  · exact rowEval237 x
  · exact rowEval238 x
  · exact rowEval239 x
  · exact rowEval240 x
  · exact rowEval241 x
  · exact rowEval242 x
  · exact rowEval243 x
  · exact rowEval244 x
  · exact rowEval245 x
  · exact rowEval246 x
  · exact rowEval247 x
  · exact rowEval248 x
  · exact rowEval249 x
  · exact rowEval250 x
  · exact rowEval251 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block0.form2.mixedGram GramFunctions.Block0.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form2 GramFunctions.Block0.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck336 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form2 = rawRow336 := by decide +kernel

theorem rowCheck336 : row336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow336 := by decide +kernel

theorem rowEval336 (x : Key → ℝ) : Integer.Sparse.eval row336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck336, Integer.Sparse.eval_collectBalanced, rawRowCheck336]

theorem rawRowCheck337 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form2 = rawRow337 := by decide +kernel

theorem rowCheck337 : row337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow337 := by decide +kernel

theorem rowEval337 (x : Key → ℝ) : Integer.Sparse.eval row337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck337, Integer.Sparse.eval_collectBalanced, rawRowCheck337]

theorem rawRowCheck338 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form2 = rawRow338 := by decide +kernel

theorem rowCheck338 : row338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow338 := by decide +kernel

theorem rowEval338 (x : Key → ℝ) : Integer.Sparse.eval row338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck338, Integer.Sparse.eval_collectBalanced, rawRowCheck338]

theorem rawRowCheck339 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form2 = rawRow339 := by decide +kernel

theorem rowCheck339 : row339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow339 := by decide +kernel

theorem rowEval339 (x : Key → ℝ) : Integer.Sparse.eval row339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck339, Integer.Sparse.eval_collectBalanced, rawRowCheck339]

theorem rawRowCheck340 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form2 = rawRow340 := by decide +kernel

theorem rowCheck340 : row340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow340 := by decide +kernel

theorem rowEval340 (x : Key → ℝ) : Integer.Sparse.eval row340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck340, Integer.Sparse.eval_collectBalanced, rawRowCheck340]

theorem rawRowCheck341 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form2 = rawRow341 := by decide +kernel

theorem rowCheck341 : row341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow341 := by decide +kernel

theorem rowEval341 (x : Key → ℝ) : Integer.Sparse.eval row341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck341, Integer.Sparse.eval_collectBalanced, rawRowCheck341]

theorem rawRowCheck342 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form2 = rawRow342 := by decide +kernel

theorem rowCheck342 : row342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow342 := by decide +kernel

theorem rowEval342 (x : Key → ℝ) : Integer.Sparse.eval row342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck342, Integer.Sparse.eval_collectBalanced, rawRowCheck342]

theorem rawRowCheck343 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form2 = rawRow343 := by decide +kernel

theorem rowCheck343 : row343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow343 := by decide +kernel

theorem rowEval343 (x : Key → ℝ) : Integer.Sparse.eval row343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck343, Integer.Sparse.eval_collectBalanced, rawRowCheck343]

theorem rawRowCheck344 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form2 = rawRow344 := by decide +kernel

theorem rowCheck344 : row344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow344 := by decide +kernel

theorem rowEval344 (x : Key → ℝ) : Integer.Sparse.eval row344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck344, Integer.Sparse.eval_collectBalanced, rawRowCheck344]

theorem rawRowCheck345 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form2 = rawRow345 := by decide +kernel

theorem rowCheck345 : row345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow345 := by decide +kernel

theorem rowEval345 (x : Key → ℝ) : Integer.Sparse.eval row345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck345, Integer.Sparse.eval_collectBalanced, rawRowCheck345]

theorem rawRowCheck346 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form2 = rawRow346 := by decide +kernel

theorem rowCheck346 : row346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow346 := by decide +kernel

theorem rowEval346 (x : Key → ℝ) : Integer.Sparse.eval row346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck346, Integer.Sparse.eval_collectBalanced, rawRowCheck346]

theorem rawRowCheck347 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form2 = rawRow347 := by decide +kernel

theorem rowCheck347 : row347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow347 := by decide +kernel

theorem rowEval347 (x : Key → ℝ) : Integer.Sparse.eval row347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck347, Integer.Sparse.eval_collectBalanced, rawRowCheck347]

theorem rawRowCheck348 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form2 = rawRow348 := by decide +kernel

theorem rowCheck348 : row348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow348 := by decide +kernel

theorem rowEval348 (x : Key → ℝ) : Integer.Sparse.eval row348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck348, Integer.Sparse.eval_collectBalanced, rawRowCheck348]

theorem rawRowCheck349 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form2 = rawRow349 := by decide +kernel

theorem rowCheck349 : row349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow349 := by decide +kernel

theorem rowEval349 (x : Key → ℝ) : Integer.Sparse.eval row349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck349, Integer.Sparse.eval_collectBalanced, rawRowCheck349]

theorem rawRowCheck350 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form2 = rawRow350 := by decide +kernel

theorem rowCheck350 : row350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow350 := by decide +kernel

theorem rowEval350 (x : Key → ℝ) : Integer.Sparse.eval row350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck350, Integer.Sparse.eval_collectBalanced, rawRowCheck350]

theorem rawRowCheck351 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form2 = rawRow351 := by decide +kernel

theorem rowCheck351 : row351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow351 := by decide +kernel

theorem rowEval351 (x : Key → ℝ) : Integer.Sparse.eval row351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck351, Integer.Sparse.eval_collectBalanced, rawRowCheck351]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck352 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form2 = rawRow352 := by decide +kernel

theorem rowCheck352 : row352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow352 := by decide +kernel

theorem rowEval352 (x : Key → ℝ) : Integer.Sparse.eval row352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck352, Integer.Sparse.eval_collectBalanced, rawRowCheck352]

theorem rawRowCheck353 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form2 = rawRow353 := by decide +kernel

theorem rowCheck353 : row353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow353 := by decide +kernel

theorem rowEval353 (x : Key → ℝ) : Integer.Sparse.eval row353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck353, Integer.Sparse.eval_collectBalanced, rawRowCheck353]

theorem rawRowCheck354 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form2 = rawRow354 := by decide +kernel

theorem rowCheck354 : row354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow354 := by decide +kernel

theorem rowEval354 (x : Key → ℝ) : Integer.Sparse.eval row354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck354, Integer.Sparse.eval_collectBalanced, rawRowCheck354]

theorem rawRowCheck355 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form2 = rawRow355 := by decide +kernel

theorem rowCheck355 : row355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow355 := by decide +kernel

theorem rowEval355 (x : Key → ℝ) : Integer.Sparse.eval row355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck355, Integer.Sparse.eval_collectBalanced, rawRowCheck355]

theorem rawRowCheck356 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form2 = rawRow356 := by decide +kernel

theorem rowCheck356 : row356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow356 := by decide +kernel

theorem rowEval356 (x : Key → ℝ) : Integer.Sparse.eval row356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck356, Integer.Sparse.eval_collectBalanced, rawRowCheck356]

theorem rawRowCheck357 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form2 = rawRow357 := by decide +kernel

theorem rowCheck357 : row357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow357 := by decide +kernel

theorem rowEval357 (x : Key → ℝ) : Integer.Sparse.eval row357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck357, Integer.Sparse.eval_collectBalanced, rawRowCheck357]

theorem rawRowCheck358 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form2 = rawRow358 := by decide +kernel

theorem rowCheck358 : row358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow358 := by decide +kernel

theorem rowEval358 (x : Key → ℝ) : Integer.Sparse.eval row358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck358, Integer.Sparse.eval_collectBalanced, rawRowCheck358]

theorem rawRowCheck359 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form2 = rawRow359 := by decide +kernel

theorem rowCheck359 : row359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow359 := by decide +kernel

theorem rowEval359 (x : Key → ℝ) : Integer.Sparse.eval row359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck359, Integer.Sparse.eval_collectBalanced, rawRowCheck359]

theorem rawRowCheck360 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form2 = rawRow360 := by decide +kernel

theorem rowCheck360 : row360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow360 := by decide +kernel

theorem rowEval360 (x : Key → ℝ) : Integer.Sparse.eval row360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck360, Integer.Sparse.eval_collectBalanced, rawRowCheck360]

theorem rawRowCheck361 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form2 = rawRow361 := by decide +kernel

theorem rowCheck361 : row361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow361 := by decide +kernel

theorem rowEval361 (x : Key → ℝ) : Integer.Sparse.eval row361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck361, Integer.Sparse.eval_collectBalanced, rawRowCheck361]

theorem rawRowCheck362 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form2 = rawRow362 := by decide +kernel

theorem rowCheck362 : row362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow362 := by decide +kernel

theorem rowEval362 (x : Key → ℝ) : Integer.Sparse.eval row362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck362, Integer.Sparse.eval_collectBalanced, rawRowCheck362]

theorem rawRowCheck363 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form2 = rawRow363 := by decide +kernel

theorem rowCheck363 : row363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow363 := by decide +kernel

theorem rowEval363 (x : Key → ℝ) : Integer.Sparse.eval row363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck363, Integer.Sparse.eval_collectBalanced, rawRowCheck363]

theorem rawRowCheck364 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form2 = rawRow364 := by decide +kernel

theorem rowCheck364 : row364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow364 := by decide +kernel

theorem rowEval364 (x : Key → ℝ) : Integer.Sparse.eval row364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck364, Integer.Sparse.eval_collectBalanced, rawRowCheck364]

theorem rawRowCheck365 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form2 = rawRow365 := by decide +kernel

theorem rowCheck365 : row365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow365 := by decide +kernel

theorem rowEval365 (x : Key → ℝ) : Integer.Sparse.eval row365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck365, Integer.Sparse.eval_collectBalanced, rawRowCheck365]

theorem rawRowCheck366 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form2 = rawRow366 := by decide +kernel

theorem rowCheck366 : row366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow366 := by decide +kernel

theorem rowEval366 (x : Key → ℝ) : Integer.Sparse.eval row366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck366, Integer.Sparse.eval_collectBalanced, rawRowCheck366]

theorem rawRowCheck367 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form2 = rawRow367 := by decide +kernel

theorem rowCheck367 : row367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow367 := by decide +kernel

theorem rowEval367 (x : Key → ℝ) : Integer.Sparse.eval row367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck367, Integer.Sparse.eval_collectBalanced, rawRowCheck367]

theorem rawRowCheck368 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form2 = rawRow368 := by decide +kernel

theorem rowCheck368 : row368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow368 := by decide +kernel

theorem rowEval368 (x : Key → ℝ) : Integer.Sparse.eval row368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck368, Integer.Sparse.eval_collectBalanced, rawRowCheck368]

theorem rawRowCheck369 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form2 = rawRow369 := by decide +kernel

theorem rowCheck369 : row369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow369 := by decide +kernel

theorem rowEval369 (x : Key → ℝ) : Integer.Sparse.eval row369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck369, Integer.Sparse.eval_collectBalanced, rawRowCheck369]

theorem rawRowCheck370 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form2 = rawRow370 := by decide +kernel

theorem rowCheck370 : row370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow370 := by decide +kernel

theorem rowEval370 (x : Key → ℝ) : Integer.Sparse.eval row370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck370, Integer.Sparse.eval_collectBalanced, rawRowCheck370]

theorem rawRowCheck371 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form2 = rawRow371 := by decide +kernel

theorem rowCheck371 : row371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow371 := by decide +kernel

theorem rowEval371 (x : Key → ℝ) : Integer.Sparse.eval row371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck371, Integer.Sparse.eval_collectBalanced, rawRowCheck371]

theorem rawRowCheck372 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form2 = rawRow372 := by decide +kernel

theorem rowCheck372 : row372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow372 := by decide +kernel

theorem rowEval372 (x : Key → ℝ) : Integer.Sparse.eval row372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck372, Integer.Sparse.eval_collectBalanced, rawRowCheck372]

theorem rawRowCheck373 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form2 = rawRow373 := by decide +kernel

theorem rowCheck373 : row373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow373 := by decide +kernel

theorem rowEval373 (x : Key → ℝ) : Integer.Sparse.eval row373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck373, Integer.Sparse.eval_collectBalanced, rawRowCheck373]

theorem rawRowCheck374 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form2 = rawRow374 := by decide +kernel

theorem rowCheck374 : row374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow374 := by decide +kernel

theorem rowEval374 (x : Key → ℝ) : Integer.Sparse.eval row374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck374, Integer.Sparse.eval_collectBalanced, rawRowCheck374]

theorem rawRowCheck375 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form2 = rawRow375 := by decide +kernel

theorem rowCheck375 : row375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow375 := by decide +kernel

theorem rowEval375 (x : Key → ℝ) : Integer.Sparse.eval row375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck375, Integer.Sparse.eval_collectBalanced, rawRowCheck375]

theorem rawRowCheck376 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form2 = rawRow376 := by decide +kernel

theorem rowCheck376 : row376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow376 := by decide +kernel

theorem rowEval376 (x : Key → ℝ) : Integer.Sparse.eval row376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck376, Integer.Sparse.eval_collectBalanced, rawRowCheck376]

theorem rawRowCheck377 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form2 = rawRow377 := by decide +kernel

theorem rowCheck377 : row377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow377 := by decide +kernel

theorem rowEval377 (x : Key → ℝ) : Integer.Sparse.eval row377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck377, Integer.Sparse.eval_collectBalanced, rawRowCheck377]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form2) x := by
  fin_cases k
  · exact rowEval336 x
  · exact rowEval337 x
  · exact rowEval338 x
  · exact rowEval339 x
  · exact rowEval340 x
  · exact rowEval341 x
  · exact rowEval342 x
  · exact rowEval343 x
  · exact rowEval344 x
  · exact rowEval345 x
  · exact rowEval346 x
  · exact rowEval347 x
  · exact rowEval348 x
  · exact rowEval349 x
  · exact rowEval350 x
  · exact rowEval351 x
  · exact rowEval352 x
  · exact rowEval353 x
  · exact rowEval354 x
  · exact rowEval355 x
  · exact rowEval356 x
  · exact rowEval357 x
  · exact rowEval358 x
  · exact rowEval359 x
  · exact rowEval360 x
  · exact rowEval361 x
  · exact rowEval362 x
  · exact rowEval363 x
  · exact rowEval364 x
  · exact rowEval365 x
  · exact rowEval366 x
  · exact rowEval367 x
  · exact rowEval368 x
  · exact rowEval369 x
  · exact rowEval370 x
  · exact rowEval371 x
  · exact rowEval372 x
  · exact rowEval373 x
  · exact rowEval374 x
  · exact rowEval375 x
  · exact rowEval376 x
  · exact rowEval377 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

theorem entryEvalRow2_e_oai (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 2 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 2).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval2_0 B hB
  · exact entryEval2_1_e B hB
  · exact entryEval2_2 B hB
  · exact (entryEval3_2 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_2_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e_oai
