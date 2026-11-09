-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:03:23.492738+00:00
-- url     : https://prove2.me/submissions/84437b99-65e7-4798-8ac4-ce993821860c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E054
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval1_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_0_e

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

theorem rawRowCheck0 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0 = rawRow0 := by decide +kernel

theorem rowCheck0 : row0 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow0 := by decide +kernel

theorem rowEval0 (x : Key → ℝ) : Integer.Sparse.eval row0 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck0, Integer.Sparse.eval_collectBalanced, rawRowCheck0]

theorem rawRowCheck1 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0 = rawRow1 := by decide +kernel

theorem rowCheck1 : row1 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1 := by decide +kernel

theorem rowEval1 (x : Key → ℝ) : Integer.Sparse.eval row1 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck1, Integer.Sparse.eval_collectBalanced, rawRowCheck1]

theorem rawRowCheck2 : GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0 = rawRow2 := by decide +kernel

theorem rowCheck2 : row2 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2 := by decide +kernel

theorem rowEval2 (x : Key → ℝ) : Integer.Sparse.eval row2 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck2, Integer.Sparse.eval_collectBalanced, rawRowCheck2]

theorem rawRowCheck3 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0 = rawRow3 := by decide +kernel

theorem rowCheck3 : row3 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3 := by decide +kernel

theorem rowEval3 (x : Key → ℝ) : Integer.Sparse.eval row3 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck3, Integer.Sparse.eval_collectBalanced, rawRowCheck3]

theorem rawRowCheck4 : GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0 = rawRow4 := by decide +kernel

theorem rowCheck4 : row4 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4 := by decide +kernel

theorem rowEval4 (x : Key → ℝ) : Integer.Sparse.eval row4 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck4, Integer.Sparse.eval_collectBalanced, rawRowCheck4]

theorem rawRowCheck5 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0 = rawRow5 := by decide +kernel

theorem rowCheck5 : row5 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5 := by decide +kernel

theorem rowEval5 (x : Key → ℝ) : Integer.Sparse.eval row5 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck5, Integer.Sparse.eval_collectBalanced, rawRowCheck5]

theorem rawRowCheck6 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0 = rawRow6 := by decide +kernel

theorem rowCheck6 : row6 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6 := by decide +kernel

theorem rowEval6 (x : Key → ℝ) : Integer.Sparse.eval row6 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck6, Integer.Sparse.eval_collectBalanced, rawRowCheck6]

theorem rawRowCheck7 : GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0 = rawRow7 := by decide +kernel

theorem rowCheck7 : row7 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7 := by decide +kernel

theorem rowEval7 (x : Key → ℝ) : Integer.Sparse.eval row7 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck7, Integer.Sparse.eval_collectBalanced, rawRowCheck7]

theorem rawRowCheck8 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0 = rawRow8 := by decide +kernel

theorem rowCheck8 : row8 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8 := by decide +kernel

theorem rowEval8 (x : Key → ℝ) : Integer.Sparse.eval row8 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck8, Integer.Sparse.eval_collectBalanced, rawRowCheck8]

theorem rawRowCheck9 : GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0 = rawRow9 := by decide +kernel

theorem rowCheck9 : row9 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9 := by decide +kernel

theorem rowEval9 (x : Key → ℝ) : Integer.Sparse.eval row9 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck9, Integer.Sparse.eval_collectBalanced, rawRowCheck9]

theorem rawRowCheck10 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0 = rawRow10 := by decide +kernel

theorem rowCheck10 : row10 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10 := by decide +kernel

theorem rowEval10 (x : Key → ℝ) : Integer.Sparse.eval row10 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck10, Integer.Sparse.eval_collectBalanced, rawRowCheck10]

theorem rawRowCheck11 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0 = rawRow11 := by decide +kernel

theorem rowCheck11 : row11 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11 := by decide +kernel

theorem rowEval11 (x : Key → ℝ) : Integer.Sparse.eval row11 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck11, Integer.Sparse.eval_collectBalanced, rawRowCheck11]

theorem rawRowCheck12 : GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0 = rawRow12 := by decide +kernel

theorem rowCheck12 : row12 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12 := by decide +kernel

theorem rowEval12 (x : Key → ℝ) : Integer.Sparse.eval row12 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck12, Integer.Sparse.eval_collectBalanced, rawRowCheck12]

theorem rawRowCheck13 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0 = rawRow13 := by decide +kernel

theorem rowCheck13 : row13 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13 := by decide +kernel

theorem rowEval13 (x : Key → ℝ) : Integer.Sparse.eval row13 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck13, Integer.Sparse.eval_collectBalanced, rawRowCheck13]

theorem rawRowCheck14 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0 = rawRow14 := by decide +kernel

theorem rowCheck14 : row14 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14 := by decide +kernel

theorem rowEval14 (x : Key → ℝ) : Integer.Sparse.eval row14 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck14, Integer.Sparse.eval_collectBalanced, rawRowCheck14]

theorem rawRowCheck15 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0 = rawRow15 := by decide +kernel

theorem rowCheck15 : row15 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15 := by decide +kernel

theorem rowEval15 (x : Key → ℝ) : Integer.Sparse.eval row15 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck15, Integer.Sparse.eval_collectBalanced, rawRowCheck15]

theorem rawRowCheck16 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0 = rawRow16 := by decide +kernel

theorem rowCheck16 : row16 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16 := by decide +kernel

theorem rowEval16 (x : Key → ℝ) : Integer.Sparse.eval row16 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck16, Integer.Sparse.eval_collectBalanced, rawRowCheck16]

theorem rawRowCheck17 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow17 := by decide +kernel

theorem rowCheck17 : row17 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17 := by decide +kernel

theorem rowEval17 (x : Key → ℝ) : Integer.Sparse.eval row17 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck17, Integer.Sparse.eval_collectBalanced, rawRowCheck17]

theorem rawRowCheck18 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow18 := by decide +kernel

theorem rowCheck18 : row18 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18 := by decide +kernel

theorem rowEval18 (x : Key → ℝ) : Integer.Sparse.eval row18 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck18, Integer.Sparse.eval_collectBalanced, rawRowCheck18]

theorem rawRowCheck19 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow19 := by decide +kernel

theorem rowCheck19 : row19 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19 := by decide +kernel

theorem rowEval19 (x : Key → ℝ) : Integer.Sparse.eval row19 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck19, Integer.Sparse.eval_collectBalanced, rawRowCheck19]

theorem rawRowCheck20 : GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow20 := by decide +kernel

theorem rowCheck20 : row20 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20 := by decide +kernel

theorem rowEval20 (x : Key → ℝ) : Integer.Sparse.eval row20 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck20, Integer.Sparse.eval_collectBalanced, rawRowCheck20]

theorem rawRowCheck21 : GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow21 := by decide +kernel

theorem rowCheck21 : row21 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow21 := by decide +kernel

theorem rowEval21 (x : Key → ℝ) : Integer.Sparse.eval row21 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck21, Integer.Sparse.eval_collectBalanced, rawRowCheck21]

theorem rawRowCheck22 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0 = rawRow22 := by decide +kernel

theorem rowCheck22 : row22 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow22 := by decide +kernel

theorem rowEval22 (x : Key → ℝ) : Integer.Sparse.eval row22 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck22, Integer.Sparse.eval_collectBalanced, rawRowCheck22]

theorem rawRowCheck23 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0 = rawRow23 := by decide +kernel

theorem rowCheck23 : row23 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow23 := by decide +kernel

theorem rowEval23 (x : Key → ℝ) : Integer.Sparse.eval row23 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck23, Integer.Sparse.eval_collectBalanced, rawRowCheck23]

theorem rawRowCheck24 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow24 := by decide +kernel

theorem rowCheck24 : row24 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow24 := by decide +kernel

theorem rowEval24 (x : Key → ℝ) : Integer.Sparse.eval row24 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck24, Integer.Sparse.eval_collectBalanced, rawRowCheck24]

theorem rawRowCheck25 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow25 := by decide +kernel

theorem rowCheck25 : row25 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow25 := by decide +kernel

theorem rowEval25 (x : Key → ℝ) : Integer.Sparse.eval row25 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck25, Integer.Sparse.eval_collectBalanced, rawRowCheck25]

theorem rawRowCheck26 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0 = rawRow26 := by decide +kernel

theorem rowCheck26 : row26 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow26 := by decide +kernel

theorem rowEval26 (x : Key → ℝ) : Integer.Sparse.eval row26 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck26, Integer.Sparse.eval_collectBalanced, rawRowCheck26]

theorem rawRowCheck27 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0 = rawRow27 := by decide +kernel

theorem rowCheck27 : row27 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow27 := by decide +kernel

theorem rowEval27 (x : Key → ℝ) : Integer.Sparse.eval row27 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck27, Integer.Sparse.eval_collectBalanced, rawRowCheck27]

theorem rawRowCheck28 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0 = rawRow28 := by decide +kernel

theorem rowCheck28 : row28 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow28 := by decide +kernel

theorem rowEval28 (x : Key → ℝ) : Integer.Sparse.eval row28 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck28, Integer.Sparse.eval_collectBalanced, rawRowCheck28]

theorem rawRowCheck29 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0 = rawRow29 := by decide +kernel

theorem rowCheck29 : row29 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow29 := by decide +kernel

theorem rowEval29 (x : Key → ℝ) : Integer.Sparse.eval row29 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck29, Integer.Sparse.eval_collectBalanced, rawRowCheck29]

theorem rawRowCheck30 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0 = rawRow30 := by decide +kernel

theorem rowCheck30 : row30 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow30 := by decide +kernel

theorem rowEval30 (x : Key → ℝ) : Integer.Sparse.eval row30 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck30, Integer.Sparse.eval_collectBalanced, rawRowCheck30]

theorem rawRowCheck31 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0 = rawRow31 := by decide +kernel

theorem rowCheck31 : row31 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow31 := by decide +kernel

theorem rowEval31 (x : Key → ℝ) : Integer.Sparse.eval row31 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck31, Integer.Sparse.eval_collectBalanced, rawRowCheck31]

theorem rawRowCheck32 : GramPolynomial.normalizedRow 0 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow32 := by decide +kernel

theorem rowCheck32 : row32 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow32 := by decide +kernel

theorem rowEval32 (x : Key → ℝ) : Integer.Sparse.eval row32 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck32, Integer.Sparse.eval_collectBalanced, rawRowCheck32]

theorem rawRowCheck33 : GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow33 := by decide +kernel

theorem rowCheck33 : row33 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow33 := by decide +kernel

theorem rowEval33 (x : Key → ℝ) : Integer.Sparse.eval row33 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck33, Integer.Sparse.eval_collectBalanced, rawRowCheck33]

theorem rawRowCheck34 : GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow34 := by decide +kernel

theorem rowCheck34 : row34 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow34 := by decide +kernel

theorem rowEval34 (x : Key → ℝ) : Integer.Sparse.eval row34 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck34, Integer.Sparse.eval_collectBalanced, rawRowCheck34]

theorem rawRowCheck35 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow35 := by decide +kernel

theorem rowCheck35 : row35 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow35 := by decide +kernel

theorem rowEval35 (x : Key → ℝ) : Integer.Sparse.eval row35 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck35, Integer.Sparse.eval_collectBalanced, rawRowCheck35]

theorem rawRowCheck36 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow36 := by decide +kernel

theorem rowCheck36 : row36 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow36 := by decide +kernel

theorem rowEval36 (x : Key → ℝ) : Integer.Sparse.eval row36 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck36, Integer.Sparse.eval_collectBalanced, rawRowCheck36]

theorem rawRowCheck37 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow37 := by decide +kernel

theorem rowCheck37 : row37 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow37 := by decide +kernel

theorem rowEval37 (x : Key → ℝ) : Integer.Sparse.eval row37 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck37, Integer.Sparse.eval_collectBalanced, rawRowCheck37]

theorem rawRowCheck38 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0 = rawRow38 := by decide +kernel

theorem rowCheck38 : row38 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow38 := by decide +kernel

theorem rowEval38 (x : Key → ℝ) : Integer.Sparse.eval row38 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck38, Integer.Sparse.eval_collectBalanced, rawRowCheck38]

theorem rawRowCheck39 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0 = rawRow39 := by decide +kernel

theorem rowCheck39 : row39 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow39 := by decide +kernel

theorem rowEval39 (x : Key → ℝ) : Integer.Sparse.eval row39 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck39, Integer.Sparse.eval_collectBalanced, rawRowCheck39]

theorem rawRowCheck40 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0 = rawRow40 := by decide +kernel

theorem rowCheck40 : row40 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow40 := by decide +kernel

theorem rowEval40 (x : Key → ℝ) : Integer.Sparse.eval row40 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck40, Integer.Sparse.eval_collectBalanced, rawRowCheck40]

theorem rawRowCheck41 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0 = rawRow41 := by decide +kernel

theorem rowCheck41 : row41 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow41 := by decide +kernel

theorem rowEval41 (x : Key → ℝ) : Integer.Sparse.eval row41 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck41, Integer.Sparse.eval_collectBalanced, rawRowCheck41]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block0.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form0.terms k).tag (GramFunctions.Block0.form0.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval0 x
  · exact rowEval1 x
  · exact rowEval2 x
  · exact rowEval3 x
  · exact rowEval4 x
  · exact rowEval5 x
  · exact rowEval6 x
  · exact rowEval7 x
  · exact rowEval8 x
  · exact rowEval9 x
  · exact rowEval10 x
  · exact rowEval11 x
  · exact rowEval12 x
  · exact rowEval13 x
  · exact rowEval14 x
  · exact rowEval15 x
  · exact rowEval16 x
  · exact rowEval17 x
  · exact rowEval18 x
  · exact rowEval19 x
  · exact rowEval20 x
  · exact rowEval21 x
  · exact rowEval22 x
  · exact rowEval23 x
  · exact rowEval24 x
  · exact rowEval25 x
  · exact rowEval26 x
  · exact rowEval27 x
  · exact rowEval28 x
  · exact rowEval29 x
  · exact rowEval30 x
  · exact rowEval31 x
  · exact rowEval32 x
  · exact rowEval33 x
  · exact rowEval34 x
  · exact rowEval35 x
  · exact rowEval36 x
  · exact rowEval37 x
  · exact rowEval38 x
  · exact rowEval39 x
  · exact rowEval40 x
  · exact rowEval41 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block0.form0.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form0 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block0

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck252 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0 = rawRow252 := by decide +kernel

theorem rowCheck252 : row252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow252 := by decide +kernel

theorem rowEval252 (x : Key → ℝ) : Integer.Sparse.eval row252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck252, Integer.Sparse.eval_collectBalanced, rawRowCheck252]

theorem rawRowCheck253 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0 = rawRow253 := by decide +kernel

theorem rowCheck253 : row253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow253 := by decide +kernel

theorem rowEval253 (x : Key → ℝ) : Integer.Sparse.eval row253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck253, Integer.Sparse.eval_collectBalanced, rawRowCheck253]

theorem rawRowCheck254 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0 = rawRow254 := by decide +kernel

theorem rowCheck254 : row254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow254 := by decide +kernel

theorem rowEval254 (x : Key → ℝ) : Integer.Sparse.eval row254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck254, Integer.Sparse.eval_collectBalanced, rawRowCheck254]

theorem rawRowCheck255 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0 = rawRow255 := by decide +kernel

theorem rowCheck255 : row255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow255 := by decide +kernel

theorem rowEval255 (x : Key → ℝ) : Integer.Sparse.eval row255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck255, Integer.Sparse.eval_collectBalanced, rawRowCheck255]

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

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck256 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0 = rawRow256 := by decide +kernel

theorem rowCheck256 : row256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow256 := by decide +kernel

theorem rowEval256 (x : Key → ℝ) : Integer.Sparse.eval row256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck256, Integer.Sparse.eval_collectBalanced, rawRowCheck256]

theorem rawRowCheck257 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0 = rawRow257 := by decide +kernel

theorem rowCheck257 : row257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow257 := by decide +kernel

theorem rowEval257 (x : Key → ℝ) : Integer.Sparse.eval row257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck257, Integer.Sparse.eval_collectBalanced, rawRowCheck257]

theorem rawRowCheck258 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0 = rawRow258 := by decide +kernel

theorem rowCheck258 : row258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow258 := by decide +kernel

theorem rowEval258 (x : Key → ℝ) : Integer.Sparse.eval row258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck258, Integer.Sparse.eval_collectBalanced, rawRowCheck258]

theorem rawRowCheck259 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0 = rawRow259 := by decide +kernel

theorem rowCheck259 : row259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow259 := by decide +kernel

theorem rowEval259 (x : Key → ℝ) : Integer.Sparse.eval row259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck259, Integer.Sparse.eval_collectBalanced, rawRowCheck259]

theorem rawRowCheck260 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0 = rawRow260 := by decide +kernel

theorem rowCheck260 : row260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow260 := by decide +kernel

theorem rowEval260 (x : Key → ℝ) : Integer.Sparse.eval row260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck260, Integer.Sparse.eval_collectBalanced, rawRowCheck260]

theorem rawRowCheck261 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0 = rawRow261 := by decide +kernel

theorem rowCheck261 : row261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow261 := by decide +kernel

theorem rowEval261 (x : Key → ℝ) : Integer.Sparse.eval row261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck261, Integer.Sparse.eval_collectBalanced, rawRowCheck261]

theorem rawRowCheck262 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0 = rawRow262 := by decide +kernel

theorem rowCheck262 : row262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow262 := by decide +kernel

theorem rowEval262 (x : Key → ℝ) : Integer.Sparse.eval row262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck262, Integer.Sparse.eval_collectBalanced, rawRowCheck262]

theorem rawRowCheck263 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0 = rawRow263 := by decide +kernel

theorem rowCheck263 : row263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow263 := by decide +kernel

theorem rowEval263 (x : Key → ℝ) : Integer.Sparse.eval row263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck263, Integer.Sparse.eval_collectBalanced, rawRowCheck263]

theorem rawRowCheck264 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0 = rawRow264 := by decide +kernel

theorem rowCheck264 : row264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow264 := by decide +kernel

theorem rowEval264 (x : Key → ℝ) : Integer.Sparse.eval row264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck264, Integer.Sparse.eval_collectBalanced, rawRowCheck264]

theorem rawRowCheck265 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0 = rawRow265 := by decide +kernel

theorem rowCheck265 : row265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow265 := by decide +kernel

theorem rowEval265 (x : Key → ℝ) : Integer.Sparse.eval row265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck265, Integer.Sparse.eval_collectBalanced, rawRowCheck265]

theorem rawRowCheck266 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0 = rawRow266 := by decide +kernel

theorem rowCheck266 : row266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow266 := by decide +kernel

theorem rowEval266 (x : Key → ℝ) : Integer.Sparse.eval row266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck266, Integer.Sparse.eval_collectBalanced, rawRowCheck266]

theorem rawRowCheck267 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0 = rawRow267 := by decide +kernel

theorem rowCheck267 : row267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow267 := by decide +kernel

theorem rowEval267 (x : Key → ℝ) : Integer.Sparse.eval row267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck267, Integer.Sparse.eval_collectBalanced, rawRowCheck267]

theorem rawRowCheck268 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow268 := by decide +kernel

theorem rowCheck268 : row268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow268 := by decide +kernel

theorem rowEval268 (x : Key → ℝ) : Integer.Sparse.eval row268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck268, Integer.Sparse.eval_collectBalanced, rawRowCheck268]

theorem rawRowCheck269 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow269 := by decide +kernel

theorem rowCheck269 : row269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow269 := by decide +kernel

theorem rowEval269 (x : Key → ℝ) : Integer.Sparse.eval row269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck269, Integer.Sparse.eval_collectBalanced, rawRowCheck269]

theorem rawRowCheck270 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow270 := by decide +kernel

theorem rowCheck270 : row270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow270 := by decide +kernel

theorem rowEval270 (x : Key → ℝ) : Integer.Sparse.eval row270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck270, Integer.Sparse.eval_collectBalanced, rawRowCheck270]

theorem rawRowCheck271 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow271 := by decide +kernel

theorem rowCheck271 : row271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow271 := by decide +kernel

theorem rowEval271 (x : Key → ℝ) : Integer.Sparse.eval row271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck271, Integer.Sparse.eval_collectBalanced, rawRowCheck271]

theorem rawRowCheck272 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0 = rawRow272 := by decide +kernel

theorem rowCheck272 : row272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow272 := by decide +kernel

theorem rowEval272 (x : Key → ℝ) : Integer.Sparse.eval row272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck272, Integer.Sparse.eval_collectBalanced, rawRowCheck272]

theorem rawRowCheck273 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0 = rawRow273 := by decide +kernel

theorem rowCheck273 : row273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow273 := by decide +kernel

theorem rowEval273 (x : Key → ℝ) : Integer.Sparse.eval row273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck273, Integer.Sparse.eval_collectBalanced, rawRowCheck273]

theorem rawRowCheck274 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0 = rawRow274 := by decide +kernel

theorem rowCheck274 : row274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow274 := by decide +kernel

theorem rowEval274 (x : Key → ℝ) : Integer.Sparse.eval row274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck274, Integer.Sparse.eval_collectBalanced, rawRowCheck274]

theorem rawRowCheck275 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0 = rawRow275 := by decide +kernel

theorem rowCheck275 : row275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow275 := by decide +kernel

theorem rowEval275 (x : Key → ℝ) : Integer.Sparse.eval row275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck275, Integer.Sparse.eval_collectBalanced, rawRowCheck275]

theorem rawRowCheck276 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0 = rawRow276 := by decide +kernel

theorem rowCheck276 : row276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow276 := by decide +kernel

theorem rowEval276 (x : Key → ℝ) : Integer.Sparse.eval row276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck276, Integer.Sparse.eval_collectBalanced, rawRowCheck276]

theorem rawRowCheck277 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0 = rawRow277 := by decide +kernel

theorem rowCheck277 : row277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow277 := by decide +kernel

theorem rowEval277 (x : Key → ℝ) : Integer.Sparse.eval row277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck277, Integer.Sparse.eval_collectBalanced, rawRowCheck277]

theorem rawRowCheck278 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0 = rawRow278 := by decide +kernel

theorem rowCheck278 : row278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow278 := by decide +kernel

theorem rowEval278 (x : Key → ℝ) : Integer.Sparse.eval row278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck278, Integer.Sparse.eval_collectBalanced, rawRowCheck278]

theorem rawRowCheck279 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0 = rawRow279 := by decide +kernel

theorem rowCheck279 : row279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow279 := by decide +kernel

theorem rowEval279 (x : Key → ℝ) : Integer.Sparse.eval row279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck279, Integer.Sparse.eval_collectBalanced, rawRowCheck279]

theorem rawRowCheck280 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0 = rawRow280 := by decide +kernel

theorem rowCheck280 : row280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow280 := by decide +kernel

theorem rowEval280 (x : Key → ℝ) : Integer.Sparse.eval row280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck280, Integer.Sparse.eval_collectBalanced, rawRowCheck280]

theorem rawRowCheck281 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0 = rawRow281 := by decide +kernel

theorem rowCheck281 : row281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow281 := by decide +kernel

theorem rowEval281 (x : Key → ℝ) : Integer.Sparse.eval row281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck281, Integer.Sparse.eval_collectBalanced, rawRowCheck281]

theorem rawRowCheck282 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow282 := by decide +kernel

theorem rowCheck282 : row282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow282 := by decide +kernel

theorem rowEval282 (x : Key → ℝ) : Integer.Sparse.eval row282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck282, Integer.Sparse.eval_collectBalanced, rawRowCheck282]

theorem rawRowCheck283 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow283 := by decide +kernel

theorem rowCheck283 : row283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow283 := by decide +kernel

theorem rowEval283 (x : Key → ℝ) : Integer.Sparse.eval row283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck283, Integer.Sparse.eval_collectBalanced, rawRowCheck283]

theorem rawRowCheck284 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0 = rawRow284 := by decide +kernel

theorem rowCheck284 : row284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow284 := by decide +kernel

theorem rowEval284 (x : Key → ℝ) : Integer.Sparse.eval row284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck284, Integer.Sparse.eval_collectBalanced, rawRowCheck284]

theorem rawRowCheck285 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0 = rawRow285 := by decide +kernel

theorem rowCheck285 : row285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow285 := by decide +kernel

theorem rowEval285 (x : Key → ℝ) : Integer.Sparse.eval row285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck285, Integer.Sparse.eval_collectBalanced, rawRowCheck285]

theorem rawRowCheck286 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow286 := by decide +kernel

theorem rowCheck286 : row286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow286 := by decide +kernel

theorem rowEval286 (x : Key → ℝ) : Integer.Sparse.eval row286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck286, Integer.Sparse.eval_collectBalanced, rawRowCheck286]

theorem rawRowCheck287 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow287 := by decide +kernel

theorem rowCheck287 : row287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow287 := by decide +kernel

theorem rowEval287 (x : Key → ℝ) : Integer.Sparse.eval row287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck287, Integer.Sparse.eval_collectBalanced, rawRowCheck287]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck288 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow288 := by decide +kernel

theorem rowCheck288 : row288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow288 := by decide +kernel

theorem rowEval288 (x : Key → ℝ) : Integer.Sparse.eval row288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck288, Integer.Sparse.eval_collectBalanced, rawRowCheck288]

theorem rawRowCheck289 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow289 := by decide +kernel

theorem rowCheck289 : row289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow289 := by decide +kernel

theorem rowEval289 (x : Key → ℝ) : Integer.Sparse.eval row289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck289, Integer.Sparse.eval_collectBalanced, rawRowCheck289]

theorem rawRowCheck290 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0 = rawRow290 := by decide +kernel

theorem rowCheck290 : row290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow290 := by decide +kernel

theorem rowEval290 (x : Key → ℝ) : Integer.Sparse.eval row290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck290, Integer.Sparse.eval_collectBalanced, rawRowCheck290]

theorem rawRowCheck291 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0 = rawRow291 := by decide +kernel

theorem rowCheck291 : row291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow291 := by decide +kernel

theorem rowEval291 (x : Key → ℝ) : Integer.Sparse.eval row291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck291, Integer.Sparse.eval_collectBalanced, rawRowCheck291]

theorem rawRowCheck292 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0 = rawRow292 := by decide +kernel

theorem rowCheck292 : row292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow292 := by decide +kernel

theorem rowEval292 (x : Key → ℝ) : Integer.Sparse.eval row292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck292, Integer.Sparse.eval_collectBalanced, rawRowCheck292]

theorem rawRowCheck293 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0 = rawRow293 := by decide +kernel

theorem rowCheck293 : row293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow293 := by decide +kernel

theorem rowEval293 (x : Key → ℝ) : Integer.Sparse.eval row293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck293, Integer.Sparse.eval_collectBalanced, rawRowCheck293]

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

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval252 x
  · exact rowEval253 x
  · exact rowEval254 x
  · exact rowEval255 x
  · exact rowEval256 x
  · exact rowEval257 x
  · exact rowEval258 x
  · exact rowEval259 x
  · exact rowEval260 x
  · exact rowEval261 x
  · exact rowEval262 x
  · exact rowEval263 x
  · exact rowEval264 x
  · exact rowEval265 x
  · exact rowEval266 x
  · exact rowEval267 x
  · exact rowEval268 x
  · exact rowEval269 x
  · exact rowEval270 x
  · exact rowEval271 x
  · exact rowEval272 x
  · exact rowEval273 x
  · exact rowEval274 x
  · exact rowEval275 x
  · exact rowEval276 x
  · exact rowEval277 x
  · exact rowEval278 x
  · exact rowEval279 x
  · exact rowEval280 x
  · exact rowEval281 x
  · exact rowEval282 x
  · exact rowEval283 x
  · exact rowEval284 x
  · exact rowEval285 x
  · exact rowEval286 x
  · exact rowEval287 x
  · exact rowEval288 x
  · exact rowEval289 x
  · exact rowEval290 x
  · exact rowEval291 x
  · exact rowEval292 x
  · exact rowEval293 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

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

theorem entryEvalRow0_e_oai (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 0).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval0_0 B hB
  · exact (entryEval1_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval2_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e_oai
