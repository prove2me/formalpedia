-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:45:27.271198+00:00
-- url     : https://prove2.me/submissions/27ddc034-6d2e-4fab-988b-096b6b90aac9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval3_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block0_entryEval4_3_e

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

theorem rawRowCheck294 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1 = rawRow294 := by decide +kernel

theorem rowCheck294 : row294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow294 := by decide +kernel

theorem rowEval294 (x : Key → ℝ) : Integer.Sparse.eval row294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck294, Integer.Sparse.eval_collectBalanced, rawRowCheck294]

theorem rawRowCheck295 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1 = rawRow295 := by decide +kernel

theorem rowCheck295 : row295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow295 := by decide +kernel

theorem rowEval295 (x : Key → ℝ) : Integer.Sparse.eval row295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck295, Integer.Sparse.eval_collectBalanced, rawRowCheck295]

theorem rawRowCheck296 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1 = rawRow296 := by decide +kernel

theorem rowCheck296 : row296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow296 := by decide +kernel

theorem rowEval296 (x : Key → ℝ) : Integer.Sparse.eval row296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck296, Integer.Sparse.eval_collectBalanced, rawRowCheck296]

theorem rawRowCheck297 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1 = rawRow297 := by decide +kernel

theorem rowCheck297 : row297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow297 := by decide +kernel

theorem rowEval297 (x : Key → ℝ) : Integer.Sparse.eval row297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck297, Integer.Sparse.eval_collectBalanced, rawRowCheck297]

theorem rawRowCheck298 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1 = rawRow298 := by decide +kernel

theorem rowCheck298 : row298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow298 := by decide +kernel

theorem rowEval298 (x : Key → ℝ) : Integer.Sparse.eval row298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck298, Integer.Sparse.eval_collectBalanced, rawRowCheck298]

theorem rawRowCheck299 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1 = rawRow299 := by decide +kernel

theorem rowCheck299 : row299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow299 := by decide +kernel

theorem rowEval299 (x : Key → ℝ) : Integer.Sparse.eval row299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck299, Integer.Sparse.eval_collectBalanced, rawRowCheck299]

theorem rawRowCheck300 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1 = rawRow300 := by decide +kernel

theorem rowCheck300 : row300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow300 := by decide +kernel

theorem rowEval300 (x : Key → ℝ) : Integer.Sparse.eval row300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck300, Integer.Sparse.eval_collectBalanced, rawRowCheck300]

theorem rawRowCheck301 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1 = rawRow301 := by decide +kernel

theorem rowCheck301 : row301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow301 := by decide +kernel

theorem rowEval301 (x : Key → ℝ) : Integer.Sparse.eval row301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck301, Integer.Sparse.eval_collectBalanced, rawRowCheck301]

theorem rawRowCheck302 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1 = rawRow302 := by decide +kernel

theorem rowCheck302 : row302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow302 := by decide +kernel

theorem rowEval302 (x : Key → ℝ) : Integer.Sparse.eval row302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck302, Integer.Sparse.eval_collectBalanced, rawRowCheck302]

theorem rawRowCheck303 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1 = rawRow303 := by decide +kernel

theorem rowCheck303 : row303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow303 := by decide +kernel

theorem rowEval303 (x : Key → ℝ) : Integer.Sparse.eval row303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck303, Integer.Sparse.eval_collectBalanced, rawRowCheck303]

theorem rawRowCheck304 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1 = rawRow304 := by decide +kernel

theorem rowCheck304 : row304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow304 := by decide +kernel

theorem rowEval304 (x : Key → ℝ) : Integer.Sparse.eval row304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck304, Integer.Sparse.eval_collectBalanced, rawRowCheck304]

theorem rawRowCheck305 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1 = rawRow305 := by decide +kernel

theorem rowCheck305 : row305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow305 := by decide +kernel

theorem rowEval305 (x : Key → ℝ) : Integer.Sparse.eval row305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck305, Integer.Sparse.eval_collectBalanced, rawRowCheck305]

theorem rawRowCheck306 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1 = rawRow306 := by decide +kernel

theorem rowCheck306 : row306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow306 := by decide +kernel

theorem rowEval306 (x : Key → ℝ) : Integer.Sparse.eval row306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck306, Integer.Sparse.eval_collectBalanced, rawRowCheck306]

theorem rawRowCheck307 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1 = rawRow307 := by decide +kernel

theorem rowCheck307 : row307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow307 := by decide +kernel

theorem rowEval307 (x : Key → ℝ) : Integer.Sparse.eval row307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck307, Integer.Sparse.eval_collectBalanced, rawRowCheck307]

theorem rawRowCheck308 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1 = rawRow308 := by decide +kernel

theorem rowCheck308 : row308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow308 := by decide +kernel

theorem rowEval308 (x : Key → ℝ) : Integer.Sparse.eval row308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck308, Integer.Sparse.eval_collectBalanced, rawRowCheck308]

theorem rawRowCheck309 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1 = rawRow309 := by decide +kernel

theorem rowCheck309 : row309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow309 := by decide +kernel

theorem rowEval309 (x : Key → ℝ) : Integer.Sparse.eval row309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck309, Integer.Sparse.eval_collectBalanced, rawRowCheck309]

theorem rawRowCheck310 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow310 := by decide +kernel

theorem rowCheck310 : row310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow310 := by decide +kernel

theorem rowEval310 (x : Key → ℝ) : Integer.Sparse.eval row310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck310, Integer.Sparse.eval_collectBalanced, rawRowCheck310]

theorem rawRowCheck311 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow311 := by decide +kernel

theorem rowCheck311 : row311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow311 := by decide +kernel

theorem rowEval311 (x : Key → ℝ) : Integer.Sparse.eval row311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck311, Integer.Sparse.eval_collectBalanced, rawRowCheck311]

theorem rawRowCheck312 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow312 := by decide +kernel

theorem rowCheck312 : row312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow312 := by decide +kernel

theorem rowEval312 (x : Key → ℝ) : Integer.Sparse.eval row312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck312, Integer.Sparse.eval_collectBalanced, rawRowCheck312]

theorem rawRowCheck313 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow313 := by decide +kernel

theorem rowCheck313 : row313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow313 := by decide +kernel

theorem rowEval313 (x : Key → ℝ) : Integer.Sparse.eval row313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck313, Integer.Sparse.eval_collectBalanced, rawRowCheck313]

theorem rawRowCheck314 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1 = rawRow314 := by decide +kernel

theorem rowCheck314 : row314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow314 := by decide +kernel

theorem rowEval314 (x : Key → ℝ) : Integer.Sparse.eval row314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck314, Integer.Sparse.eval_collectBalanced, rawRowCheck314]

theorem rawRowCheck315 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1 = rawRow315 := by decide +kernel

theorem rowCheck315 : row315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow315 := by decide +kernel

theorem rowEval315 (x : Key → ℝ) : Integer.Sparse.eval row315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck315, Integer.Sparse.eval_collectBalanced, rawRowCheck315]

theorem rawRowCheck316 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1 = rawRow316 := by decide +kernel

theorem rowCheck316 : row316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow316 := by decide +kernel

theorem rowEval316 (x : Key → ℝ) : Integer.Sparse.eval row316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck316, Integer.Sparse.eval_collectBalanced, rawRowCheck316]

theorem rawRowCheck317 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1 = rawRow317 := by decide +kernel

theorem rowCheck317 : row317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow317 := by decide +kernel

theorem rowEval317 (x : Key → ℝ) : Integer.Sparse.eval row317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck317, Integer.Sparse.eval_collectBalanced, rawRowCheck317]

theorem rawRowCheck318 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1 = rawRow318 := by decide +kernel

theorem rowCheck318 : row318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow318 := by decide +kernel

theorem rowEval318 (x : Key → ℝ) : Integer.Sparse.eval row318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck318, Integer.Sparse.eval_collectBalanced, rawRowCheck318]

theorem rawRowCheck319 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1 = rawRow319 := by decide +kernel

theorem rowCheck319 : row319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow319 := by decide +kernel

theorem rowEval319 (x : Key → ℝ) : Integer.Sparse.eval row319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck319, Integer.Sparse.eval_collectBalanced, rawRowCheck319]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck320 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1 = rawRow320 := by decide +kernel

theorem rowCheck320 : row320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow320 := by decide +kernel

theorem rowEval320 (x : Key → ℝ) : Integer.Sparse.eval row320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck320, Integer.Sparse.eval_collectBalanced, rawRowCheck320]

theorem rawRowCheck321 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1 = rawRow321 := by decide +kernel

theorem rowCheck321 : row321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow321 := by decide +kernel

theorem rowEval321 (x : Key → ℝ) : Integer.Sparse.eval row321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck321, Integer.Sparse.eval_collectBalanced, rawRowCheck321]

theorem rawRowCheck322 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1 = rawRow322 := by decide +kernel

theorem rowCheck322 : row322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow322 := by decide +kernel

theorem rowEval322 (x : Key → ℝ) : Integer.Sparse.eval row322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck322, Integer.Sparse.eval_collectBalanced, rawRowCheck322]

theorem rawRowCheck323 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1 = rawRow323 := by decide +kernel

theorem rowCheck323 : row323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow323 := by decide +kernel

theorem rowEval323 (x : Key → ℝ) : Integer.Sparse.eval row323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck323, Integer.Sparse.eval_collectBalanced, rawRowCheck323]

theorem rawRowCheck324 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow324 := by decide +kernel

theorem rowCheck324 : row324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow324 := by decide +kernel

theorem rowEval324 (x : Key → ℝ) : Integer.Sparse.eval row324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck324, Integer.Sparse.eval_collectBalanced, rawRowCheck324]

theorem rawRowCheck325 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow325 := by decide +kernel

theorem rowCheck325 : row325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow325 := by decide +kernel

theorem rowEval325 (x : Key → ℝ) : Integer.Sparse.eval row325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck325, Integer.Sparse.eval_collectBalanced, rawRowCheck325]

theorem rawRowCheck326 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1 = rawRow326 := by decide +kernel

theorem rowCheck326 : row326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow326 := by decide +kernel

theorem rowEval326 (x : Key → ℝ) : Integer.Sparse.eval row326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck326, Integer.Sparse.eval_collectBalanced, rawRowCheck326]

theorem rawRowCheck327 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1 = rawRow327 := by decide +kernel

theorem rowCheck327 : row327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow327 := by decide +kernel

theorem rowEval327 (x : Key → ℝ) : Integer.Sparse.eval row327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck327, Integer.Sparse.eval_collectBalanced, rawRowCheck327]

theorem rawRowCheck328 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow328 := by decide +kernel

theorem rowCheck328 : row328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow328 := by decide +kernel

theorem rowEval328 (x : Key → ℝ) : Integer.Sparse.eval row328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck328, Integer.Sparse.eval_collectBalanced, rawRowCheck328]

theorem rawRowCheck329 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow329 := by decide +kernel

theorem rowCheck329 : row329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow329 := by decide +kernel

theorem rowEval329 (x : Key → ℝ) : Integer.Sparse.eval row329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck329, Integer.Sparse.eval_collectBalanced, rawRowCheck329]

theorem rawRowCheck330 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow330 := by decide +kernel

theorem rowCheck330 : row330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow330 := by decide +kernel

theorem rowEval330 (x : Key → ℝ) : Integer.Sparse.eval row330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck330, Integer.Sparse.eval_collectBalanced, rawRowCheck330]

theorem rawRowCheck331 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow331 := by decide +kernel

theorem rowCheck331 : row331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow331 := by decide +kernel

theorem rowEval331 (x : Key → ℝ) : Integer.Sparse.eval row331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck331, Integer.Sparse.eval_collectBalanced, rawRowCheck331]

theorem rawRowCheck332 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1 = rawRow332 := by decide +kernel

theorem rowCheck332 : row332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow332 := by decide +kernel

theorem rowEval332 (x : Key → ℝ) : Integer.Sparse.eval row332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck332, Integer.Sparse.eval_collectBalanced, rawRowCheck332]

theorem rawRowCheck333 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1 = rawRow333 := by decide +kernel

theorem rowCheck333 : row333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow333 := by decide +kernel

theorem rowEval333 (x : Key → ℝ) : Integer.Sparse.eval row333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck333, Integer.Sparse.eval_collectBalanced, rawRowCheck333]

theorem rawRowCheck334 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1 = rawRow334 := by decide +kernel

theorem rowCheck334 : row334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow334 := by decide +kernel

theorem rowEval334 (x : Key → ℝ) : Integer.Sparse.eval row334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck334, Integer.Sparse.eval_collectBalanced, rawRowCheck334]

theorem rawRowCheck335 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1 = rawRow335 := by decide +kernel

theorem rowCheck335 : row335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow335 := by decide +kernel

theorem rowEval335 (x : Key → ℝ) : Integer.Sparse.eval row335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck335, Integer.Sparse.eval_collectBalanced, rawRowCheck335]

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

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval294 x
  · exact rowEval295 x
  · exact rowEval296 x
  · exact rowEval297 x
  · exact rowEval298 x
  · exact rowEval299 x
  · exact rowEval300 x
  · exact rowEval301 x
  · exact rowEval302 x
  · exact rowEval303 x
  · exact rowEval304 x
  · exact rowEval305 x
  · exact rowEval306 x
  · exact rowEval307 x
  · exact rowEval308 x
  · exact rowEval309 x
  · exact rowEval310 x
  · exact rowEval311 x
  · exact rowEval312 x
  · exact rowEval313 x
  · exact rowEval314 x
  · exact rowEval315 x
  · exact rowEval316 x
  · exact rowEval317 x
  · exact rowEval318 x
  · exact rowEval319 x
  · exact rowEval320 x
  · exact rowEval321 x
  · exact rowEval322 x
  · exact rowEval323 x
  · exact rowEval324 x
  · exact rowEval325 x
  · exact rowEval326 x
  · exact rowEval327 x
  · exact rowEval328 x
  · exact rowEval329 x
  · exact rowEval330 x
  · exact rowEval331 x
  · exact rowEval332 x
  · exact rowEval333 x
  · exact rowEval334 x
  · exact rowEval335 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

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

theorem entryEvalRow3_e_oai (j : Fin 5) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 3 j) (GramNormalization.eval B) =
      (GramFunctions.Block0.forms 3).mixedGram (GramFunctions.Block0.forms j) B := by
  fin_cases j
  · exact entryEval3_0 B hB
  · exact entryEval3_1 B hB
  · exact entryEval3_2 B hB
  · exact entryEval3_3_e B hB
  · exact (entryEval4_3_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow3_e_oai
