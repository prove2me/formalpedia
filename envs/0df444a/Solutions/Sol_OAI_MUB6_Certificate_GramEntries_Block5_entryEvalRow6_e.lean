-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:52:24.160195+00:00
-- url     : https://prove2.me/submissions/1e5d3573-900b-4033-9b5f-ea2a028a6ac8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_6_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19344 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19344 := by decide +kernel

theorem rowCheck19344 : row19344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19344 := by decide +kernel

theorem rowEval19344 (x : Key → ℝ) : Integer.Sparse.eval row19344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19344, Integer.Sparse.eval_collectBalanced, rawRowCheck19344]

theorem rawRowCheck19345 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19345 := by decide +kernel

theorem rowCheck19345 : row19345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19345 := by decide +kernel

theorem rowEval19345 (x : Key → ℝ) : Integer.Sparse.eval row19345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19345, Integer.Sparse.eval_collectBalanced, rawRowCheck19345]

theorem rawRowCheck19346 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19346 := by decide +kernel

theorem rowCheck19346 : row19346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19346 := by decide +kernel

theorem rowEval19346 (x : Key → ℝ) : Integer.Sparse.eval row19346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19346, Integer.Sparse.eval_collectBalanced, rawRowCheck19346]

theorem rawRowCheck19347 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19347 := by decide +kernel

theorem rowCheck19347 : row19347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19347 := by decide +kernel

theorem rowEval19347 (x : Key → ℝ) : Integer.Sparse.eval row19347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19347, Integer.Sparse.eval_collectBalanced, rawRowCheck19347]

theorem rawRowCheck19348 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19348 := by decide +kernel

theorem rowCheck19348 : row19348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19348 := by decide +kernel

theorem rowEval19348 (x : Key → ℝ) : Integer.Sparse.eval row19348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19348, Integer.Sparse.eval_collectBalanced, rawRowCheck19348]

theorem rawRowCheck19349 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19349 := by decide +kernel

theorem rowCheck19349 : row19349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19349 := by decide +kernel

theorem rowEval19349 (x : Key → ℝ) : Integer.Sparse.eval row19349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19349, Integer.Sparse.eval_collectBalanced, rawRowCheck19349]

theorem rawRowCheck19350 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6 = rawRow19350 := by decide +kernel

theorem rowCheck19350 : row19350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19350 := by decide +kernel

theorem rowEval19350 (x : Key → ℝ) : Integer.Sparse.eval row19350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19350, Integer.Sparse.eval_collectBalanced, rawRowCheck19350]

theorem rawRowCheck19351 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6 = rawRow19351 := by decide +kernel

theorem rowCheck19351 : row19351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19351 := by decide +kernel

theorem rowEval19351 (x : Key → ℝ) : Integer.Sparse.eval row19351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19351, Integer.Sparse.eval_collectBalanced, rawRowCheck19351]

theorem rawRowCheck19352 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6 = rawRow19352 := by decide +kernel

theorem rowCheck19352 : row19352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19352 := by decide +kernel

theorem rowEval19352 (x : Key → ℝ) : Integer.Sparse.eval row19352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19352, Integer.Sparse.eval_collectBalanced, rawRowCheck19352]

theorem rawRowCheck19353 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6 = rawRow19353 := by decide +kernel

theorem rowCheck19353 : row19353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19353 := by decide +kernel

theorem rowEval19353 (x : Key → ℝ) : Integer.Sparse.eval row19353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19353, Integer.Sparse.eval_collectBalanced, rawRowCheck19353]

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

theorem rawRowCheck19504 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19504 := by decide +kernel

theorem rowCheck19504 : row19504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19504 := by decide +kernel

theorem rowEval19504 (x : Key → ℝ) : Integer.Sparse.eval row19504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19504, Integer.Sparse.eval_collectBalanced, rawRowCheck19504]

theorem rawRowCheck19505 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19505 := by decide +kernel

theorem rowCheck19505 : row19505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19505 := by decide +kernel

theorem rowEval19505 (x : Key → ℝ) : Integer.Sparse.eval row19505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19505, Integer.Sparse.eval_collectBalanced, rawRowCheck19505]

theorem rawRowCheck19506 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19506 := by decide +kernel

theorem rowCheck19506 : row19506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19506 := by decide +kernel

theorem rowEval19506 (x : Key → ℝ) : Integer.Sparse.eval row19506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19506, Integer.Sparse.eval_collectBalanced, rawRowCheck19506]

theorem rawRowCheck19507 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19507 := by decide +kernel

theorem rowCheck19507 : row19507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19507 := by decide +kernel

theorem rowEval19507 (x : Key → ℝ) : Integer.Sparse.eval row19507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19507, Integer.Sparse.eval_collectBalanced, rawRowCheck19507]

theorem rawRowCheck19508 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19508 := by decide +kernel

theorem rowCheck19508 : row19508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19508 := by decide +kernel

theorem rowEval19508 (x : Key → ℝ) : Integer.Sparse.eval row19508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19508, Integer.Sparse.eval_collectBalanced, rawRowCheck19508]

theorem rawRowCheck19509 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19509 := by decide +kernel

theorem rowCheck19509 : row19509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19509 := by decide +kernel

theorem rowEval19509 (x : Key → ℝ) : Integer.Sparse.eval row19509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19509, Integer.Sparse.eval_collectBalanced, rawRowCheck19509]

theorem rawRowCheck19510 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19510 := by decide +kernel

theorem rowCheck19510 : row19510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19510 := by decide +kernel

theorem rowEval19510 (x : Key → ℝ) : Integer.Sparse.eval row19510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19510, Integer.Sparse.eval_collectBalanced, rawRowCheck19510]

theorem rawRowCheck19511 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19511 := by decide +kernel

theorem rowCheck19511 : row19511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19511 := by decide +kernel

theorem rowEval19511 (x : Key → ℝ) : Integer.Sparse.eval row19511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19511, Integer.Sparse.eval_collectBalanced, rawRowCheck19511]

theorem rawRowCheck19512 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19512 := by decide +kernel

theorem rowCheck19512 : row19512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19512 := by decide +kernel

theorem rowEval19512 (x : Key → ℝ) : Integer.Sparse.eval row19512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19512, Integer.Sparse.eval_collectBalanced, rawRowCheck19512]

theorem rawRowCheck19513 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19513 := by decide +kernel

theorem rowCheck19513 : row19513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19513 := by decide +kernel

theorem rowEval19513 (x : Key → ℝ) : Integer.Sparse.eval row19513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19513, Integer.Sparse.eval_collectBalanced, rawRowCheck19513]

theorem rawRowCheck19514 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19514 := by decide +kernel

theorem rowCheck19514 : row19514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19514 := by decide +kernel

theorem rowEval19514 (x : Key → ℝ) : Integer.Sparse.eval row19514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19514, Integer.Sparse.eval_collectBalanced, rawRowCheck19514]

theorem rawRowCheck19515 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19515 := by decide +kernel

theorem rowCheck19515 : row19515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19515 := by decide +kernel

theorem rowEval19515 (x : Key → ℝ) : Integer.Sparse.eval row19515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19515, Integer.Sparse.eval_collectBalanced, rawRowCheck19515]

theorem rawRowCheck19516 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19516 := by decide +kernel

theorem rowCheck19516 : row19516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19516 := by decide +kernel

theorem rowEval19516 (x : Key → ℝ) : Integer.Sparse.eval row19516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19516, Integer.Sparse.eval_collectBalanced, rawRowCheck19516]

theorem rawRowCheck19517 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19517 := by decide +kernel

theorem rowCheck19517 : row19517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19517 := by decide +kernel

theorem rowEval19517 (x : Key → ℝ) : Integer.Sparse.eval row19517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19517, Integer.Sparse.eval_collectBalanced, rawRowCheck19517]

theorem rawRowCheck19518 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19518 := by decide +kernel

theorem rowCheck19518 : row19518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19518 := by decide +kernel

theorem rowEval19518 (x : Key → ℝ) : Integer.Sparse.eval row19518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19518, Integer.Sparse.eval_collectBalanced, rawRowCheck19518]

theorem rawRowCheck19519 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19519 := by decide +kernel

theorem rowCheck19519 : row19519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19519 := by decide +kernel

theorem rowEval19519 (x : Key → ℝ) : Integer.Sparse.eval row19519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19519, Integer.Sparse.eval_collectBalanced, rawRowCheck19519]

theorem rawRowCheck19520 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19520 := by decide +kernel

theorem rowCheck19520 : row19520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19520 := by decide +kernel

theorem rowEval19520 (x : Key → ℝ) : Integer.Sparse.eval row19520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19520, Integer.Sparse.eval_collectBalanced, rawRowCheck19520]

theorem rawRowCheck19521 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19521 := by decide +kernel

theorem rowCheck19521 : row19521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19521 := by decide +kernel

theorem rowEval19521 (x : Key → ℝ) : Integer.Sparse.eval row19521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19521, Integer.Sparse.eval_collectBalanced, rawRowCheck19521]

theorem rawRowCheck19522 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19522 := by decide +kernel

theorem rowCheck19522 : row19522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19522 := by decide +kernel

theorem rowEval19522 (x : Key → ℝ) : Integer.Sparse.eval row19522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19522, Integer.Sparse.eval_collectBalanced, rawRowCheck19522]

theorem rawRowCheck19523 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19523 := by decide +kernel

theorem rowCheck19523 : row19523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19523 := by decide +kernel

theorem rowEval19523 (x : Key → ℝ) : Integer.Sparse.eval row19523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19523, Integer.Sparse.eval_collectBalanced, rawRowCheck19523]

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

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19504 x
  · exact rowEval19505 x
  · exact rowEval19506 x
  · exact rowEval19507 x
  · exact rowEval19508 x
  · exact rowEval19509 x
  · exact rowEval19510 x
  · exact rowEval19511 x
  · exact rowEval19512 x
  · exact rowEval19513 x
  · exact rowEval19514 x
  · exact rowEval19515 x
  · exact rowEval19516 x
  · exact rowEval19517 x
  · exact rowEval19518 x
  · exact rowEval19519 x
  · exact rowEval19520 x
  · exact rowEval19521 x
  · exact rowEval19522 x
  · exact rowEval19523 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

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

theorem rawRowCheck18939 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18939 := by decide +kernel

theorem rowCheck18939 : row18939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18939 := by decide +kernel

theorem rowEval18939 (x : Key → ℝ) : Integer.Sparse.eval row18939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18939, Integer.Sparse.eval_collectBalanced, rawRowCheck18939]

theorem rawRowCheck18940 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18940 := by decide +kernel

theorem rowCheck18940 : row18940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18940 := by decide +kernel

theorem rowEval18940 (x : Key → ℝ) : Integer.Sparse.eval row18940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18940, Integer.Sparse.eval_collectBalanced, rawRowCheck18940]

theorem rawRowCheck18941 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18941 := by decide +kernel

theorem rowCheck18941 : row18941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18941 := by decide +kernel

theorem rowEval18941 (x : Key → ℝ) : Integer.Sparse.eval row18941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18941, Integer.Sparse.eval_collectBalanced, rawRowCheck18941]

theorem rawRowCheck18942 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18942 := by decide +kernel

theorem rowCheck18942 : row18942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18942 := by decide +kernel

theorem rowEval18942 (x : Key → ℝ) : Integer.Sparse.eval row18942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18942, Integer.Sparse.eval_collectBalanced, rawRowCheck18942]

theorem rawRowCheck18943 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18943 := by decide +kernel

theorem rowCheck18943 : row18943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18943 := by decide +kernel

theorem rowEval18943 (x : Key → ℝ) : Integer.Sparse.eval row18943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18943, Integer.Sparse.eval_collectBalanced, rawRowCheck18943]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck18944 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18944 := by decide +kernel

theorem rowCheck18944 : row18944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18944 := by decide +kernel

theorem rowEval18944 (x : Key → ℝ) : Integer.Sparse.eval row18944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18944, Integer.Sparse.eval_collectBalanced, rawRowCheck18944]

theorem rawRowCheck18945 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18945 := by decide +kernel

theorem rowCheck18945 : row18945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18945 := by decide +kernel

theorem rowEval18945 (x : Key → ℝ) : Integer.Sparse.eval row18945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18945, Integer.Sparse.eval_collectBalanced, rawRowCheck18945]

theorem rawRowCheck18946 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18946 := by decide +kernel

theorem rowCheck18946 : row18946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18946 := by decide +kernel

theorem rowEval18946 (x : Key → ℝ) : Integer.Sparse.eval row18946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18946, Integer.Sparse.eval_collectBalanced, rawRowCheck18946]

theorem rawRowCheck18947 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18947 := by decide +kernel

theorem rowCheck18947 : row18947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18947 := by decide +kernel

theorem rowEval18947 (x : Key → ℝ) : Integer.Sparse.eval row18947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18947, Integer.Sparse.eval_collectBalanced, rawRowCheck18947]

theorem rawRowCheck18948 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18948 := by decide +kernel

theorem rowCheck18948 : row18948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18948 := by decide +kernel

theorem rowEval18948 (x : Key → ℝ) : Integer.Sparse.eval row18948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18948, Integer.Sparse.eval_collectBalanced, rawRowCheck18948]

theorem rawRowCheck18949 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18949 := by decide +kernel

theorem rowCheck18949 : row18949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18949 := by decide +kernel

theorem rowEval18949 (x : Key → ℝ) : Integer.Sparse.eval row18949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18949, Integer.Sparse.eval_collectBalanced, rawRowCheck18949]

theorem rawRowCheck18950 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18950 := by decide +kernel

theorem rowCheck18950 : row18950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18950 := by decide +kernel

theorem rowEval18950 (x : Key → ℝ) : Integer.Sparse.eval row18950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18950, Integer.Sparse.eval_collectBalanced, rawRowCheck18950]

theorem rawRowCheck18951 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18951 := by decide +kernel

theorem rowCheck18951 : row18951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18951 := by decide +kernel

theorem rowEval18951 (x : Key → ℝ) : Integer.Sparse.eval row18951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18951, Integer.Sparse.eval_collectBalanced, rawRowCheck18951]

theorem rawRowCheck18952 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18952 := by decide +kernel

theorem rowCheck18952 : row18952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18952 := by decide +kernel

theorem rowEval18952 (x : Key → ℝ) : Integer.Sparse.eval row18952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18952, Integer.Sparse.eval_collectBalanced, rawRowCheck18952]

theorem rawRowCheck18953 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18953 := by decide +kernel

theorem rowCheck18953 : row18953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18953 := by decide +kernel

theorem rowEval18953 (x : Key → ℝ) : Integer.Sparse.eval row18953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18953, Integer.Sparse.eval_collectBalanced, rawRowCheck18953]

theorem rawRowCheck18954 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18954 := by decide +kernel

theorem rowCheck18954 : row18954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18954 := by decide +kernel

theorem rowEval18954 (x : Key → ℝ) : Integer.Sparse.eval row18954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18954, Integer.Sparse.eval_collectBalanced, rawRowCheck18954]

theorem rawRowCheck18955 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18955 := by decide +kernel

theorem rowCheck18955 : row18955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18955 := by decide +kernel

theorem rowEval18955 (x : Key → ℝ) : Integer.Sparse.eval row18955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18955, Integer.Sparse.eval_collectBalanced, rawRowCheck18955]

theorem rawRowCheck18956 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18956 := by decide +kernel

theorem rowCheck18956 : row18956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18956 := by decide +kernel

theorem rowEval18956 (x : Key → ℝ) : Integer.Sparse.eval row18956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18956, Integer.Sparse.eval_collectBalanced, rawRowCheck18956]

theorem rawRowCheck18957 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18957 := by decide +kernel

theorem rowCheck18957 : row18957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18957 := by decide +kernel

theorem rowEval18957 (x : Key → ℝ) : Integer.Sparse.eval row18957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18957, Integer.Sparse.eval_collectBalanced, rawRowCheck18957]

theorem rawRowCheck18958 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18958 := by decide +kernel

theorem rowCheck18958 : row18958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18958 := by decide +kernel

theorem rowEval18958 (x : Key → ℝ) : Integer.Sparse.eval row18958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18958, Integer.Sparse.eval_collectBalanced, rawRowCheck18958]

theorem rawRowCheck18959 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18959 := by decide +kernel

theorem rowCheck18959 : row18959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18959 := by decide +kernel

theorem rowEval18959 (x : Key → ℝ) : Integer.Sparse.eval row18959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18959, Integer.Sparse.eval_collectBalanced, rawRowCheck18959]

theorem rawRowCheck18960 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18960 := by decide +kernel

theorem rowCheck18960 : row18960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18960 := by decide +kernel

theorem rowEval18960 (x : Key → ℝ) : Integer.Sparse.eval row18960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18960, Integer.Sparse.eval_collectBalanced, rawRowCheck18960]

theorem rawRowCheck18961 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18961 := by decide +kernel

theorem rowCheck18961 : row18961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18961 := by decide +kernel

theorem rowEval18961 (x : Key → ℝ) : Integer.Sparse.eval row18961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18961, Integer.Sparse.eval_collectBalanced, rawRowCheck18961]

theorem rawRowCheck18962 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18962 := by decide +kernel

theorem rowCheck18962 : row18962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18962 := by decide +kernel

theorem rowEval18962 (x : Key → ℝ) : Integer.Sparse.eval row18962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18962, Integer.Sparse.eval_collectBalanced, rawRowCheck18962]

theorem rawRowCheck18963 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1 = rawRow18963 := by decide +kernel

theorem rowCheck18963 : row18963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18963 := by decide +kernel

theorem rowEval18963 (x : Key → ℝ) : Integer.Sparse.eval row18963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18963, Integer.Sparse.eval_collectBalanced, rawRowCheck18963]

theorem rawRowCheck18964 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1 = rawRow18964 := by decide +kernel

theorem rowCheck18964 : row18964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18964 := by decide +kernel

theorem rowEval18964 (x : Key → ℝ) : Integer.Sparse.eval row18964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18964, Integer.Sparse.eval_collectBalanced, rawRowCheck18964]

theorem rawRowCheck18965 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1 = rawRow18965 := by decide +kernel

theorem rowCheck18965 : row18965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18965 := by decide +kernel

theorem rowEval18965 (x : Key → ℝ) : Integer.Sparse.eval row18965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18965, Integer.Sparse.eval_collectBalanced, rawRowCheck18965]

theorem rawRowCheck18966 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1 = rawRow18966 := by decide +kernel

theorem rowCheck18966 : row18966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18966 := by decide +kernel

theorem rowEval18966 (x : Key → ℝ) : Integer.Sparse.eval row18966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18966, Integer.Sparse.eval_collectBalanced, rawRowCheck18966]

theorem rawRowCheck18967 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1 = rawRow18967 := by decide +kernel

theorem rowCheck18967 : row18967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18967 := by decide +kernel

theorem rowEval18967 (x : Key → ℝ) : Integer.Sparse.eval row18967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18967, Integer.Sparse.eval_collectBalanced, rawRowCheck18967]

theorem rawRowCheck18968 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1 = rawRow18968 := by decide +kernel

theorem rowCheck18968 : row18968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18968 := by decide +kernel

theorem rowEval18968 (x : Key → ℝ) : Integer.Sparse.eval row18968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form1) x := by
  rw [rowCheck18968, Integer.Sparse.eval_collectBalanced, rawRowCheck18968]

theorem rawRowCheck18969 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1 = rawRow18969 := by decide +kernel

theorem rowCheck18969 : row18969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18969 := by decide +kernel

theorem rowEval18969 (x : Key → ℝ) : Integer.Sparse.eval row18969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18969, Integer.Sparse.eval_collectBalanced, rawRowCheck18969]

theorem rawRowCheck18970 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1 = rawRow18970 := by decide +kernel

theorem rowCheck18970 : row18970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18970 := by decide +kernel

theorem rowEval18970 (x : Key → ℝ) : Integer.Sparse.eval row18970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18970, Integer.Sparse.eval_collectBalanced, rawRowCheck18970]

theorem rawRowCheck18971 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1 = rawRow18971 := by decide +kernel

theorem rowCheck18971 : row18971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18971 := by decide +kernel

theorem rowEval18971 (x : Key → ℝ) : Integer.Sparse.eval row18971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18971, Integer.Sparse.eval_collectBalanced, rawRowCheck18971]

theorem rawRowCheck18972 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18972 := by decide +kernel

theorem rowCheck18972 : row18972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18972 := by decide +kernel

theorem rowEval18972 (x : Key → ℝ) : Integer.Sparse.eval row18972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18972, Integer.Sparse.eval_collectBalanced, rawRowCheck18972]

theorem rawRowCheck18973 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18973 := by decide +kernel

theorem rowCheck18973 : row18973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18973 := by decide +kernel

theorem rowEval18973 (x : Key → ℝ) : Integer.Sparse.eval row18973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18973, Integer.Sparse.eval_collectBalanced, rawRowCheck18973]

theorem rawRowCheck18974 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18974 := by decide +kernel

theorem rowCheck18974 : row18974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18974 := by decide +kernel

theorem rowEval18974 (x : Key → ℝ) : Integer.Sparse.eval row18974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18974, Integer.Sparse.eval_collectBalanced, rawRowCheck18974]

theorem rawRowCheck18975 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18975 := by decide +kernel

theorem rowCheck18975 : row18975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18975 := by decide +kernel

theorem rowEval18975 (x : Key → ℝ) : Integer.Sparse.eval row18975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18975, Integer.Sparse.eval_collectBalanced, rawRowCheck18975]

theorem rawRowCheck18976 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18976 := by decide +kernel

theorem rowCheck18976 : row18976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18976 := by decide +kernel

theorem rowEval18976 (x : Key → ℝ) : Integer.Sparse.eval row18976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18976, Integer.Sparse.eval_collectBalanced, rawRowCheck18976]

theorem rawRowCheck18977 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18977 := by decide +kernel

theorem rowCheck18977 : row18977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18977 := by decide +kernel

theorem rowEval18977 (x : Key → ℝ) : Integer.Sparse.eval row18977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18977, Integer.Sparse.eval_collectBalanced, rawRowCheck18977]

theorem rawRowCheck18978 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18978 := by decide +kernel

theorem rowCheck18978 : row18978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18978 := by decide +kernel

theorem rowEval18978 (x : Key → ℝ) : Integer.Sparse.eval row18978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18978, Integer.Sparse.eval_collectBalanced, rawRowCheck18978]

theorem rawRowCheck18979 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18979 := by decide +kernel

theorem rowCheck18979 : row18979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18979 := by decide +kernel

theorem rowEval18979 (x : Key → ℝ) : Integer.Sparse.eval row18979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18979, Integer.Sparse.eval_collectBalanced, rawRowCheck18979]

theorem rawRowCheck18980 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18980 := by decide +kernel

theorem rowCheck18980 : row18980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18980 := by decide +kernel

theorem rowEval18980 (x : Key → ℝ) : Integer.Sparse.eval row18980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18980, Integer.Sparse.eval_collectBalanced, rawRowCheck18980]

theorem rawRowCheck18981 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18981 := by decide +kernel

theorem rowCheck18981 : row18981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18981 := by decide +kernel

theorem rowEval18981 (x : Key → ℝ) : Integer.Sparse.eval row18981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18981, Integer.Sparse.eval_collectBalanced, rawRowCheck18981]

theorem rawRowCheck18982 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18982 := by decide +kernel

theorem rowCheck18982 : row18982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18982 := by decide +kernel

theorem rowEval18982 (x : Key → ℝ) : Integer.Sparse.eval row18982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18982, Integer.Sparse.eval_collectBalanced, rawRowCheck18982]

theorem rawRowCheck18983 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form2 = rawRow18983 := by decide +kernel

theorem rowCheck18983 : row18983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18983 := by decide +kernel

theorem rowEval18983 (x : Key → ℝ) : Integer.Sparse.eval row18983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18983, Integer.Sparse.eval_collectBalanced, rawRowCheck18983]

theorem rawRowCheck18984 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form2 = rawRow18984 := by decide +kernel

theorem rowCheck18984 : row18984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18984 := by decide +kernel

theorem rowEval18984 (x : Key → ℝ) : Integer.Sparse.eval row18984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18984, Integer.Sparse.eval_collectBalanced, rawRowCheck18984]

theorem rawRowCheck18985 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form2 = rawRow18985 := by decide +kernel

theorem rowCheck18985 : row18985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18985 := by decide +kernel

theorem rowEval18985 (x : Key → ℝ) : Integer.Sparse.eval row18985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18985, Integer.Sparse.eval_collectBalanced, rawRowCheck18985]

theorem rawRowCheck18986 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form2 = rawRow18986 := by decide +kernel

theorem rowCheck18986 : row18986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18986 := by decide +kernel

theorem rowEval18986 (x : Key → ℝ) : Integer.Sparse.eval row18986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18986, Integer.Sparse.eval_collectBalanced, rawRowCheck18986]

theorem rawRowCheck18987 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form2 = rawRow18987 := by decide +kernel

theorem rowCheck18987 : row18987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18987 := by decide +kernel

theorem rowEval18987 (x : Key → ℝ) : Integer.Sparse.eval row18987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18987, Integer.Sparse.eval_collectBalanced, rawRowCheck18987]

theorem rawRowCheck18988 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form2 = rawRow18988 := by decide +kernel

theorem rowCheck18988 : row18988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18988 := by decide +kernel

theorem rowEval18988 (x : Key → ℝ) : Integer.Sparse.eval row18988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form2) x := by
  rw [rowCheck18988, Integer.Sparse.eval_collectBalanced, rawRowCheck18988]

theorem rawRowCheck18989 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form2 = rawRow18989 := by decide +kernel

theorem rowCheck18989 : row18989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18989 := by decide +kernel

theorem rowEval18989 (x : Key → ℝ) : Integer.Sparse.eval row18989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18989, Integer.Sparse.eval_collectBalanced, rawRowCheck18989]

theorem rawRowCheck18990 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form2 = rawRow18990 := by decide +kernel

theorem rowCheck18990 : row18990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18990 := by decide +kernel

theorem rowEval18990 (x : Key → ℝ) : Integer.Sparse.eval row18990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18990, Integer.Sparse.eval_collectBalanced, rawRowCheck18990]

theorem rawRowCheck18991 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form2 = rawRow18991 := by decide +kernel

theorem rowCheck18991 : row18991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18991 := by decide +kernel

theorem rowEval18991 (x : Key → ℝ) : Integer.Sparse.eval row18991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18991, Integer.Sparse.eval_collectBalanced, rawRowCheck18991]

theorem rawRowCheck18992 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18992 := by decide +kernel

theorem rowCheck18992 : row18992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18992 := by decide +kernel

theorem rowEval18992 (x : Key → ℝ) : Integer.Sparse.eval row18992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18992, Integer.Sparse.eval_collectBalanced, rawRowCheck18992]

theorem rawRowCheck18993 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18993 := by decide +kernel

theorem rowCheck18993 : row18993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18993 := by decide +kernel

theorem rowEval18993 (x : Key → ℝ) : Integer.Sparse.eval row18993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18993, Integer.Sparse.eval_collectBalanced, rawRowCheck18993]

theorem rawRowCheck18994 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18994 := by decide +kernel

theorem rowCheck18994 : row18994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18994 := by decide +kernel

theorem rowEval18994 (x : Key → ℝ) : Integer.Sparse.eval row18994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18994, Integer.Sparse.eval_collectBalanced, rawRowCheck18994]

theorem rawRowCheck18995 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18995 := by decide +kernel

theorem rowCheck18995 : row18995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18995 := by decide +kernel

theorem rowEval18995 (x : Key → ℝ) : Integer.Sparse.eval row18995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18995, Integer.Sparse.eval_collectBalanced, rawRowCheck18995]

theorem rawRowCheck18996 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18996 := by decide +kernel

theorem rowCheck18996 : row18996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18996 := by decide +kernel

theorem rowEval18996 (x : Key → ℝ) : Integer.Sparse.eval row18996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18996, Integer.Sparse.eval_collectBalanced, rawRowCheck18996]

theorem rawRowCheck18997 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18997 := by decide +kernel

theorem rowCheck18997 : row18997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18997 := by decide +kernel

theorem rowEval18997 (x : Key → ℝ) : Integer.Sparse.eval row18997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18997, Integer.Sparse.eval_collectBalanced, rawRowCheck18997]

theorem rawRowCheck18998 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18998 := by decide +kernel

theorem rowCheck18998 : row18998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18998 := by decide +kernel

theorem rowEval18998 (x : Key → ℝ) : Integer.Sparse.eval row18998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18998, Integer.Sparse.eval_collectBalanced, rawRowCheck18998]

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

theorem rawRowCheck19019 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form4 = rawRow19019 := by decide +kernel

theorem rowCheck19019 : row19019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19019 := by decide +kernel

theorem rowEval19019 (x : Key → ℝ) : Integer.Sparse.eval row19019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19019, Integer.Sparse.eval_collectBalanced, rawRowCheck19019]

theorem rawRowCheck19020 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form4 = rawRow19020 := by decide +kernel

theorem rowCheck19020 : row19020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19020 := by decide +kernel

theorem rowEval19020 (x : Key → ℝ) : Integer.Sparse.eval row19020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19020, Integer.Sparse.eval_collectBalanced, rawRowCheck19020]

theorem rawRowCheck19021 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form4 = rawRow19021 := by decide +kernel

theorem rowCheck19021 : row19021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19021 := by decide +kernel

theorem rowEval19021 (x : Key → ℝ) : Integer.Sparse.eval row19021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19021, Integer.Sparse.eval_collectBalanced, rawRowCheck19021]

theorem rawRowCheck19022 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19022 := by decide +kernel

theorem rowCheck19022 : row19022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19022 := by decide +kernel

theorem rowEval19022 (x : Key → ℝ) : Integer.Sparse.eval row19022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19022, Integer.Sparse.eval_collectBalanced, rawRowCheck19022]

theorem rawRowCheck19023 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form4 = rawRow19023 := by decide +kernel

theorem rowCheck19023 : row19023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19023 := by decide +kernel

theorem rowEval19023 (x : Key → ℝ) : Integer.Sparse.eval row19023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19023, Integer.Sparse.eval_collectBalanced, rawRowCheck19023]

theorem rawRowCheck19024 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form4 = rawRow19024 := by decide +kernel

theorem rowCheck19024 : row19024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19024 := by decide +kernel

theorem rowEval19024 (x : Key → ℝ) : Integer.Sparse.eval row19024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19024, Integer.Sparse.eval_collectBalanced, rawRowCheck19024]

theorem rawRowCheck19025 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form4 = rawRow19025 := by decide +kernel

theorem rowCheck19025 : row19025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19025 := by decide +kernel

theorem rowEval19025 (x : Key → ℝ) : Integer.Sparse.eval row19025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19025, Integer.Sparse.eval_collectBalanced, rawRowCheck19025]

theorem rawRowCheck19026 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form4 = rawRow19026 := by decide +kernel

theorem rowCheck19026 : row19026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19026 := by decide +kernel

theorem rowEval19026 (x : Key → ℝ) : Integer.Sparse.eval row19026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19026, Integer.Sparse.eval_collectBalanced, rawRowCheck19026]

theorem rawRowCheck19027 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form4 = rawRow19027 := by decide +kernel

theorem rowCheck19027 : row19027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19027 := by decide +kernel

theorem rowEval19027 (x : Key → ℝ) : Integer.Sparse.eval row19027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19027, Integer.Sparse.eval_collectBalanced, rawRowCheck19027]

theorem rawRowCheck19028 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form4 = rawRow19028 := by decide +kernel

theorem rowCheck19028 : row19028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19028 := by decide +kernel

theorem rowEval19028 (x : Key → ℝ) : Integer.Sparse.eval row19028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19028, Integer.Sparse.eval_collectBalanced, rawRowCheck19028]

theorem rawRowCheck19029 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form4 = rawRow19029 := by decide +kernel

theorem rowCheck19029 : row19029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19029 := by decide +kernel

theorem rowEval19029 (x : Key → ℝ) : Integer.Sparse.eval row19029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19029, Integer.Sparse.eval_collectBalanced, rawRowCheck19029]

theorem rawRowCheck19030 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form4 = rawRow19030 := by decide +kernel

theorem rowCheck19030 : row19030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19030 := by decide +kernel

theorem rowEval19030 (x : Key → ℝ) : Integer.Sparse.eval row19030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19030, Integer.Sparse.eval_collectBalanced, rawRowCheck19030]

theorem rawRowCheck19031 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form4 = rawRow19031 := by decide +kernel

theorem rowCheck19031 : row19031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19031 := by decide +kernel

theorem rowEval19031 (x : Key → ℝ) : Integer.Sparse.eval row19031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19031, Integer.Sparse.eval_collectBalanced, rawRowCheck19031]

theorem rawRowCheck19032 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form4 = rawRow19032 := by decide +kernel

theorem rowCheck19032 : row19032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19032 := by decide +kernel

theorem rowEval19032 (x : Key → ℝ) : Integer.Sparse.eval row19032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19032, Integer.Sparse.eval_collectBalanced, rawRowCheck19032]

theorem rawRowCheck19033 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form4 = rawRow19033 := by decide +kernel

theorem rowCheck19033 : row19033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19033 := by decide +kernel

theorem rowEval19033 (x : Key → ℝ) : Integer.Sparse.eval row19033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19033, Integer.Sparse.eval_collectBalanced, rawRowCheck19033]

theorem rawRowCheck19034 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form4 = rawRow19034 := by decide +kernel

theorem rowCheck19034 : row19034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19034 := by decide +kernel

theorem rowEval19034 (x : Key → ℝ) : Integer.Sparse.eval row19034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19034, Integer.Sparse.eval_collectBalanced, rawRowCheck19034]

theorem rawRowCheck19035 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19035 := by decide +kernel

theorem rowCheck19035 : row19035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19035 := by decide +kernel

theorem rowEval19035 (x : Key → ℝ) : Integer.Sparse.eval row19035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19035, Integer.Sparse.eval_collectBalanced, rawRowCheck19035]

theorem rawRowCheck19036 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form4 = rawRow19036 := by decide +kernel

theorem rowCheck19036 : row19036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19036 := by decide +kernel

theorem rowEval19036 (x : Key → ℝ) : Integer.Sparse.eval row19036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19036, Integer.Sparse.eval_collectBalanced, rawRowCheck19036]

theorem rawRowCheck19037 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form4 = rawRow19037 := by decide +kernel

theorem rowCheck19037 : row19037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19037 := by decide +kernel

theorem rowEval19037 (x : Key → ℝ) : Integer.Sparse.eval row19037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19037, Integer.Sparse.eval_collectBalanced, rawRowCheck19037]

theorem rawRowCheck19038 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form4 = rawRow19038 := by decide +kernel

theorem rowCheck19038 : row19038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19038 := by decide +kernel

theorem rowEval19038 (x : Key → ℝ) : Integer.Sparse.eval row19038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck19038, Integer.Sparse.eval_collectBalanced, rawRowCheck19038]

theorem rawRowCheck19039 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19039 := by decide +kernel

theorem rowCheck19039 : row19039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19039 := by decide +kernel

theorem rowEval19039 (x : Key → ℝ) : Integer.Sparse.eval row19039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19039, Integer.Sparse.eval_collectBalanced, rawRowCheck19039]

theorem rawRowCheck19040 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19040 := by decide +kernel

theorem rowCheck19040 : row19040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19040 := by decide +kernel

theorem rowEval19040 (x : Key → ℝ) : Integer.Sparse.eval row19040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19040, Integer.Sparse.eval_collectBalanced, rawRowCheck19040]

theorem rawRowCheck19041 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19041 := by decide +kernel

theorem rowCheck19041 : row19041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19041 := by decide +kernel

theorem rowEval19041 (x : Key → ℝ) : Integer.Sparse.eval row19041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19041, Integer.Sparse.eval_collectBalanced, rawRowCheck19041]

theorem rawRowCheck19042 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19042 := by decide +kernel

theorem rowCheck19042 : row19042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19042 := by decide +kernel

theorem rowEval19042 (x : Key → ℝ) : Integer.Sparse.eval row19042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19042, Integer.Sparse.eval_collectBalanced, rawRowCheck19042]

theorem rawRowCheck19043 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5 = rawRow19043 := by decide +kernel

theorem rowCheck19043 : row19043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19043 := by decide +kernel

theorem rowEval19043 (x : Key → ℝ) : Integer.Sparse.eval row19043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19043, Integer.Sparse.eval_collectBalanced, rawRowCheck19043]

theorem rawRowCheck19044 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5 = rawRow19044 := by decide +kernel

theorem rowCheck19044 : row19044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19044 := by decide +kernel

theorem rowEval19044 (x : Key → ℝ) : Integer.Sparse.eval row19044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19044, Integer.Sparse.eval_collectBalanced, rawRowCheck19044]

theorem rawRowCheck19045 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5 = rawRow19045 := by decide +kernel

theorem rowCheck19045 : row19045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19045 := by decide +kernel

theorem rowEval19045 (x : Key → ℝ) : Integer.Sparse.eval row19045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19045, Integer.Sparse.eval_collectBalanced, rawRowCheck19045]

theorem rawRowCheck19046 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5 = rawRow19046 := by decide +kernel

theorem rowCheck19046 : row19046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19046 := by decide +kernel

theorem rowEval19046 (x : Key → ℝ) : Integer.Sparse.eval row19046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19046, Integer.Sparse.eval_collectBalanced, rawRowCheck19046]

theorem rawRowCheck19047 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5 = rawRow19047 := by decide +kernel

theorem rowCheck19047 : row19047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19047 := by decide +kernel

theorem rowEval19047 (x : Key → ℝ) : Integer.Sparse.eval row19047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19047, Integer.Sparse.eval_collectBalanced, rawRowCheck19047]

theorem rawRowCheck19048 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5 = rawRow19048 := by decide +kernel

theorem rowCheck19048 : row19048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19048 := by decide +kernel

theorem rowEval19048 (x : Key → ℝ) : Integer.Sparse.eval row19048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form5) x := by
  rw [rowCheck19048, Integer.Sparse.eval_collectBalanced, rawRowCheck19048]

theorem rawRowCheck19049 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5 = rawRow19049 := by decide +kernel

theorem rowCheck19049 : row19049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19049 := by decide +kernel

theorem rowEval19049 (x : Key → ℝ) : Integer.Sparse.eval row19049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19049, Integer.Sparse.eval_collectBalanced, rawRowCheck19049]

theorem rawRowCheck19050 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5 = rawRow19050 := by decide +kernel

theorem rowCheck19050 : row19050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19050 := by decide +kernel

theorem rowEval19050 (x : Key → ℝ) : Integer.Sparse.eval row19050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19050, Integer.Sparse.eval_collectBalanced, rawRowCheck19050]

theorem rawRowCheck19051 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5 = rawRow19051 := by decide +kernel

theorem rowCheck19051 : row19051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19051 := by decide +kernel

theorem rowEval19051 (x : Key → ℝ) : Integer.Sparse.eval row19051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19051, Integer.Sparse.eval_collectBalanced, rawRowCheck19051]

theorem rawRowCheck19052 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19052 := by decide +kernel

theorem rowCheck19052 : row19052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19052 := by decide +kernel

theorem rowEval19052 (x : Key → ℝ) : Integer.Sparse.eval row19052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19052, Integer.Sparse.eval_collectBalanced, rawRowCheck19052]

theorem rawRowCheck19053 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19053 := by decide +kernel

theorem rowCheck19053 : row19053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19053 := by decide +kernel

theorem rowEval19053 (x : Key → ℝ) : Integer.Sparse.eval row19053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19053, Integer.Sparse.eval_collectBalanced, rawRowCheck19053]

theorem rawRowCheck19054 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19054 := by decide +kernel

theorem rowCheck19054 : row19054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19054 := by decide +kernel

theorem rowEval19054 (x : Key → ℝ) : Integer.Sparse.eval row19054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19054, Integer.Sparse.eval_collectBalanced, rawRowCheck19054]

theorem rawRowCheck19055 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19055 := by decide +kernel

theorem rowCheck19055 : row19055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19055 := by decide +kernel

theorem rowEval19055 (x : Key → ℝ) : Integer.Sparse.eval row19055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19055, Integer.Sparse.eval_collectBalanced, rawRowCheck19055]

theorem rawRowCheck19056 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5 = rawRow19056 := by decide +kernel

theorem rowCheck19056 : row19056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19056 := by decide +kernel

theorem rowEval19056 (x : Key → ℝ) : Integer.Sparse.eval row19056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19056, Integer.Sparse.eval_collectBalanced, rawRowCheck19056]

theorem rawRowCheck19057 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5 = rawRow19057 := by decide +kernel

theorem rowCheck19057 : row19057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19057 := by decide +kernel

theorem rowEval19057 (x : Key → ℝ) : Integer.Sparse.eval row19057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19057, Integer.Sparse.eval_collectBalanced, rawRowCheck19057]

theorem rawRowCheck19058 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5 = rawRow19058 := by decide +kernel

theorem rowCheck19058 : row19058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19058 := by decide +kernel

theorem rowEval19058 (x : Key → ℝ) : Integer.Sparse.eval row19058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form5) x := by
  rw [rowCheck19058, Integer.Sparse.eval_collectBalanced, rawRowCheck19058]

theorem rawRowCheck19059 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form6 = rawRow19059 := by decide +kernel

theorem rowCheck19059 : row19059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19059 := by decide +kernel

theorem rowEval19059 (x : Key → ℝ) : Integer.Sparse.eval row19059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19059, Integer.Sparse.eval_collectBalanced, rawRowCheck19059]

theorem rawRowCheck19060 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form6 = rawRow19060 := by decide +kernel

theorem rowCheck19060 : row19060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19060 := by decide +kernel

theorem rowEval19060 (x : Key → ℝ) : Integer.Sparse.eval row19060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19060, Integer.Sparse.eval_collectBalanced, rawRowCheck19060]

theorem rawRowCheck19061 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form6 = rawRow19061 := by decide +kernel

theorem rowCheck19061 : row19061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19061 := by decide +kernel

theorem rowEval19061 (x : Key → ℝ) : Integer.Sparse.eval row19061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19061, Integer.Sparse.eval_collectBalanced, rawRowCheck19061]

theorem rawRowCheck19062 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19062 := by decide +kernel

theorem rowCheck19062 : row19062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19062 := by decide +kernel

theorem rowEval19062 (x : Key → ℝ) : Integer.Sparse.eval row19062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19062, Integer.Sparse.eval_collectBalanced, rawRowCheck19062]

theorem rawRowCheck19063 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form6 = rawRow19063 := by decide +kernel

theorem rowCheck19063 : row19063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19063 := by decide +kernel

theorem rowEval19063 (x : Key → ℝ) : Integer.Sparse.eval row19063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19063, Integer.Sparse.eval_collectBalanced, rawRowCheck19063]

theorem rawRowCheck19064 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form6 = rawRow19064 := by decide +kernel

theorem rowCheck19064 : row19064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19064 := by decide +kernel

theorem rowEval19064 (x : Key → ℝ) : Integer.Sparse.eval row19064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19064, Integer.Sparse.eval_collectBalanced, rawRowCheck19064]

theorem rawRowCheck19065 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form6 = rawRow19065 := by decide +kernel

theorem rowCheck19065 : row19065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19065 := by decide +kernel

theorem rowEval19065 (x : Key → ℝ) : Integer.Sparse.eval row19065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19065, Integer.Sparse.eval_collectBalanced, rawRowCheck19065]

theorem rawRowCheck19066 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form6 = rawRow19066 := by decide +kernel

theorem rowCheck19066 : row19066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19066 := by decide +kernel

theorem rowEval19066 (x : Key → ℝ) : Integer.Sparse.eval row19066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19066, Integer.Sparse.eval_collectBalanced, rawRowCheck19066]

theorem rawRowCheck19067 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form6 = rawRow19067 := by decide +kernel

theorem rowCheck19067 : row19067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19067 := by decide +kernel

theorem rowEval19067 (x : Key → ℝ) : Integer.Sparse.eval row19067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19067, Integer.Sparse.eval_collectBalanced, rawRowCheck19067]

theorem rawRowCheck19068 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form6 = rawRow19068 := by decide +kernel

theorem rowCheck19068 : row19068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19068 := by decide +kernel

theorem rowEval19068 (x : Key → ℝ) : Integer.Sparse.eval row19068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19068, Integer.Sparse.eval_collectBalanced, rawRowCheck19068]

theorem rawRowCheck19069 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form6 = rawRow19069 := by decide +kernel

theorem rowCheck19069 : row19069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19069 := by decide +kernel

theorem rowEval19069 (x : Key → ℝ) : Integer.Sparse.eval row19069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19069, Integer.Sparse.eval_collectBalanced, rawRowCheck19069]

theorem rawRowCheck19070 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form6 = rawRow19070 := by decide +kernel

theorem rowCheck19070 : row19070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19070 := by decide +kernel

theorem rowEval19070 (x : Key → ℝ) : Integer.Sparse.eval row19070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19070, Integer.Sparse.eval_collectBalanced, rawRowCheck19070]

theorem rawRowCheck19071 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form6 = rawRow19071 := by decide +kernel

theorem rowCheck19071 : row19071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19071 := by decide +kernel

theorem rowEval19071 (x : Key → ℝ) : Integer.Sparse.eval row19071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19071, Integer.Sparse.eval_collectBalanced, rawRowCheck19071]

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

theorem rawRowCheck19072 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form6 = rawRow19072 := by decide +kernel

theorem rowCheck19072 : row19072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19072 := by decide +kernel

theorem rowEval19072 (x : Key → ℝ) : Integer.Sparse.eval row19072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19072, Integer.Sparse.eval_collectBalanced, rawRowCheck19072]

theorem rawRowCheck19073 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form6 = rawRow19073 := by decide +kernel

theorem rowCheck19073 : row19073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19073 := by decide +kernel

theorem rowEval19073 (x : Key → ℝ) : Integer.Sparse.eval row19073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19073, Integer.Sparse.eval_collectBalanced, rawRowCheck19073]

theorem rawRowCheck19074 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form6 = rawRow19074 := by decide +kernel

theorem rowCheck19074 : row19074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19074 := by decide +kernel

theorem rowEval19074 (x : Key → ℝ) : Integer.Sparse.eval row19074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19074, Integer.Sparse.eval_collectBalanced, rawRowCheck19074]

theorem rawRowCheck19075 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19075 := by decide +kernel

theorem rowCheck19075 : row19075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19075 := by decide +kernel

theorem rowEval19075 (x : Key → ℝ) : Integer.Sparse.eval row19075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19075, Integer.Sparse.eval_collectBalanced, rawRowCheck19075]

theorem rawRowCheck19076 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form6 = rawRow19076 := by decide +kernel

theorem rowCheck19076 : row19076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19076 := by decide +kernel

theorem rowEval19076 (x : Key → ℝ) : Integer.Sparse.eval row19076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19076, Integer.Sparse.eval_collectBalanced, rawRowCheck19076]

theorem rawRowCheck19077 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form6 = rawRow19077 := by decide +kernel

theorem rowCheck19077 : row19077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19077 := by decide +kernel

theorem rowEval19077 (x : Key → ℝ) : Integer.Sparse.eval row19077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19077, Integer.Sparse.eval_collectBalanced, rawRowCheck19077]

theorem rawRowCheck19078 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form6 = rawRow19078 := by decide +kernel

theorem rowCheck19078 : row19078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19078 := by decide +kernel

theorem rowEval19078 (x : Key → ℝ) : Integer.Sparse.eval row19078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block5.form6) x := by
  rw [rowCheck19078, Integer.Sparse.eval_collectBalanced, rawRowCheck19078]

theorem rawRowCheck19199 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19199 := by decide +kernel

theorem rowCheck19199 : row19199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19199 := by decide +kernel

theorem rowEval19199 (x : Key → ℝ) : Integer.Sparse.eval row19199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19199, Integer.Sparse.eval_collectBalanced, rawRowCheck19199]

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

theorem entryCheck6_0 : entry6_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_0 k)) := by decide +kernel

theorem rowsSound6_0 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18939 x
  · exact rowEval18940 x
  · exact rowEval18941 x
  · exact rowEval18942 x
  · exact rowEval18943 x
  · exact rowEval18944 x
  · exact rowEval18945 x
  · exact rowEval18946 x
  · exact rowEval18947 x
  · exact rowEval18948 x
  · exact rowEval18949 x
  · exact rowEval18950 x
  · exact rowEval18951 x
  · exact rowEval18952 x
  · exact rowEval18953 x
  · exact rowEval18954 x
  · exact rowEval18955 x
  · exact rowEval18956 x
  · exact rowEval18957 x
  · exact rowEval18958 x

theorem entryEval6_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_0 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck6_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_0]

theorem entryCheck6_1 : entry6_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_1 k)) := by decide +kernel

theorem rowsSound6_1 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18959 x
  · exact rowEval18960 x
  · exact rowEval18961 x
  · exact rowEval18962 x
  · exact rowEval18963 x
  · exact rowEval18964 x
  · exact rowEval18965 x
  · exact rowEval18966 x
  · exact rowEval18967 x
  · exact rowEval18968 x
  · exact rowEval18969 x
  · exact rowEval18970 x
  · exact rowEval18971 x
  · exact rowEval18972 x
  · exact rowEval18973 x
  · exact rowEval18974 x
  · exact rowEval18975 x
  · exact rowEval18976 x
  · exact rowEval18977 x
  · exact rowEval18978 x

theorem entryEval6_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_1 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck6_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_1]

theorem entryCheck6_2 : entry6_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_2 k)) := by decide +kernel

theorem rowsSound6_2 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18979 x
  · exact rowEval18980 x
  · exact rowEval18981 x
  · exact rowEval18982 x
  · exact rowEval18983 x
  · exact rowEval18984 x
  · exact rowEval18985 x
  · exact rowEval18986 x
  · exact rowEval18987 x
  · exact rowEval18988 x
  · exact rowEval18989 x
  · exact rowEval18990 x
  · exact rowEval18991 x
  · exact rowEval18992 x
  · exact rowEval18993 x
  · exact rowEval18994 x
  · exact rowEval18995 x
  · exact rowEval18996 x
  · exact rowEval18997 x
  · exact rowEval18998 x

theorem entryEval6_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_2 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck6_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_2]

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

theorem entryCheck6_4 : entry6_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_4 k)) := by decide +kernel

theorem rowsSound6_4 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19019 x
  · exact rowEval19020 x
  · exact rowEval19021 x
  · exact rowEval19022 x
  · exact rowEval19023 x
  · exact rowEval19024 x
  · exact rowEval19025 x
  · exact rowEval19026 x
  · exact rowEval19027 x
  · exact rowEval19028 x
  · exact rowEval19029 x
  · exact rowEval19030 x
  · exact rowEval19031 x
  · exact rowEval19032 x
  · exact rowEval19033 x
  · exact rowEval19034 x
  · exact rowEval19035 x
  · exact rowEval19036 x
  · exact rowEval19037 x
  · exact rowEval19038 x

theorem entryEval6_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_4 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck6_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_4]

theorem entryCheck6_5 : entry6_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_5 k)) := by decide +kernel

theorem rowsSound6_5 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form5) x := by
  fin_cases k
  · exact rowEval19039 x
  · exact rowEval19040 x
  · exact rowEval19041 x
  · exact rowEval19042 x
  · exact rowEval19043 x
  · exact rowEval19044 x
  · exact rowEval19045 x
  · exact rowEval19046 x
  · exact rowEval19047 x
  · exact rowEval19048 x
  · exact rowEval19049 x
  · exact rowEval19050 x
  · exact rowEval19051 x
  · exact rowEval19052 x
  · exact rowEval19053 x
  · exact rowEval19054 x
  · exact rowEval19055 x
  · exact rowEval19056 x
  · exact rowEval19057 x
  · exact rowEval19058 x

theorem entryEval6_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_5 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form5 B := by
  rw [entryCheck6_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_5]

theorem entryCheck6_6 : entry6_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form6.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form6.terms k).coefficient) (rows6_6 k)) := by decide +kernel

theorem rowsSound6_6 (k : Fin GramFunctions.Block5.form6.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows6_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form6.terms k).tag (GramFunctions.Block5.form6.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19059 x
  · exact rowEval19060 x
  · exact rowEval19061 x
  · exact rowEval19062 x
  · exact rowEval19063 x
  · exact rowEval19064 x
  · exact rowEval19065 x
  · exact rowEval19066 x
  · exact rowEval19067 x
  · exact rowEval19068 x
  · exact rowEval19069 x
  · exact rowEval19070 x
  · exact rowEval19071 x
  · exact rowEval19072 x
  · exact rowEval19073 x
  · exact rowEval19074 x
  · exact rowEval19075 x
  · exact rowEval19076 x
  · exact rowEval19077 x
  · exact rowEval19078 x

theorem entryEval6_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry6_6 (GramNormalization.eval B) = GramFunctions.Block5.form6.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck6_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form6 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound6_6]

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

theorem rawRowCheck19200 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19200 := by decide +kernel

theorem rowCheck19200 : row19200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19200 := by decide +kernel

theorem rowEval19200 (x : Key → ℝ) : Integer.Sparse.eval row19200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19200, Integer.Sparse.eval_collectBalanced, rawRowCheck19200]

theorem rawRowCheck19201 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19201 := by decide +kernel

theorem rowCheck19201 : row19201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19201 := by decide +kernel

theorem rowEval19201 (x : Key → ℝ) : Integer.Sparse.eval row19201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19201, Integer.Sparse.eval_collectBalanced, rawRowCheck19201]

theorem rawRowCheck19202 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19202 := by decide +kernel

theorem rowCheck19202 : row19202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19202 := by decide +kernel

theorem rowEval19202 (x : Key → ℝ) : Integer.Sparse.eval row19202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19202, Integer.Sparse.eval_collectBalanced, rawRowCheck19202]

theorem rawRowCheck19203 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19203 := by decide +kernel

theorem rowCheck19203 : row19203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19203 := by decide +kernel

theorem rowEval19203 (x : Key → ℝ) : Integer.Sparse.eval row19203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19203, Integer.Sparse.eval_collectBalanced, rawRowCheck19203]

theorem rawRowCheck19204 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19204 := by decide +kernel

theorem rowCheck19204 : row19204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19204 := by decide +kernel

theorem rowEval19204 (x : Key → ℝ) : Integer.Sparse.eval row19204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19204, Integer.Sparse.eval_collectBalanced, rawRowCheck19204]

theorem rawRowCheck19205 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19205 := by decide +kernel

theorem rowCheck19205 : row19205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19205 := by decide +kernel

theorem rowEval19205 (x : Key → ℝ) : Integer.Sparse.eval row19205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19205, Integer.Sparse.eval_collectBalanced, rawRowCheck19205]

theorem rawRowCheck19206 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19206 := by decide +kernel

theorem rowCheck19206 : row19206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19206 := by decide +kernel

theorem rowEval19206 (x : Key → ℝ) : Integer.Sparse.eval row19206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19206, Integer.Sparse.eval_collectBalanced, rawRowCheck19206]

theorem rawRowCheck19207 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19207 := by decide +kernel

theorem rowCheck19207 : row19207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19207 := by decide +kernel

theorem rowEval19207 (x : Key → ℝ) : Integer.Sparse.eval row19207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19207, Integer.Sparse.eval_collectBalanced, rawRowCheck19207]

theorem rawRowCheck19208 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19208 := by decide +kernel

theorem rowCheck19208 : row19208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19208 := by decide +kernel

theorem rowEval19208 (x : Key → ℝ) : Integer.Sparse.eval row19208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19208, Integer.Sparse.eval_collectBalanced, rawRowCheck19208]

theorem rawRowCheck19209 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19209 := by decide +kernel

theorem rowCheck19209 : row19209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19209 := by decide +kernel

theorem rowEval19209 (x : Key → ℝ) : Integer.Sparse.eval row19209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19209, Integer.Sparse.eval_collectBalanced, rawRowCheck19209]

theorem rawRowCheck19210 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19210 := by decide +kernel

theorem rowCheck19210 : row19210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19210 := by decide +kernel

theorem rowEval19210 (x : Key → ℝ) : Integer.Sparse.eval row19210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19210, Integer.Sparse.eval_collectBalanced, rawRowCheck19210]

theorem rawRowCheck19211 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19211 := by decide +kernel

theorem rowCheck19211 : row19211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19211 := by decide +kernel

theorem rowEval19211 (x : Key → ℝ) : Integer.Sparse.eval row19211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19211, Integer.Sparse.eval_collectBalanced, rawRowCheck19211]

theorem rawRowCheck19212 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19212 := by decide +kernel

theorem rowCheck19212 : row19212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19212 := by decide +kernel

theorem rowEval19212 (x : Key → ℝ) : Integer.Sparse.eval row19212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19212, Integer.Sparse.eval_collectBalanced, rawRowCheck19212]

theorem rawRowCheck19213 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6 = rawRow19213 := by decide +kernel

theorem rowCheck19213 : row19213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19213 := by decide +kernel

theorem rowEval19213 (x : Key → ℝ) : Integer.Sparse.eval row19213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19213, Integer.Sparse.eval_collectBalanced, rawRowCheck19213]

theorem rawRowCheck19214 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6 = rawRow19214 := by decide +kernel

theorem rowCheck19214 : row19214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19214 := by decide +kernel

theorem rowEval19214 (x : Key → ℝ) : Integer.Sparse.eval row19214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19214, Integer.Sparse.eval_collectBalanced, rawRowCheck19214]

theorem rawRowCheck19215 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6 = rawRow19215 := by decide +kernel

theorem rowCheck19215 : row19215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19215 := by decide +kernel

theorem rowEval19215 (x : Key → ℝ) : Integer.Sparse.eval row19215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19215, Integer.Sparse.eval_collectBalanced, rawRowCheck19215]

theorem rawRowCheck19216 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6 = rawRow19216 := by decide +kernel

theorem rowCheck19216 : row19216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19216 := by decide +kernel

theorem rowEval19216 (x : Key → ℝ) : Integer.Sparse.eval row19216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19216, Integer.Sparse.eval_collectBalanced, rawRowCheck19216]

theorem rawRowCheck19217 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6 = rawRow19217 := by decide +kernel

theorem rowCheck19217 : row19217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19217 := by decide +kernel

theorem rowEval19217 (x : Key → ℝ) : Integer.Sparse.eval row19217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19217, Integer.Sparse.eval_collectBalanced, rawRowCheck19217]

theorem rawRowCheck19218 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6 = rawRow19218 := by decide +kernel

theorem rowCheck19218 : row19218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19218 := by decide +kernel

theorem rowEval19218 (x : Key → ℝ) : Integer.Sparse.eval row19218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19218, Integer.Sparse.eval_collectBalanced, rawRowCheck19218]

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

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19199 x
  · exact rowEval19200 x
  · exact rowEval19201 x
  · exact rowEval19202 x
  · exact rowEval19203 x
  · exact rowEval19204 x
  · exact rowEval19205 x
  · exact rowEval19206 x
  · exact rowEval19207 x
  · exact rowEval19208 x
  · exact rowEval19209 x
  · exact rowEval19210 x
  · exact rowEval19211 x
  · exact rowEval19212 x
  · exact rowEval19213 x
  · exact rowEval19214 x
  · exact rowEval19215 x
  · exact rowEval19216 x
  · exact rowEval19217 x
  · exact rowEval19218 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

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

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19344 x
  · exact rowEval19345 x
  · exact rowEval19346 x
  · exact rowEval19347 x
  · exact rowEval19348 x
  · exact rowEval19349 x
  · exact rowEval19350 x
  · exact rowEval19351 x
  · exact rowEval19352 x
  · exact rowEval19353 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

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

theorem entryEvalRow6_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 6 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 6).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval6_0 B hB
  · exact entryEval6_1 B hB
  · exact entryEval6_2 B hB
  · exact entryEval6_3 B hB
  · exact entryEval6_4 B hB
  · exact entryEval6_5 B hB
  · exact entryEval6_6 B hB
  · exact (entryEval7_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_6 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_6_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6_e_oai
