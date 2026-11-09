-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:27:39.625331+00:00
-- url     : https://prove2.me/submissions/d436e397-1d1b-4606-af69-559fb2b7a2f0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E019
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E052
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval19_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval20_19_e

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

theorem rawRowCheck4570 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4570 := by decide +kernel

theorem rowCheck4570 : row4570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4570 := by decide +kernel

theorem rowEval4570 (x : Key → ℝ) : Integer.Sparse.eval row4570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4570, Integer.Sparse.eval_collectBalanced, rawRowCheck4570]

theorem rawRowCheck4571 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4571 := by decide +kernel

theorem rowCheck4571 : row4571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4571 := by decide +kernel

theorem rowEval4571 (x : Key → ℝ) : Integer.Sparse.eval row4571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4571, Integer.Sparse.eval_collectBalanced, rawRowCheck4571]

theorem rawRowCheck4572 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4572 := by decide +kernel

theorem rowCheck4572 : row4572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4572 := by decide +kernel

theorem rowEval4572 (x : Key → ℝ) : Integer.Sparse.eval row4572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4572, Integer.Sparse.eval_collectBalanced, rawRowCheck4572]

theorem rawRowCheck4573 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4573 := by decide +kernel

theorem rowCheck4573 : row4573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4573 := by decide +kernel

theorem rowEval4573 (x : Key → ℝ) : Integer.Sparse.eval row4573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4573, Integer.Sparse.eval_collectBalanced, rawRowCheck4573]

theorem rawRowCheck4574 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4574 := by decide +kernel

theorem rowCheck4574 : row4574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4574 := by decide +kernel

theorem rowEval4574 (x : Key → ℝ) : Integer.Sparse.eval row4574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4574, Integer.Sparse.eval_collectBalanced, rawRowCheck4574]

theorem rawRowCheck4575 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4575 := by decide +kernel

theorem rowCheck4575 : row4575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4575 := by decide +kernel

theorem rowEval4575 (x : Key → ℝ) : Integer.Sparse.eval row4575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4575, Integer.Sparse.eval_collectBalanced, rawRowCheck4575]

theorem rawRowCheck4576 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4576 := by decide +kernel

theorem rowCheck4576 : row4576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4576 := by decide +kernel

theorem rowEval4576 (x : Key → ℝ) : Integer.Sparse.eval row4576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4576, Integer.Sparse.eval_collectBalanced, rawRowCheck4576]

theorem rawRowCheck4577 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4577 := by decide +kernel

theorem rowCheck4577 : row4577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4577 := by decide +kernel

theorem rowEval4577 (x : Key → ℝ) : Integer.Sparse.eval row4577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4577, Integer.Sparse.eval_collectBalanced, rawRowCheck4577]

theorem rawRowCheck4578 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4578 := by decide +kernel

theorem rowCheck4578 : row4578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4578 := by decide +kernel

theorem rowEval4578 (x : Key → ℝ) : Integer.Sparse.eval row4578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4578, Integer.Sparse.eval_collectBalanced, rawRowCheck4578]

theorem rawRowCheck4579 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4579 := by decide +kernel

theorem rowCheck4579 : row4579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4579 := by decide +kernel

theorem rowEval4579 (x : Key → ℝ) : Integer.Sparse.eval row4579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4579, Integer.Sparse.eval_collectBalanced, rawRowCheck4579]

theorem rawRowCheck4580 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4580 := by decide +kernel

theorem rowCheck4580 : row4580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4580 := by decide +kernel

theorem rowEval4580 (x : Key → ℝ) : Integer.Sparse.eval row4580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4580, Integer.Sparse.eval_collectBalanced, rawRowCheck4580]

theorem rawRowCheck4581 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4581 := by decide +kernel

theorem rowCheck4581 : row4581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4581 := by decide +kernel

theorem rowEval4581 (x : Key → ℝ) : Integer.Sparse.eval row4581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4581, Integer.Sparse.eval_collectBalanced, rawRowCheck4581]

theorem rawRowCheck4582 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4582 := by decide +kernel

theorem rowCheck4582 : row4582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4582 := by decide +kernel

theorem rowEval4582 (x : Key → ℝ) : Integer.Sparse.eval row4582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4582, Integer.Sparse.eval_collectBalanced, rawRowCheck4582]

theorem rawRowCheck4583 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4583 := by decide +kernel

theorem rowCheck4583 : row4583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4583 := by decide +kernel

theorem rowEval4583 (x : Key → ℝ) : Integer.Sparse.eval row4583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4583, Integer.Sparse.eval_collectBalanced, rawRowCheck4583]

theorem rawRowCheck4598 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4598 := by decide +kernel

theorem rowCheck4598 : row4598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4598 := by decide +kernel

theorem rowEval4598 (x : Key → ℝ) : Integer.Sparse.eval row4598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4598, Integer.Sparse.eval_collectBalanced, rawRowCheck4598]

theorem rawRowCheck4599 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4599 := by decide +kernel

theorem rowCheck4599 : row4599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4599 := by decide +kernel

theorem rowEval4599 (x : Key → ℝ) : Integer.Sparse.eval row4599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4599, Integer.Sparse.eval_collectBalanced, rawRowCheck4599]

theorem rawRowCheck4600 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4600 := by decide +kernel

theorem rowCheck4600 : row4600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4600 := by decide +kernel

theorem rowEval4600 (x : Key → ℝ) : Integer.Sparse.eval row4600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4600, Integer.Sparse.eval_collectBalanced, rawRowCheck4600]

theorem rawRowCheck4601 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4601 := by decide +kernel

theorem rowCheck4601 : row4601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4601 := by decide +kernel

theorem rowEval4601 (x : Key → ℝ) : Integer.Sparse.eval row4601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4601, Integer.Sparse.eval_collectBalanced, rawRowCheck4601]

theorem rawRowCheck4602 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4602 := by decide +kernel

theorem rowCheck4602 : row4602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4602 := by decide +kernel

theorem rowEval4602 (x : Key → ℝ) : Integer.Sparse.eval row4602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4602, Integer.Sparse.eval_collectBalanced, rawRowCheck4602]

theorem rawRowCheck4603 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4603 := by decide +kernel

theorem rowCheck4603 : row4603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4603 := by decide +kernel

theorem rowEval4603 (x : Key → ℝ) : Integer.Sparse.eval row4603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4603, Integer.Sparse.eval_collectBalanced, rawRowCheck4603]

theorem rawRowCheck4604 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4604 := by decide +kernel

theorem rowCheck4604 : row4604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4604 := by decide +kernel

theorem rowEval4604 (x : Key → ℝ) : Integer.Sparse.eval row4604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4604, Integer.Sparse.eval_collectBalanced, rawRowCheck4604]

theorem rawRowCheck4605 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4605 := by decide +kernel

theorem rowCheck4605 : row4605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4605 := by decide +kernel

theorem rowEval4605 (x : Key → ℝ) : Integer.Sparse.eval row4605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4605, Integer.Sparse.eval_collectBalanced, rawRowCheck4605]

theorem rawRowCheck4606 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4606 := by decide +kernel

theorem rowCheck4606 : row4606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4606 := by decide +kernel

theorem rowEval4606 (x : Key → ℝ) : Integer.Sparse.eval row4606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4606, Integer.Sparse.eval_collectBalanced, rawRowCheck4606]

theorem rawRowCheck4607 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4607 := by decide +kernel

theorem rowCheck4607 : row4607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4607 := by decide +kernel

theorem rowEval4607 (x : Key → ℝ) : Integer.Sparse.eval row4607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4607, Integer.Sparse.eval_collectBalanced, rawRowCheck4607]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck4608 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4608 := by decide +kernel

theorem rowCheck4608 : row4608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4608 := by decide +kernel

theorem rowEval4608 (x : Key → ℝ) : Integer.Sparse.eval row4608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4608, Integer.Sparse.eval_collectBalanced, rawRowCheck4608]

theorem rawRowCheck4609 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4609 := by decide +kernel

theorem rowCheck4609 : row4609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4609 := by decide +kernel

theorem rowEval4609 (x : Key → ℝ) : Integer.Sparse.eval row4609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4609, Integer.Sparse.eval_collectBalanced, rawRowCheck4609]

theorem rawRowCheck4610 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4610 := by decide +kernel

theorem rowCheck4610 : row4610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4610 := by decide +kernel

theorem rowEval4610 (x : Key → ℝ) : Integer.Sparse.eval row4610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4610, Integer.Sparse.eval_collectBalanced, rawRowCheck4610]

theorem rawRowCheck4611 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4611 := by decide +kernel

theorem rowCheck4611 : row4611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4611 := by decide +kernel

theorem rowEval4611 (x : Key → ℝ) : Integer.Sparse.eval row4611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4611, Integer.Sparse.eval_collectBalanced, rawRowCheck4611]

theorem rawRowCheck4612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4612 := by decide +kernel

theorem rowCheck4612 : row4612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4612 := by decide +kernel

theorem rowEval4612 (x : Key → ℝ) : Integer.Sparse.eval row4612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4612, Integer.Sparse.eval_collectBalanced, rawRowCheck4612]

theorem rawRowCheck4613 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4613 := by decide +kernel

theorem rowCheck4613 : row4613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4613 := by decide +kernel

theorem rowEval4613 (x : Key → ℝ) : Integer.Sparse.eval row4613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4613, Integer.Sparse.eval_collectBalanced, rawRowCheck4613]

theorem rawRowCheck4614 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4614 := by decide +kernel

theorem rowCheck4614 : row4614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4614 := by decide +kernel

theorem rowEval4614 (x : Key → ℝ) : Integer.Sparse.eval row4614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4614, Integer.Sparse.eval_collectBalanced, rawRowCheck4614]

theorem rawRowCheck4615 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4615 := by decide +kernel

theorem rowCheck4615 : row4615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4615 := by decide +kernel

theorem rowEval4615 (x : Key → ℝ) : Integer.Sparse.eval row4615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4615, Integer.Sparse.eval_collectBalanced, rawRowCheck4615]

theorem rawRowCheck4616 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4 = rawRow4616 := by decide +kernel

theorem rowCheck4616 : row4616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4616 := by decide +kernel

theorem rowEval4616 (x : Key → ℝ) : Integer.Sparse.eval row4616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck4616, Integer.Sparse.eval_collectBalanced, rawRowCheck4616]

theorem rawRowCheck4617 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4 = rawRow4617 := by decide +kernel

theorem rowCheck4617 : row4617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4617 := by decide +kernel

theorem rowEval4617 (x : Key → ℝ) : Integer.Sparse.eval row4617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4617, Integer.Sparse.eval_collectBalanced, rawRowCheck4617]

theorem rawRowCheck4618 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4 = rawRow4618 := by decide +kernel

theorem rowCheck4618 : row4618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4618 := by decide +kernel

theorem rowEval4618 (x : Key → ℝ) : Integer.Sparse.eval row4618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4618, Integer.Sparse.eval_collectBalanced, rawRowCheck4618]

theorem rawRowCheck4619 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4619 := by decide +kernel

theorem rowCheck4619 : row4619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4619 := by decide +kernel

theorem rowEval4619 (x : Key → ℝ) : Integer.Sparse.eval row4619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4619, Integer.Sparse.eval_collectBalanced, rawRowCheck4619]

theorem rawRowCheck4620 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4620 := by decide +kernel

theorem rowCheck4620 : row4620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4620 := by decide +kernel

theorem rowEval4620 (x : Key → ℝ) : Integer.Sparse.eval row4620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4620, Integer.Sparse.eval_collectBalanced, rawRowCheck4620]

theorem rawRowCheck4621 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4621 := by decide +kernel

theorem rowCheck4621 : row4621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4621 := by decide +kernel

theorem rowEval4621 (x : Key → ℝ) : Integer.Sparse.eval row4621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4621, Integer.Sparse.eval_collectBalanced, rawRowCheck4621]

theorem rawRowCheck4622 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4 = rawRow4622 := by decide +kernel

theorem rowCheck4622 : row4622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4622 := by decide +kernel

theorem rowEval4622 (x : Key → ℝ) : Integer.Sparse.eval row4622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4622, Integer.Sparse.eval_collectBalanced, rawRowCheck4622]

theorem rawRowCheck4623 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4 = rawRow4623 := by decide +kernel

theorem rowCheck4623 : row4623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4623 := by decide +kernel

theorem rowEval4623 (x : Key → ℝ) : Integer.Sparse.eval row4623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4623, Integer.Sparse.eval_collectBalanced, rawRowCheck4623]

theorem rawRowCheck4624 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4 = rawRow4624 := by decide +kernel

theorem rowCheck4624 : row4624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4624 := by decide +kernel

theorem rowEval4624 (x : Key → ℝ) : Integer.Sparse.eval row4624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck4624, Integer.Sparse.eval_collectBalanced, rawRowCheck4624]

theorem rawRowCheck4625 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4 = rawRow4625 := by decide +kernel

theorem rowCheck4625 : row4625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4625 := by decide +kernel

theorem rowEval4625 (x : Key → ℝ) : Integer.Sparse.eval row4625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck4625, Integer.Sparse.eval_collectBalanced, rawRowCheck4625]

theorem rawRowCheck4626 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4626 := by decide +kernel

theorem rowCheck4626 : row4626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4626 := by decide +kernel

theorem rowEval4626 (x : Key → ℝ) : Integer.Sparse.eval row4626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4626, Integer.Sparse.eval_collectBalanced, rawRowCheck4626]

theorem rawRowCheck4627 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4627 := by decide +kernel

theorem rowCheck4627 : row4627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4627 := by decide +kernel

theorem rowEval4627 (x : Key → ℝ) : Integer.Sparse.eval row4627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4627, Integer.Sparse.eval_collectBalanced, rawRowCheck4627]

theorem rawRowCheck4628 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4628 := by decide +kernel

theorem rowCheck4628 : row4628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4628 := by decide +kernel

theorem rowEval4628 (x : Key → ℝ) : Integer.Sparse.eval row4628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4628, Integer.Sparse.eval_collectBalanced, rawRowCheck4628]

theorem rawRowCheck4629 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4629 := by decide +kernel

theorem rowCheck4629 : row4629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4629 := by decide +kernel

theorem rowEval4629 (x : Key → ℝ) : Integer.Sparse.eval row4629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4629, Integer.Sparse.eval_collectBalanced, rawRowCheck4629]

theorem rawRowCheck4630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5 = rawRow4630 := by decide +kernel

theorem rowCheck4630 : row4630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4630 := by decide +kernel

theorem rowEval4630 (x : Key → ℝ) : Integer.Sparse.eval row4630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck4630, Integer.Sparse.eval_collectBalanced, rawRowCheck4630]

theorem rawRowCheck4631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5 = rawRow4631 := by decide +kernel

theorem rowCheck4631 : row4631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4631 := by decide +kernel

theorem rowEval4631 (x : Key → ℝ) : Integer.Sparse.eval row4631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4631, Integer.Sparse.eval_collectBalanced, rawRowCheck4631]

theorem rawRowCheck4632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5 = rawRow4632 := by decide +kernel

theorem rowCheck4632 : row4632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4632 := by decide +kernel

theorem rowEval4632 (x : Key → ℝ) : Integer.Sparse.eval row4632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4632, Integer.Sparse.eval_collectBalanced, rawRowCheck4632]

theorem rawRowCheck4633 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4633 := by decide +kernel

theorem rowCheck4633 : row4633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4633 := by decide +kernel

theorem rowEval4633 (x : Key → ℝ) : Integer.Sparse.eval row4633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4633, Integer.Sparse.eval_collectBalanced, rawRowCheck4633]

theorem rawRowCheck4634 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4634 := by decide +kernel

theorem rowCheck4634 : row4634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4634 := by decide +kernel

theorem rowEval4634 (x : Key → ℝ) : Integer.Sparse.eval row4634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4634, Integer.Sparse.eval_collectBalanced, rawRowCheck4634]

theorem rawRowCheck4635 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4635 := by decide +kernel

theorem rowCheck4635 : row4635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4635 := by decide +kernel

theorem rowEval4635 (x : Key → ℝ) : Integer.Sparse.eval row4635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4635, Integer.Sparse.eval_collectBalanced, rawRowCheck4635]

theorem rawRowCheck4636 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5 = rawRow4636 := by decide +kernel

theorem rowCheck4636 : row4636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4636 := by decide +kernel

theorem rowEval4636 (x : Key → ℝ) : Integer.Sparse.eval row4636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4636, Integer.Sparse.eval_collectBalanced, rawRowCheck4636]

theorem rawRowCheck4637 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5 = rawRow4637 := by decide +kernel

theorem rowCheck4637 : row4637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4637 := by decide +kernel

theorem rowEval4637 (x : Key → ℝ) : Integer.Sparse.eval row4637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4637, Integer.Sparse.eval_collectBalanced, rawRowCheck4637]

theorem rawRowCheck4638 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5 = rawRow4638 := by decide +kernel

theorem rowCheck4638 : row4638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4638 := by decide +kernel

theorem rowEval4638 (x : Key → ℝ) : Integer.Sparse.eval row4638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck4638, Integer.Sparse.eval_collectBalanced, rawRowCheck4638]

theorem rawRowCheck4639 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5 = rawRow4639 := by decide +kernel

theorem rowCheck4639 : row4639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4639 := by decide +kernel

theorem rowEval4639 (x : Key → ℝ) : Integer.Sparse.eval row4639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck4639, Integer.Sparse.eval_collectBalanced, rawRowCheck4639]

theorem rawRowCheck4640 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4640 := by decide +kernel

theorem rowCheck4640 : row4640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4640 := by decide +kernel

theorem rowEval4640 (x : Key → ℝ) : Integer.Sparse.eval row4640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4640, Integer.Sparse.eval_collectBalanced, rawRowCheck4640]

theorem rawRowCheck4641 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4641 := by decide +kernel

theorem rowCheck4641 : row4641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4641 := by decide +kernel

theorem rowEval4641 (x : Key → ℝ) : Integer.Sparse.eval row4641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4641, Integer.Sparse.eval_collectBalanced, rawRowCheck4641]

theorem rawRowCheck4642 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4642 := by decide +kernel

theorem rowCheck4642 : row4642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4642 := by decide +kernel

theorem rowEval4642 (x : Key → ℝ) : Integer.Sparse.eval row4642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4642, Integer.Sparse.eval_collectBalanced, rawRowCheck4642]

theorem rawRowCheck4643 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4643 := by decide +kernel

theorem rowCheck4643 : row4643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4643 := by decide +kernel

theorem rowEval4643 (x : Key → ℝ) : Integer.Sparse.eval row4643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4643, Integer.Sparse.eval_collectBalanced, rawRowCheck4643]

theorem rawRowCheck4644 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6 = rawRow4644 := by decide +kernel

theorem rowCheck4644 : row4644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4644 := by decide +kernel

theorem rowEval4644 (x : Key → ℝ) : Integer.Sparse.eval row4644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck4644, Integer.Sparse.eval_collectBalanced, rawRowCheck4644]

theorem rawRowCheck4645 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6 = rawRow4645 := by decide +kernel

theorem rowCheck4645 : row4645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4645 := by decide +kernel

theorem rowEval4645 (x : Key → ℝ) : Integer.Sparse.eval row4645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4645, Integer.Sparse.eval_collectBalanced, rawRowCheck4645]

theorem rawRowCheck4646 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6 = rawRow4646 := by decide +kernel

theorem rowCheck4646 : row4646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4646 := by decide +kernel

theorem rowEval4646 (x : Key → ℝ) : Integer.Sparse.eval row4646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4646, Integer.Sparse.eval_collectBalanced, rawRowCheck4646]

theorem rawRowCheck4647 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4647 := by decide +kernel

theorem rowCheck4647 : row4647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4647 := by decide +kernel

theorem rowEval4647 (x : Key → ℝ) : Integer.Sparse.eval row4647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4647, Integer.Sparse.eval_collectBalanced, rawRowCheck4647]

theorem rawRowCheck4648 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4648 := by decide +kernel

theorem rowCheck4648 : row4648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4648 := by decide +kernel

theorem rowEval4648 (x : Key → ℝ) : Integer.Sparse.eval row4648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4648, Integer.Sparse.eval_collectBalanced, rawRowCheck4648]

theorem rawRowCheck4649 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4649 := by decide +kernel

theorem rowCheck4649 : row4649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4649 := by decide +kernel

theorem rowEval4649 (x : Key → ℝ) : Integer.Sparse.eval row4649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4649, Integer.Sparse.eval_collectBalanced, rawRowCheck4649]

theorem rawRowCheck4650 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6 = rawRow4650 := by decide +kernel

theorem rowCheck4650 : row4650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4650 := by decide +kernel

theorem rowEval4650 (x : Key → ℝ) : Integer.Sparse.eval row4650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4650, Integer.Sparse.eval_collectBalanced, rawRowCheck4650]

theorem rawRowCheck4651 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6 = rawRow4651 := by decide +kernel

theorem rowCheck4651 : row4651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4651 := by decide +kernel

theorem rowEval4651 (x : Key → ℝ) : Integer.Sparse.eval row4651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4651, Integer.Sparse.eval_collectBalanced, rawRowCheck4651]

theorem rawRowCheck4652 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6 = rawRow4652 := by decide +kernel

theorem rowCheck4652 : row4652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4652 := by decide +kernel

theorem rowEval4652 (x : Key → ℝ) : Integer.Sparse.eval row4652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4652, Integer.Sparse.eval_collectBalanced, rawRowCheck4652]

theorem rawRowCheck4653 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6 = rawRow4653 := by decide +kernel

theorem rowCheck4653 : row4653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4653 := by decide +kernel

theorem rowEval4653 (x : Key → ℝ) : Integer.Sparse.eval row4653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck4653, Integer.Sparse.eval_collectBalanced, rawRowCheck4653]

theorem rawRowCheck4654 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4654 := by decide +kernel

theorem rowCheck4654 : row4654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4654 := by decide +kernel

theorem rowEval4654 (x : Key → ℝ) : Integer.Sparse.eval row4654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4654, Integer.Sparse.eval_collectBalanced, rawRowCheck4654]

theorem rawRowCheck4655 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4655 := by decide +kernel

theorem rowCheck4655 : row4655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4655 := by decide +kernel

theorem rowEval4655 (x : Key → ℝ) : Integer.Sparse.eval row4655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4655, Integer.Sparse.eval_collectBalanced, rawRowCheck4655]

theorem rawRowCheck4656 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4656 := by decide +kernel

theorem rowCheck4656 : row4656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4656 := by decide +kernel

theorem rowEval4656 (x : Key → ℝ) : Integer.Sparse.eval row4656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4656, Integer.Sparse.eval_collectBalanced, rawRowCheck4656]

theorem rawRowCheck4657 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4657 := by decide +kernel

theorem rowCheck4657 : row4657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4657 := by decide +kernel

theorem rowEval4657 (x : Key → ℝ) : Integer.Sparse.eval row4657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4657, Integer.Sparse.eval_collectBalanced, rawRowCheck4657]

theorem rawRowCheck4658 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7 = rawRow4658 := by decide +kernel

theorem rowCheck4658 : row4658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4658 := by decide +kernel

theorem rowEval4658 (x : Key → ℝ) : Integer.Sparse.eval row4658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck4658, Integer.Sparse.eval_collectBalanced, rawRowCheck4658]

theorem rawRowCheck4659 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7 = rawRow4659 := by decide +kernel

theorem rowCheck4659 : row4659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4659 := by decide +kernel

theorem rowEval4659 (x : Key → ℝ) : Integer.Sparse.eval row4659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4659, Integer.Sparse.eval_collectBalanced, rawRowCheck4659]

theorem rawRowCheck4660 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7 = rawRow4660 := by decide +kernel

theorem rowCheck4660 : row4660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4660 := by decide +kernel

theorem rowEval4660 (x : Key → ℝ) : Integer.Sparse.eval row4660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4660, Integer.Sparse.eval_collectBalanced, rawRowCheck4660]

theorem rawRowCheck4661 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4661 := by decide +kernel

theorem rowCheck4661 : row4661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4661 := by decide +kernel

theorem rowEval4661 (x : Key → ℝ) : Integer.Sparse.eval row4661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4661, Integer.Sparse.eval_collectBalanced, rawRowCheck4661]

theorem rawRowCheck4662 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4662 := by decide +kernel

theorem rowCheck4662 : row4662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4662 := by decide +kernel

theorem rowEval4662 (x : Key → ℝ) : Integer.Sparse.eval row4662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4662, Integer.Sparse.eval_collectBalanced, rawRowCheck4662]

theorem rawRowCheck4663 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4663 := by decide +kernel

theorem rowCheck4663 : row4663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4663 := by decide +kernel

theorem rowEval4663 (x : Key → ℝ) : Integer.Sparse.eval row4663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4663, Integer.Sparse.eval_collectBalanced, rawRowCheck4663]

theorem rawRowCheck4664 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7 = rawRow4664 := by decide +kernel

theorem rowCheck4664 : row4664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4664 := by decide +kernel

theorem rowEval4664 (x : Key → ℝ) : Integer.Sparse.eval row4664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4664, Integer.Sparse.eval_collectBalanced, rawRowCheck4664]

theorem rawRowCheck4665 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7 = rawRow4665 := by decide +kernel

theorem rowCheck4665 : row4665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4665 := by decide +kernel

theorem rowEval4665 (x : Key → ℝ) : Integer.Sparse.eval row4665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4665, Integer.Sparse.eval_collectBalanced, rawRowCheck4665]

theorem rawRowCheck4666 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7 = rawRow4666 := by decide +kernel

theorem rowCheck4666 : row4666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4666 := by decide +kernel

theorem rowEval4666 (x : Key → ℝ) : Integer.Sparse.eval row4666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck4666, Integer.Sparse.eval_collectBalanced, rawRowCheck4666]

theorem rawRowCheck4667 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7 = rawRow4667 := by decide +kernel

theorem rowCheck4667 : row4667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4667 := by decide +kernel

theorem rowEval4667 (x : Key → ℝ) : Integer.Sparse.eval row4667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck4667, Integer.Sparse.eval_collectBalanced, rawRowCheck4667]

theorem rawRowCheck4668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4668 := by decide +kernel

theorem rowCheck4668 : row4668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4668 := by decide +kernel

theorem rowEval4668 (x : Key → ℝ) : Integer.Sparse.eval row4668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4668, Integer.Sparse.eval_collectBalanced, rawRowCheck4668]

theorem rawRowCheck4669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4669 := by decide +kernel

theorem rowCheck4669 : row4669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4669 := by decide +kernel

theorem rowEval4669 (x : Key → ℝ) : Integer.Sparse.eval row4669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4669, Integer.Sparse.eval_collectBalanced, rawRowCheck4669]

theorem rawRowCheck4670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4670 := by decide +kernel

theorem rowCheck4670 : row4670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4670 := by decide +kernel

theorem rowEval4670 (x : Key → ℝ) : Integer.Sparse.eval row4670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4670, Integer.Sparse.eval_collectBalanced, rawRowCheck4670]

theorem rawRowCheck4671 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4671 := by decide +kernel

theorem rowCheck4671 : row4671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4671 := by decide +kernel

theorem rowEval4671 (x : Key → ℝ) : Integer.Sparse.eval row4671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4671, Integer.Sparse.eval_collectBalanced, rawRowCheck4671]

theorem rawRowCheck4672 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8 = rawRow4672 := by decide +kernel

theorem rowCheck4672 : row4672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4672 := by decide +kernel

theorem rowEval4672 (x : Key → ℝ) : Integer.Sparse.eval row4672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck4672, Integer.Sparse.eval_collectBalanced, rawRowCheck4672]

theorem rawRowCheck4673 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8 = rawRow4673 := by decide +kernel

theorem rowCheck4673 : row4673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4673 := by decide +kernel

theorem rowEval4673 (x : Key → ℝ) : Integer.Sparse.eval row4673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4673, Integer.Sparse.eval_collectBalanced, rawRowCheck4673]

theorem rawRowCheck4674 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8 = rawRow4674 := by decide +kernel

theorem rowCheck4674 : row4674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4674 := by decide +kernel

theorem rowEval4674 (x : Key → ℝ) : Integer.Sparse.eval row4674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4674, Integer.Sparse.eval_collectBalanced, rawRowCheck4674]

theorem rawRowCheck4675 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4675 := by decide +kernel

theorem rowCheck4675 : row4675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4675 := by decide +kernel

theorem rowEval4675 (x : Key → ℝ) : Integer.Sparse.eval row4675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4675, Integer.Sparse.eval_collectBalanced, rawRowCheck4675]

theorem rawRowCheck4676 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4676 := by decide +kernel

theorem rowCheck4676 : row4676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4676 := by decide +kernel

theorem rowEval4676 (x : Key → ℝ) : Integer.Sparse.eval row4676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4676, Integer.Sparse.eval_collectBalanced, rawRowCheck4676]

theorem rawRowCheck4677 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4677 := by decide +kernel

theorem rowCheck4677 : row4677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4677 := by decide +kernel

theorem rowEval4677 (x : Key → ℝ) : Integer.Sparse.eval row4677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4677, Integer.Sparse.eval_collectBalanced, rawRowCheck4677]

theorem rawRowCheck4678 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8 = rawRow4678 := by decide +kernel

theorem rowCheck4678 : row4678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4678 := by decide +kernel

theorem rowEval4678 (x : Key → ℝ) : Integer.Sparse.eval row4678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4678, Integer.Sparse.eval_collectBalanced, rawRowCheck4678]

theorem rawRowCheck4679 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8 = rawRow4679 := by decide +kernel

theorem rowCheck4679 : row4679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4679 := by decide +kernel

theorem rowEval4679 (x : Key → ℝ) : Integer.Sparse.eval row4679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4679, Integer.Sparse.eval_collectBalanced, rawRowCheck4679]

theorem rawRowCheck4680 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8 = rawRow4680 := by decide +kernel

theorem rowCheck4680 : row4680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4680 := by decide +kernel

theorem rowEval4680 (x : Key → ℝ) : Integer.Sparse.eval row4680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck4680, Integer.Sparse.eval_collectBalanced, rawRowCheck4680]

theorem rawRowCheck4681 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8 = rawRow4681 := by decide +kernel

theorem rowCheck4681 : row4681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4681 := by decide +kernel

theorem rowEval4681 (x : Key → ℝ) : Integer.Sparse.eval row4681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck4681, Integer.Sparse.eval_collectBalanced, rawRowCheck4681]

theorem rawRowCheck4682 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4682 := by decide +kernel

theorem rowCheck4682 : row4682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4682 := by decide +kernel

theorem rowEval4682 (x : Key → ℝ) : Integer.Sparse.eval row4682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4682, Integer.Sparse.eval_collectBalanced, rawRowCheck4682]

theorem rawRowCheck4683 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4683 := by decide +kernel

theorem rowCheck4683 : row4683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4683 := by decide +kernel

theorem rowEval4683 (x : Key → ℝ) : Integer.Sparse.eval row4683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4683, Integer.Sparse.eval_collectBalanced, rawRowCheck4683]

theorem rawRowCheck4684 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4684 := by decide +kernel

theorem rowCheck4684 : row4684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4684 := by decide +kernel

theorem rowEval4684 (x : Key → ℝ) : Integer.Sparse.eval row4684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4684, Integer.Sparse.eval_collectBalanced, rawRowCheck4684]

theorem rawRowCheck4685 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4685 := by decide +kernel

theorem rowCheck4685 : row4685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4685 := by decide +kernel

theorem rowEval4685 (x : Key → ℝ) : Integer.Sparse.eval row4685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4685, Integer.Sparse.eval_collectBalanced, rawRowCheck4685]

theorem rawRowCheck4686 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9 = rawRow4686 := by decide +kernel

theorem rowCheck4686 : row4686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4686 := by decide +kernel

theorem rowEval4686 (x : Key → ℝ) : Integer.Sparse.eval row4686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4686, Integer.Sparse.eval_collectBalanced, rawRowCheck4686]

theorem rawRowCheck4687 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9 = rawRow4687 := by decide +kernel

theorem rowCheck4687 : row4687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4687 := by decide +kernel

theorem rowEval4687 (x : Key → ℝ) : Integer.Sparse.eval row4687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4687, Integer.Sparse.eval_collectBalanced, rawRowCheck4687]

theorem rawRowCheck4688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9 = rawRow4688 := by decide +kernel

theorem rowCheck4688 : row4688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4688 := by decide +kernel

theorem rowEval4688 (x : Key → ℝ) : Integer.Sparse.eval row4688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4688, Integer.Sparse.eval_collectBalanced, rawRowCheck4688]

theorem rawRowCheck4689 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4689 := by decide +kernel

theorem rowCheck4689 : row4689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4689 := by decide +kernel

theorem rowEval4689 (x : Key → ℝ) : Integer.Sparse.eval row4689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4689, Integer.Sparse.eval_collectBalanced, rawRowCheck4689]

theorem rawRowCheck4690 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4690 := by decide +kernel

theorem rowCheck4690 : row4690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4690 := by decide +kernel

theorem rowEval4690 (x : Key → ℝ) : Integer.Sparse.eval row4690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4690, Integer.Sparse.eval_collectBalanced, rawRowCheck4690]

theorem rawRowCheck4691 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4691 := by decide +kernel

theorem rowCheck4691 : row4691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4691 := by decide +kernel

theorem rowEval4691 (x : Key → ℝ) : Integer.Sparse.eval row4691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4691, Integer.Sparse.eval_collectBalanced, rawRowCheck4691]

theorem rawRowCheck4692 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9 = rawRow4692 := by decide +kernel

theorem rowCheck4692 : row4692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4692 := by decide +kernel

theorem rowEval4692 (x : Key → ℝ) : Integer.Sparse.eval row4692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4692, Integer.Sparse.eval_collectBalanced, rawRowCheck4692]

theorem rawRowCheck4693 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9 = rawRow4693 := by decide +kernel

theorem rowCheck4693 : row4693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4693 := by decide +kernel

theorem rowEval4693 (x : Key → ℝ) : Integer.Sparse.eval row4693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4693, Integer.Sparse.eval_collectBalanced, rawRowCheck4693]

theorem rawRowCheck4694 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9 = rawRow4694 := by decide +kernel

theorem rowCheck4694 : row4694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4694 := by decide +kernel

theorem rowEval4694 (x : Key → ℝ) : Integer.Sparse.eval row4694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4694, Integer.Sparse.eval_collectBalanced, rawRowCheck4694]

theorem rawRowCheck4695 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9 = rawRow4695 := by decide +kernel

theorem rowCheck4695 : row4695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4695 := by decide +kernel

theorem rowEval4695 (x : Key → ℝ) : Integer.Sparse.eval row4695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4695, Integer.Sparse.eval_collectBalanced, rawRowCheck4695]

theorem rawRowCheck4696 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4696 := by decide +kernel

theorem rowCheck4696 : row4696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4696 := by decide +kernel

theorem rowEval4696 (x : Key → ℝ) : Integer.Sparse.eval row4696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4696, Integer.Sparse.eval_collectBalanced, rawRowCheck4696]

theorem rawRowCheck4697 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4697 := by decide +kernel

theorem rowCheck4697 : row4697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4697 := by decide +kernel

theorem rowEval4697 (x : Key → ℝ) : Integer.Sparse.eval row4697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4697, Integer.Sparse.eval_collectBalanced, rawRowCheck4697]

theorem rawRowCheck4698 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4698 := by decide +kernel

theorem rowCheck4698 : row4698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4698 := by decide +kernel

theorem rowEval4698 (x : Key → ℝ) : Integer.Sparse.eval row4698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4698, Integer.Sparse.eval_collectBalanced, rawRowCheck4698]

theorem rawRowCheck4699 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4699 := by decide +kernel

theorem rowCheck4699 : row4699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4699 := by decide +kernel

theorem rowEval4699 (x : Key → ℝ) : Integer.Sparse.eval row4699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4699, Integer.Sparse.eval_collectBalanced, rawRowCheck4699]

theorem rawRowCheck4700 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10 = rawRow4700 := by decide +kernel

theorem rowCheck4700 : row4700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4700 := by decide +kernel

theorem rowEval4700 (x : Key → ℝ) : Integer.Sparse.eval row4700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4700, Integer.Sparse.eval_collectBalanced, rawRowCheck4700]

theorem rawRowCheck4701 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10 = rawRow4701 := by decide +kernel

theorem rowCheck4701 : row4701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4701 := by decide +kernel

theorem rowEval4701 (x : Key → ℝ) : Integer.Sparse.eval row4701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4701, Integer.Sparse.eval_collectBalanced, rawRowCheck4701]

theorem rawRowCheck4702 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10 = rawRow4702 := by decide +kernel

theorem rowCheck4702 : row4702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4702 := by decide +kernel

theorem rowEval4702 (x : Key → ℝ) : Integer.Sparse.eval row4702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4702, Integer.Sparse.eval_collectBalanced, rawRowCheck4702]

theorem rawRowCheck4703 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4703 := by decide +kernel

theorem rowCheck4703 : row4703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4703 := by decide +kernel

theorem rowEval4703 (x : Key → ℝ) : Integer.Sparse.eval row4703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4703, Integer.Sparse.eval_collectBalanced, rawRowCheck4703]

theorem rawRowCheck4704 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4704 := by decide +kernel

theorem rowCheck4704 : row4704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4704 := by decide +kernel

theorem rowEval4704 (x : Key → ℝ) : Integer.Sparse.eval row4704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4704, Integer.Sparse.eval_collectBalanced, rawRowCheck4704]

theorem rawRowCheck4705 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4705 := by decide +kernel

theorem rowCheck4705 : row4705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4705 := by decide +kernel

theorem rowEval4705 (x : Key → ℝ) : Integer.Sparse.eval row4705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4705, Integer.Sparse.eval_collectBalanced, rawRowCheck4705]

theorem rawRowCheck4706 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10 = rawRow4706 := by decide +kernel

theorem rowCheck4706 : row4706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4706 := by decide +kernel

theorem rowEval4706 (x : Key → ℝ) : Integer.Sparse.eval row4706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4706, Integer.Sparse.eval_collectBalanced, rawRowCheck4706]

theorem rawRowCheck4707 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10 = rawRow4707 := by decide +kernel

theorem rowCheck4707 : row4707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4707 := by decide +kernel

theorem rowEval4707 (x : Key → ℝ) : Integer.Sparse.eval row4707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4707, Integer.Sparse.eval_collectBalanced, rawRowCheck4707]

theorem rawRowCheck4708 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10 = rawRow4708 := by decide +kernel

theorem rowCheck4708 : row4708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4708 := by decide +kernel

theorem rowEval4708 (x : Key → ℝ) : Integer.Sparse.eval row4708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4708, Integer.Sparse.eval_collectBalanced, rawRowCheck4708]

theorem rawRowCheck4709 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10 = rawRow4709 := by decide +kernel

theorem rowCheck4709 : row4709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4709 := by decide +kernel

theorem rowEval4709 (x : Key → ℝ) : Integer.Sparse.eval row4709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4709, Integer.Sparse.eval_collectBalanced, rawRowCheck4709]

theorem rawRowCheck4710 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4710 := by decide +kernel

theorem rowCheck4710 : row4710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4710 := by decide +kernel

theorem rowEval4710 (x : Key → ℝ) : Integer.Sparse.eval row4710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4710, Integer.Sparse.eval_collectBalanced, rawRowCheck4710]

theorem rawRowCheck4711 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4711 := by decide +kernel

theorem rowCheck4711 : row4711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4711 := by decide +kernel

theorem rowEval4711 (x : Key → ℝ) : Integer.Sparse.eval row4711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4711, Integer.Sparse.eval_collectBalanced, rawRowCheck4711]

theorem rawRowCheck4712 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4712 := by decide +kernel

theorem rowCheck4712 : row4712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4712 := by decide +kernel

theorem rowEval4712 (x : Key → ℝ) : Integer.Sparse.eval row4712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4712, Integer.Sparse.eval_collectBalanced, rawRowCheck4712]

theorem rawRowCheck4713 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4713 := by decide +kernel

theorem rowCheck4713 : row4713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4713 := by decide +kernel

theorem rowEval4713 (x : Key → ℝ) : Integer.Sparse.eval row4713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4713, Integer.Sparse.eval_collectBalanced, rawRowCheck4713]

theorem rawRowCheck4714 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11 = rawRow4714 := by decide +kernel

theorem rowCheck4714 : row4714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4714 := by decide +kernel

theorem rowEval4714 (x : Key → ℝ) : Integer.Sparse.eval row4714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4714, Integer.Sparse.eval_collectBalanced, rawRowCheck4714]

theorem rawRowCheck4715 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11 = rawRow4715 := by decide +kernel

theorem rowCheck4715 : row4715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4715 := by decide +kernel

theorem rowEval4715 (x : Key → ℝ) : Integer.Sparse.eval row4715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4715, Integer.Sparse.eval_collectBalanced, rawRowCheck4715]

theorem rawRowCheck4716 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11 = rawRow4716 := by decide +kernel

theorem rowCheck4716 : row4716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4716 := by decide +kernel

theorem rowEval4716 (x : Key → ℝ) : Integer.Sparse.eval row4716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4716, Integer.Sparse.eval_collectBalanced, rawRowCheck4716]

theorem rawRowCheck4717 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4717 := by decide +kernel

theorem rowCheck4717 : row4717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4717 := by decide +kernel

theorem rowEval4717 (x : Key → ℝ) : Integer.Sparse.eval row4717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4717, Integer.Sparse.eval_collectBalanced, rawRowCheck4717]

theorem rawRowCheck4718 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4718 := by decide +kernel

theorem rowCheck4718 : row4718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4718 := by decide +kernel

theorem rowEval4718 (x : Key → ℝ) : Integer.Sparse.eval row4718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4718, Integer.Sparse.eval_collectBalanced, rawRowCheck4718]

theorem rawRowCheck4719 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4719 := by decide +kernel

theorem rowCheck4719 : row4719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4719 := by decide +kernel

theorem rowEval4719 (x : Key → ℝ) : Integer.Sparse.eval row4719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4719, Integer.Sparse.eval_collectBalanced, rawRowCheck4719]

theorem rawRowCheck4720 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11 = rawRow4720 := by decide +kernel

theorem rowCheck4720 : row4720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4720 := by decide +kernel

theorem rowEval4720 (x : Key → ℝ) : Integer.Sparse.eval row4720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4720, Integer.Sparse.eval_collectBalanced, rawRowCheck4720]

theorem rawRowCheck4721 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11 = rawRow4721 := by decide +kernel

theorem rowCheck4721 : row4721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4721 := by decide +kernel

theorem rowEval4721 (x : Key → ℝ) : Integer.Sparse.eval row4721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4721, Integer.Sparse.eval_collectBalanced, rawRowCheck4721]

theorem rawRowCheck4722 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11 = rawRow4722 := by decide +kernel

theorem rowCheck4722 : row4722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4722 := by decide +kernel

theorem rowEval4722 (x : Key → ℝ) : Integer.Sparse.eval row4722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4722, Integer.Sparse.eval_collectBalanced, rawRowCheck4722]

theorem rawRowCheck4723 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11 = rawRow4723 := by decide +kernel

theorem rowCheck4723 : row4723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4723 := by decide +kernel

theorem rowEval4723 (x : Key → ℝ) : Integer.Sparse.eval row4723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4723, Integer.Sparse.eval_collectBalanced, rawRowCheck4723]

theorem rawRowCheck4724 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4724 := by decide +kernel

theorem rowCheck4724 : row4724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4724 := by decide +kernel

theorem rowEval4724 (x : Key → ℝ) : Integer.Sparse.eval row4724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4724, Integer.Sparse.eval_collectBalanced, rawRowCheck4724]

theorem rawRowCheck4725 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4725 := by decide +kernel

theorem rowCheck4725 : row4725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4725 := by decide +kernel

theorem rowEval4725 (x : Key → ℝ) : Integer.Sparse.eval row4725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4725, Integer.Sparse.eval_collectBalanced, rawRowCheck4725]

theorem rawRowCheck4726 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4726 := by decide +kernel

theorem rowCheck4726 : row4726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4726 := by decide +kernel

theorem rowEval4726 (x : Key → ℝ) : Integer.Sparse.eval row4726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4726, Integer.Sparse.eval_collectBalanced, rawRowCheck4726]

theorem rawRowCheck4727 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4727 := by decide +kernel

theorem rowCheck4727 : row4727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4727 := by decide +kernel

theorem rowEval4727 (x : Key → ℝ) : Integer.Sparse.eval row4727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4727, Integer.Sparse.eval_collectBalanced, rawRowCheck4727]

theorem rawRowCheck4728 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12 = rawRow4728 := by decide +kernel

theorem rowCheck4728 : row4728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4728 := by decide +kernel

theorem rowEval4728 (x : Key → ℝ) : Integer.Sparse.eval row4728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4728, Integer.Sparse.eval_collectBalanced, rawRowCheck4728]

theorem rawRowCheck4729 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12 = rawRow4729 := by decide +kernel

theorem rowCheck4729 : row4729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4729 := by decide +kernel

theorem rowEval4729 (x : Key → ℝ) : Integer.Sparse.eval row4729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4729, Integer.Sparse.eval_collectBalanced, rawRowCheck4729]

theorem rawRowCheck4730 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12 = rawRow4730 := by decide +kernel

theorem rowCheck4730 : row4730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4730 := by decide +kernel

theorem rowEval4730 (x : Key → ℝ) : Integer.Sparse.eval row4730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4730, Integer.Sparse.eval_collectBalanced, rawRowCheck4730]

theorem rawRowCheck4731 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4731 := by decide +kernel

theorem rowCheck4731 : row4731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4731 := by decide +kernel

theorem rowEval4731 (x : Key → ℝ) : Integer.Sparse.eval row4731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4731, Integer.Sparse.eval_collectBalanced, rawRowCheck4731]

theorem rawRowCheck4732 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4732 := by decide +kernel

theorem rowCheck4732 : row4732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4732 := by decide +kernel

theorem rowEval4732 (x : Key → ℝ) : Integer.Sparse.eval row4732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4732, Integer.Sparse.eval_collectBalanced, rawRowCheck4732]

theorem rawRowCheck4733 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4733 := by decide +kernel

theorem rowCheck4733 : row4733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4733 := by decide +kernel

theorem rowEval4733 (x : Key → ℝ) : Integer.Sparse.eval row4733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4733, Integer.Sparse.eval_collectBalanced, rawRowCheck4733]

theorem rawRowCheck4734 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12 = rawRow4734 := by decide +kernel

theorem rowCheck4734 : row4734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4734 := by decide +kernel

theorem rowEval4734 (x : Key → ℝ) : Integer.Sparse.eval row4734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4734, Integer.Sparse.eval_collectBalanced, rawRowCheck4734]

theorem rawRowCheck4735 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12 = rawRow4735 := by decide +kernel

theorem rowCheck4735 : row4735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4735 := by decide +kernel

theorem rowEval4735 (x : Key → ℝ) : Integer.Sparse.eval row4735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4735, Integer.Sparse.eval_collectBalanced, rawRowCheck4735]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck4736 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4736 := by decide +kernel

theorem rowCheck4736 : row4736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4736 := by decide +kernel

theorem rowEval4736 (x : Key → ℝ) : Integer.Sparse.eval row4736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4736, Integer.Sparse.eval_collectBalanced, rawRowCheck4736]

theorem rawRowCheck4737 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4737 := by decide +kernel

theorem rowCheck4737 : row4737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4737 := by decide +kernel

theorem rowEval4737 (x : Key → ℝ) : Integer.Sparse.eval row4737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4737, Integer.Sparse.eval_collectBalanced, rawRowCheck4737]

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

theorem rawRowCheck4752 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4752 := by decide +kernel

theorem rowCheck4752 : row4752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4752 := by decide +kernel

theorem rowEval4752 (x : Key → ℝ) : Integer.Sparse.eval row4752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4752, Integer.Sparse.eval_collectBalanced, rawRowCheck4752]

theorem rawRowCheck4753 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4753 := by decide +kernel

theorem rowCheck4753 : row4753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4753 := by decide +kernel

theorem rowEval4753 (x : Key → ℝ) : Integer.Sparse.eval row4753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4753, Integer.Sparse.eval_collectBalanced, rawRowCheck4753]

theorem rawRowCheck4754 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4754 := by decide +kernel

theorem rowCheck4754 : row4754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4754 := by decide +kernel

theorem rowEval4754 (x : Key → ℝ) : Integer.Sparse.eval row4754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4754, Integer.Sparse.eval_collectBalanced, rawRowCheck4754]

theorem rawRowCheck4755 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4755 := by decide +kernel

theorem rowCheck4755 : row4755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4755 := by decide +kernel

theorem rowEval4755 (x : Key → ℝ) : Integer.Sparse.eval row4755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4755, Integer.Sparse.eval_collectBalanced, rawRowCheck4755]

theorem rawRowCheck4756 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4756 := by decide +kernel

theorem rowCheck4756 : row4756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4756 := by decide +kernel

theorem rowEval4756 (x : Key → ℝ) : Integer.Sparse.eval row4756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4756, Integer.Sparse.eval_collectBalanced, rawRowCheck4756]

theorem rawRowCheck4757 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4757 := by decide +kernel

theorem rowCheck4757 : row4757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4757 := by decide +kernel

theorem rowEval4757 (x : Key → ℝ) : Integer.Sparse.eval row4757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4757, Integer.Sparse.eval_collectBalanced, rawRowCheck4757]

theorem rawRowCheck4758 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4758 := by decide +kernel

theorem rowCheck4758 : row4758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4758 := by decide +kernel

theorem rowEval4758 (x : Key → ℝ) : Integer.Sparse.eval row4758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4758, Integer.Sparse.eval_collectBalanced, rawRowCheck4758]

theorem rawRowCheck4759 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4759 := by decide +kernel

theorem rowCheck4759 : row4759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4759 := by decide +kernel

theorem rowEval4759 (x : Key → ℝ) : Integer.Sparse.eval row4759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4759, Integer.Sparse.eval_collectBalanced, rawRowCheck4759]

theorem rawRowCheck4760 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4760 := by decide +kernel

theorem rowCheck4760 : row4760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4760 := by decide +kernel

theorem rowEval4760 (x : Key → ℝ) : Integer.Sparse.eval row4760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4760, Integer.Sparse.eval_collectBalanced, rawRowCheck4760]

theorem rawRowCheck4761 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4761 := by decide +kernel

theorem rowCheck4761 : row4761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4761 := by decide +kernel

theorem rowEval4761 (x : Key → ℝ) : Integer.Sparse.eval row4761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4761, Integer.Sparse.eval_collectBalanced, rawRowCheck4761]

theorem rawRowCheck4762 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4762 := by decide +kernel

theorem rowCheck4762 : row4762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4762 := by decide +kernel

theorem rowEval4762 (x : Key → ℝ) : Integer.Sparse.eval row4762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4762, Integer.Sparse.eval_collectBalanced, rawRowCheck4762]

theorem rawRowCheck4763 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4763 := by decide +kernel

theorem rowCheck4763 : row4763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4763 := by decide +kernel

theorem rowEval4763 (x : Key → ℝ) : Integer.Sparse.eval row4763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4763, Integer.Sparse.eval_collectBalanced, rawRowCheck4763]

theorem rawRowCheck4764 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4764 := by decide +kernel

theorem rowCheck4764 : row4764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4764 := by decide +kernel

theorem rowEval4764 (x : Key → ℝ) : Integer.Sparse.eval row4764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4764, Integer.Sparse.eval_collectBalanced, rawRowCheck4764]

theorem rawRowCheck4765 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4765 := by decide +kernel

theorem rowCheck4765 : row4765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4765 := by decide +kernel

theorem rowEval4765 (x : Key → ℝ) : Integer.Sparse.eval row4765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4765, Integer.Sparse.eval_collectBalanced, rawRowCheck4765]

theorem rawRowCheck4766 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form15 = rawRow4766 := by decide +kernel

theorem rowCheck4766 : row4766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4766 := by decide +kernel

theorem rowEval4766 (x : Key → ℝ) : Integer.Sparse.eval row4766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4766, Integer.Sparse.eval_collectBalanced, rawRowCheck4766]

theorem rawRowCheck4767 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form15 = rawRow4767 := by decide +kernel

theorem rowCheck4767 : row4767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4767 := by decide +kernel

theorem rowEval4767 (x : Key → ℝ) : Integer.Sparse.eval row4767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4767, Integer.Sparse.eval_collectBalanced, rawRowCheck4767]

theorem rawRowCheck4768 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form15 = rawRow4768 := by decide +kernel

theorem rowCheck4768 : row4768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4768 := by decide +kernel

theorem rowEval4768 (x : Key → ℝ) : Integer.Sparse.eval row4768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4768, Integer.Sparse.eval_collectBalanced, rawRowCheck4768]

theorem rawRowCheck4769 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form15 = rawRow4769 := by decide +kernel

theorem rowCheck4769 : row4769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4769 := by decide +kernel

theorem rowEval4769 (x : Key → ℝ) : Integer.Sparse.eval row4769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4769, Integer.Sparse.eval_collectBalanced, rawRowCheck4769]

theorem rawRowCheck4770 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form15 = rawRow4770 := by decide +kernel

theorem rowCheck4770 : row4770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4770 := by decide +kernel

theorem rowEval4770 (x : Key → ℝ) : Integer.Sparse.eval row4770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4770, Integer.Sparse.eval_collectBalanced, rawRowCheck4770]

theorem rawRowCheck4771 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form15 = rawRow4771 := by decide +kernel

theorem rowCheck4771 : row4771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4771 := by decide +kernel

theorem rowEval4771 (x : Key → ℝ) : Integer.Sparse.eval row4771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4771, Integer.Sparse.eval_collectBalanced, rawRowCheck4771]

theorem rawRowCheck4772 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form15 = rawRow4772 := by decide +kernel

theorem rowCheck4772 : row4772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4772 := by decide +kernel

theorem rowEval4772 (x : Key → ℝ) : Integer.Sparse.eval row4772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4772, Integer.Sparse.eval_collectBalanced, rawRowCheck4772]

theorem rawRowCheck4773 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4773 := by decide +kernel

theorem rowCheck4773 : row4773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4773 := by decide +kernel

theorem rowEval4773 (x : Key → ℝ) : Integer.Sparse.eval row4773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4773, Integer.Sparse.eval_collectBalanced, rawRowCheck4773]

theorem rawRowCheck4774 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4774 := by decide +kernel

theorem rowCheck4774 : row4774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4774 := by decide +kernel

theorem rowEval4774 (x : Key → ℝ) : Integer.Sparse.eval row4774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4774, Integer.Sparse.eval_collectBalanced, rawRowCheck4774]

theorem rawRowCheck4775 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4775 := by decide +kernel

theorem rowCheck4775 : row4775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4775 := by decide +kernel

theorem rowEval4775 (x : Key → ℝ) : Integer.Sparse.eval row4775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4775, Integer.Sparse.eval_collectBalanced, rawRowCheck4775]

theorem rawRowCheck4776 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form15 = rawRow4776 := by decide +kernel

theorem rowCheck4776 : row4776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4776 := by decide +kernel

theorem rowEval4776 (x : Key → ℝ) : Integer.Sparse.eval row4776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4776, Integer.Sparse.eval_collectBalanced, rawRowCheck4776]

theorem rawRowCheck4777 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4777 := by decide +kernel

theorem rowCheck4777 : row4777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4777 := by decide +kernel

theorem rowEval4777 (x : Key → ℝ) : Integer.Sparse.eval row4777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4777, Integer.Sparse.eval_collectBalanced, rawRowCheck4777]

theorem rawRowCheck4778 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4778 := by decide +kernel

theorem rowCheck4778 : row4778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4778 := by decide +kernel

theorem rowEval4778 (x : Key → ℝ) : Integer.Sparse.eval row4778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4778, Integer.Sparse.eval_collectBalanced, rawRowCheck4778]

theorem rawRowCheck4779 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4779 := by decide +kernel

theorem rowCheck4779 : row4779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4779 := by decide +kernel

theorem rowEval4779 (x : Key → ℝ) : Integer.Sparse.eval row4779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4779, Integer.Sparse.eval_collectBalanced, rawRowCheck4779]

theorem rawRowCheck4780 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4780 := by decide +kernel

theorem rowCheck4780 : row4780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4780 := by decide +kernel

theorem rowEval4780 (x : Key → ℝ) : Integer.Sparse.eval row4780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4780, Integer.Sparse.eval_collectBalanced, rawRowCheck4780]

theorem rawRowCheck4781 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4781 := by decide +kernel

theorem rowCheck4781 : row4781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4781 := by decide +kernel

theorem rowEval4781 (x : Key → ℝ) : Integer.Sparse.eval row4781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4781, Integer.Sparse.eval_collectBalanced, rawRowCheck4781]

theorem rawRowCheck4782 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4782 := by decide +kernel

theorem rowCheck4782 : row4782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4782 := by decide +kernel

theorem rowEval4782 (x : Key → ℝ) : Integer.Sparse.eval row4782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4782, Integer.Sparse.eval_collectBalanced, rawRowCheck4782]

theorem rawRowCheck4783 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4783 := by decide +kernel

theorem rowCheck4783 : row4783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4783 := by decide +kernel

theorem rowEval4783 (x : Key → ℝ) : Integer.Sparse.eval row4783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4783, Integer.Sparse.eval_collectBalanced, rawRowCheck4783]

theorem rawRowCheck4784 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4784 := by decide +kernel

theorem rowCheck4784 : row4784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4784 := by decide +kernel

theorem rowEval4784 (x : Key → ℝ) : Integer.Sparse.eval row4784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4784, Integer.Sparse.eval_collectBalanced, rawRowCheck4784]

theorem rawRowCheck4785 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4785 := by decide +kernel

theorem rowCheck4785 : row4785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4785 := by decide +kernel

theorem rowEval4785 (x : Key → ℝ) : Integer.Sparse.eval row4785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4785, Integer.Sparse.eval_collectBalanced, rawRowCheck4785]

theorem rawRowCheck4786 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4786 := by decide +kernel

theorem rowCheck4786 : row4786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4786 := by decide +kernel

theorem rowEval4786 (x : Key → ℝ) : Integer.Sparse.eval row4786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4786, Integer.Sparse.eval_collectBalanced, rawRowCheck4786]

theorem rawRowCheck4787 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4787 := by decide +kernel

theorem rowCheck4787 : row4787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4787 := by decide +kernel

theorem rowEval4787 (x : Key → ℝ) : Integer.Sparse.eval row4787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4787, Integer.Sparse.eval_collectBalanced, rawRowCheck4787]

theorem rawRowCheck4788 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4788 := by decide +kernel

theorem rowCheck4788 : row4788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4788 := by decide +kernel

theorem rowEval4788 (x : Key → ℝ) : Integer.Sparse.eval row4788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4788, Integer.Sparse.eval_collectBalanced, rawRowCheck4788]

theorem rawRowCheck4789 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4789 := by decide +kernel

theorem rowCheck4789 : row4789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4789 := by decide +kernel

theorem rowEval4789 (x : Key → ℝ) : Integer.Sparse.eval row4789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4789, Integer.Sparse.eval_collectBalanced, rawRowCheck4789]

theorem rawRowCheck4790 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4790 := by decide +kernel

theorem rowCheck4790 : row4790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4790 := by decide +kernel

theorem rowEval4790 (x : Key → ℝ) : Integer.Sparse.eval row4790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4790, Integer.Sparse.eval_collectBalanced, rawRowCheck4790]

theorem rawRowCheck4791 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4791 := by decide +kernel

theorem rowCheck4791 : row4791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4791 := by decide +kernel

theorem rowEval4791 (x : Key → ℝ) : Integer.Sparse.eval row4791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4791, Integer.Sparse.eval_collectBalanced, rawRowCheck4791]

theorem rawRowCheck4792 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4792 := by decide +kernel

theorem rowCheck4792 : row4792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4792 := by decide +kernel

theorem rowEval4792 (x : Key → ℝ) : Integer.Sparse.eval row4792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4792, Integer.Sparse.eval_collectBalanced, rawRowCheck4792]

theorem rawRowCheck4793 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4793 := by decide +kernel

theorem rowCheck4793 : row4793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4793 := by decide +kernel

theorem rowEval4793 (x : Key → ℝ) : Integer.Sparse.eval row4793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4793, Integer.Sparse.eval_collectBalanced, rawRowCheck4793]

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

theorem rawRowCheck4808 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form18 = rawRow4808 := by decide +kernel

theorem rowCheck4808 : row4808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4808 := by decide +kernel

theorem rowEval4808 (x : Key → ℝ) : Integer.Sparse.eval row4808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4808, Integer.Sparse.eval_collectBalanced, rawRowCheck4808]

theorem rawRowCheck4809 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form18 = rawRow4809 := by decide +kernel

theorem rowCheck4809 : row4809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4809 := by decide +kernel

theorem rowEval4809 (x : Key → ℝ) : Integer.Sparse.eval row4809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4809, Integer.Sparse.eval_collectBalanced, rawRowCheck4809]

theorem rawRowCheck4810 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form18 = rawRow4810 := by decide +kernel

theorem rowCheck4810 : row4810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4810 := by decide +kernel

theorem rowEval4810 (x : Key → ℝ) : Integer.Sparse.eval row4810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4810, Integer.Sparse.eval_collectBalanced, rawRowCheck4810]

theorem rawRowCheck4811 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form18 = rawRow4811 := by decide +kernel

theorem rowCheck4811 : row4811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4811 := by decide +kernel

theorem rowEval4811 (x : Key → ℝ) : Integer.Sparse.eval row4811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4811, Integer.Sparse.eval_collectBalanced, rawRowCheck4811]

theorem rawRowCheck4812 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form18 = rawRow4812 := by decide +kernel

theorem rowCheck4812 : row4812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4812 := by decide +kernel

theorem rowEval4812 (x : Key → ℝ) : Integer.Sparse.eval row4812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4812, Integer.Sparse.eval_collectBalanced, rawRowCheck4812]

theorem rawRowCheck4813 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form18 = rawRow4813 := by decide +kernel

theorem rowCheck4813 : row4813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4813 := by decide +kernel

theorem rowEval4813 (x : Key → ℝ) : Integer.Sparse.eval row4813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4813, Integer.Sparse.eval_collectBalanced, rawRowCheck4813]

theorem rawRowCheck4814 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form18 = rawRow4814 := by decide +kernel

theorem rowCheck4814 : row4814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4814 := by decide +kernel

theorem rowEval4814 (x : Key → ℝ) : Integer.Sparse.eval row4814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4814, Integer.Sparse.eval_collectBalanced, rawRowCheck4814]

theorem rawRowCheck4815 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4815 := by decide +kernel

theorem rowCheck4815 : row4815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4815 := by decide +kernel

theorem rowEval4815 (x : Key → ℝ) : Integer.Sparse.eval row4815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4815, Integer.Sparse.eval_collectBalanced, rawRowCheck4815]

theorem rawRowCheck4816 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4816 := by decide +kernel

theorem rowCheck4816 : row4816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4816 := by decide +kernel

theorem rowEval4816 (x : Key → ℝ) : Integer.Sparse.eval row4816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4816, Integer.Sparse.eval_collectBalanced, rawRowCheck4816]

theorem rawRowCheck4817 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4817 := by decide +kernel

theorem rowCheck4817 : row4817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4817 := by decide +kernel

theorem rowEval4817 (x : Key → ℝ) : Integer.Sparse.eval row4817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4817, Integer.Sparse.eval_collectBalanced, rawRowCheck4817]

theorem rawRowCheck4818 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form18 = rawRow4818 := by decide +kernel

theorem rowCheck4818 : row4818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4818 := by decide +kernel

theorem rowEval4818 (x : Key → ℝ) : Integer.Sparse.eval row4818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4818, Integer.Sparse.eval_collectBalanced, rawRowCheck4818]

theorem rawRowCheck4819 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4819 := by decide +kernel

theorem rowCheck4819 : row4819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4819 := by decide +kernel

theorem rowEval4819 (x : Key → ℝ) : Integer.Sparse.eval row4819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4819, Integer.Sparse.eval_collectBalanced, rawRowCheck4819]

theorem rawRowCheck4820 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4820 := by decide +kernel

theorem rowCheck4820 : row4820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4820 := by decide +kernel

theorem rowEval4820 (x : Key → ℝ) : Integer.Sparse.eval row4820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4820, Integer.Sparse.eval_collectBalanced, rawRowCheck4820]

theorem rawRowCheck4821 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4821 := by decide +kernel

theorem rowCheck4821 : row4821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4821 := by decide +kernel

theorem rowEval4821 (x : Key → ℝ) : Integer.Sparse.eval row4821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4821, Integer.Sparse.eval_collectBalanced, rawRowCheck4821]

theorem rawRowCheck4822 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form19 = rawRow4822 := by decide +kernel

theorem rowCheck4822 : row4822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4822 := by decide +kernel

theorem rowEval4822 (x : Key → ℝ) : Integer.Sparse.eval row4822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck4822, Integer.Sparse.eval_collectBalanced, rawRowCheck4822]

theorem rawRowCheck4823 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form19 = rawRow4823 := by decide +kernel

theorem rowCheck4823 : row4823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4823 := by decide +kernel

theorem rowEval4823 (x : Key → ℝ) : Integer.Sparse.eval row4823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4823, Integer.Sparse.eval_collectBalanced, rawRowCheck4823]

theorem rawRowCheck4824 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form19 = rawRow4824 := by decide +kernel

theorem rowCheck4824 : row4824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4824 := by decide +kernel

theorem rowEval4824 (x : Key → ℝ) : Integer.Sparse.eval row4824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4824, Integer.Sparse.eval_collectBalanced, rawRowCheck4824]

theorem rawRowCheck4825 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form19 = rawRow4825 := by decide +kernel

theorem rowCheck4825 : row4825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4825 := by decide +kernel

theorem rowEval4825 (x : Key → ℝ) : Integer.Sparse.eval row4825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4825, Integer.Sparse.eval_collectBalanced, rawRowCheck4825]

theorem rawRowCheck4826 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form19 = rawRow4826 := by decide +kernel

theorem rowCheck4826 : row4826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4826 := by decide +kernel

theorem rowEval4826 (x : Key → ℝ) : Integer.Sparse.eval row4826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck4826, Integer.Sparse.eval_collectBalanced, rawRowCheck4826]

theorem rawRowCheck4827 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form19 = rawRow4827 := by decide +kernel

theorem rowCheck4827 : row4827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4827 := by decide +kernel

theorem rowEval4827 (x : Key → ℝ) : Integer.Sparse.eval row4827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4827, Integer.Sparse.eval_collectBalanced, rawRowCheck4827]

theorem rawRowCheck4828 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form19 = rawRow4828 := by decide +kernel

theorem rowCheck4828 : row4828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4828 := by decide +kernel

theorem rowEval4828 (x : Key → ℝ) : Integer.Sparse.eval row4828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4828, Integer.Sparse.eval_collectBalanced, rawRowCheck4828]

theorem rawRowCheck4829 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form19 = rawRow4829 := by decide +kernel

theorem rowCheck4829 : row4829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4829 := by decide +kernel

theorem rowEval4829 (x : Key → ℝ) : Integer.Sparse.eval row4829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4829, Integer.Sparse.eval_collectBalanced, rawRowCheck4829]

theorem rawRowCheck4830 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form19 = rawRow4830 := by decide +kernel

theorem rowCheck4830 : row4830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4830 := by decide +kernel

theorem rowEval4830 (x : Key → ℝ) : Integer.Sparse.eval row4830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4830, Integer.Sparse.eval_collectBalanced, rawRowCheck4830]

theorem rawRowCheck4831 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form19 = rawRow4831 := by decide +kernel

theorem rowCheck4831 : row4831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4831 := by decide +kernel

theorem rowEval4831 (x : Key → ℝ) : Integer.Sparse.eval row4831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck4831, Integer.Sparse.eval_collectBalanced, rawRowCheck4831]

theorem rawRowCheck4832 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form19 = rawRow4832 := by decide +kernel

theorem rowCheck4832 : row4832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4832 := by decide +kernel

theorem rowEval4832 (x : Key → ℝ) : Integer.Sparse.eval row4832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4832, Integer.Sparse.eval_collectBalanced, rawRowCheck4832]

theorem rawRowCheck4833 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form19 = rawRow4833 := by decide +kernel

theorem rowCheck4833 : row4833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4833 := by decide +kernel

theorem rowEval4833 (x : Key → ℝ) : Integer.Sparse.eval row4833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4833, Integer.Sparse.eval_collectBalanced, rawRowCheck4833]

theorem rawRowCheck4834 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form19 = rawRow4834 := by decide +kernel

theorem rowCheck4834 : row4834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4834 := by decide +kernel

theorem rowEval4834 (x : Key → ℝ) : Integer.Sparse.eval row4834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4834, Integer.Sparse.eval_collectBalanced, rawRowCheck4834]

theorem rawRowCheck4835 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form19 = rawRow4835 := by decide +kernel

theorem rowCheck4835 : row4835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4835 := by decide +kernel

theorem rowEval4835 (x : Key → ℝ) : Integer.Sparse.eval row4835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck4835, Integer.Sparse.eval_collectBalanced, rawRowCheck4835]

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

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4570 x
  · exact rowEval4571 x
  · exact rowEval4572 x
  · exact rowEval4573 x
  · exact rowEval4574 x
  · exact rowEval4575 x
  · exact rowEval4576 x
  · exact rowEval4577 x
  · exact rowEval4578 x
  · exact rowEval4579 x
  · exact rowEval4580 x
  · exact rowEval4581 x
  · exact rowEval4582 x
  · exact rowEval4583 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4598 x
  · exact rowEval4599 x
  · exact rowEval4600 x
  · exact rowEval4601 x
  · exact rowEval4602 x
  · exact rowEval4603 x
  · exact rowEval4604 x
  · exact rowEval4605 x
  · exact rowEval4606 x
  · exact rowEval4607 x
  · exact rowEval4608 x
  · exact rowEval4609 x
  · exact rowEval4610 x
  · exact rowEval4611 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4612 x
  · exact rowEval4613 x
  · exact rowEval4614 x
  · exact rowEval4615 x
  · exact rowEval4616 x
  · exact rowEval4617 x
  · exact rowEval4618 x
  · exact rowEval4619 x
  · exact rowEval4620 x
  · exact rowEval4621 x
  · exact rowEval4622 x
  · exact rowEval4623 x
  · exact rowEval4624 x
  · exact rowEval4625 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval4626 x
  · exact rowEval4627 x
  · exact rowEval4628 x
  · exact rowEval4629 x
  · exact rowEval4630 x
  · exact rowEval4631 x
  · exact rowEval4632 x
  · exact rowEval4633 x
  · exact rowEval4634 x
  · exact rowEval4635 x
  · exact rowEval4636 x
  · exact rowEval4637 x
  · exact rowEval4638 x
  · exact rowEval4639 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4640 x
  · exact rowEval4641 x
  · exact rowEval4642 x
  · exact rowEval4643 x
  · exact rowEval4644 x
  · exact rowEval4645 x
  · exact rowEval4646 x
  · exact rowEval4647 x
  · exact rowEval4648 x
  · exact rowEval4649 x
  · exact rowEval4650 x
  · exact rowEval4651 x
  · exact rowEval4652 x
  · exact rowEval4653 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4654 x
  · exact rowEval4655 x
  · exact rowEval4656 x
  · exact rowEval4657 x
  · exact rowEval4658 x
  · exact rowEval4659 x
  · exact rowEval4660 x
  · exact rowEval4661 x
  · exact rowEval4662 x
  · exact rowEval4663 x
  · exact rowEval4664 x
  · exact rowEval4665 x
  · exact rowEval4666 x
  · exact rowEval4667 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4668 x
  · exact rowEval4669 x
  · exact rowEval4670 x
  · exact rowEval4671 x
  · exact rowEval4672 x
  · exact rowEval4673 x
  · exact rowEval4674 x
  · exact rowEval4675 x
  · exact rowEval4676 x
  · exact rowEval4677 x
  · exact rowEval4678 x
  · exact rowEval4679 x
  · exact rowEval4680 x
  · exact rowEval4681 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval4682 x
  · exact rowEval4683 x
  · exact rowEval4684 x
  · exact rowEval4685 x
  · exact rowEval4686 x
  · exact rowEval4687 x
  · exact rowEval4688 x
  · exact rowEval4689 x
  · exact rowEval4690 x
  · exact rowEval4691 x
  · exact rowEval4692 x
  · exact rowEval4693 x
  · exact rowEval4694 x
  · exact rowEval4695 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4696 x
  · exact rowEval4697 x
  · exact rowEval4698 x
  · exact rowEval4699 x
  · exact rowEval4700 x
  · exact rowEval4701 x
  · exact rowEval4702 x
  · exact rowEval4703 x
  · exact rowEval4704 x
  · exact rowEval4705 x
  · exact rowEval4706 x
  · exact rowEval4707 x
  · exact rowEval4708 x
  · exact rowEval4709 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4710 x
  · exact rowEval4711 x
  · exact rowEval4712 x
  · exact rowEval4713 x
  · exact rowEval4714 x
  · exact rowEval4715 x
  · exact rowEval4716 x
  · exact rowEval4717 x
  · exact rowEval4718 x
  · exact rowEval4719 x
  · exact rowEval4720 x
  · exact rowEval4721 x
  · exact rowEval4722 x
  · exact rowEval4723 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4724 x
  · exact rowEval4725 x
  · exact rowEval4726 x
  · exact rowEval4727 x
  · exact rowEval4728 x
  · exact rowEval4729 x
  · exact rowEval4730 x
  · exact rowEval4731 x
  · exact rowEval4732 x
  · exact rowEval4733 x
  · exact rowEval4734 x
  · exact rowEval4735 x
  · exact rowEval4736 x
  · exact rowEval4737 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

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

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval4752 x
  · exact rowEval4753 x
  · exact rowEval4754 x
  · exact rowEval4755 x
  · exact rowEval4756 x
  · exact rowEval4757 x
  · exact rowEval4758 x
  · exact rowEval4759 x
  · exact rowEval4760 x
  · exact rowEval4761 x
  · exact rowEval4762 x
  · exact rowEval4763 x
  · exact rowEval4764 x
  · exact rowEval4765 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval4766 x
  · exact rowEval4767 x
  · exact rowEval4768 x
  · exact rowEval4769 x
  · exact rowEval4770 x
  · exact rowEval4771 x
  · exact rowEval4772 x
  · exact rowEval4773 x
  · exact rowEval4774 x
  · exact rowEval4775 x
  · exact rowEval4776 x
  · exact rowEval4777 x
  · exact rowEval4778 x
  · exact rowEval4779 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval4780 x
  · exact rowEval4781 x
  · exact rowEval4782 x
  · exact rowEval4783 x
  · exact rowEval4784 x
  · exact rowEval4785 x
  · exact rowEval4786 x
  · exact rowEval4787 x
  · exact rowEval4788 x
  · exact rowEval4789 x
  · exact rowEval4790 x
  · exact rowEval4791 x
  · exact rowEval4792 x
  · exact rowEval4793 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

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

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form18) x := by
  fin_cases k
  · exact rowEval4808 x
  · exact rowEval4809 x
  · exact rowEval4810 x
  · exact rowEval4811 x
  · exact rowEval4812 x
  · exact rowEval4813 x
  · exact rowEval4814 x
  · exact rowEval4815 x
  · exact rowEval4816 x
  · exact rowEval4817 x
  · exact rowEval4818 x
  · exact rowEval4819 x
  · exact rowEval4820 x
  · exact rowEval4821 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form19) x := by
  fin_cases k
  · exact rowEval4822 x
  · exact rowEval4823 x
  · exact rowEval4824 x
  · exact rowEval4825 x
  · exact rowEval4826 x
  · exact rowEval4827 x
  · exact rowEval4828 x
  · exact rowEval4829 x
  · exact rowEval4830 x
  · exact rowEval4831 x
  · exact rowEval4832 x
  · exact rowEval4833 x
  · exact rowEval4834 x
  · exact rowEval4835 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

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

theorem entryEvalRow19_e_oai (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 19 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 19).mixedGram (GramFunctions.Block1.forms j) B := by
  fin_cases j
  · exact entryEval19_0 B hB
  · exact entryEval19_1 B hB
  · exact entryEval19_2_e B hB
  · exact entryEval19_3 B hB
  · exact entryEval19_4 B hB
  · exact entryEval19_5 B hB
  · exact entryEval19_6 B hB
  · exact entryEval19_7 B hB
  · exact entryEval19_8 B hB
  · exact entryEval19_9 B hB
  · exact entryEval19_10 B hB
  · exact entryEval19_11 B hB
  · exact entryEval19_12 B hB
  · exact entryEval19_13 B hB
  · exact entryEval19_14 B hB
  · exact entryEval19_15 B hB
  · exact entryEval19_16 B hB
  · exact entryEval19_17 B hB
  · exact entryEval19_18 B hB
  · exact entryEval19_19 B hB
  · exact (entryEval20_19_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e_oai := @OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e_oai
