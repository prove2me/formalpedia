-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:23:54.774892+00:00
-- url     : https://prove2.me/submissions/9d9e6701-e70e-46f5-9432-798cf9beae65

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18429 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18429 := by decide +kernel

theorem rowCheck18429 : row18429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18429 := by decide +kernel

theorem rowEval18429 (x : Key → ℝ) : Integer.Sparse.eval row18429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18429, Integer.Sparse.eval_collectBalanced, rawRowCheck18429]

theorem rawRowCheck18430 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18430 := by decide +kernel

theorem rowCheck18430 : row18430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18430 := by decide +kernel

theorem rowEval18430 (x : Key → ℝ) : Integer.Sparse.eval row18430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18430, Integer.Sparse.eval_collectBalanced, rawRowCheck18430]

theorem rawRowCheck18431 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18431 := by decide +kernel

theorem rowCheck18431 : row18431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18431 := by decide +kernel

theorem rowEval18431 (x : Key → ℝ) : Integer.Sparse.eval row18431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18431, Integer.Sparse.eval_collectBalanced, rawRowCheck18431]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18432 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18432 := by decide +kernel

theorem rowCheck18432 : row18432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18432 := by decide +kernel

theorem rowEval18432 (x : Key → ℝ) : Integer.Sparse.eval row18432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18432, Integer.Sparse.eval_collectBalanced, rawRowCheck18432]

theorem rawRowCheck18433 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18433 := by decide +kernel

theorem rowCheck18433 : row18433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18433 := by decide +kernel

theorem rowEval18433 (x : Key → ℝ) : Integer.Sparse.eval row18433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18433, Integer.Sparse.eval_collectBalanced, rawRowCheck18433]

theorem rawRowCheck18434 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18434 := by decide +kernel

theorem rowCheck18434 : row18434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18434 := by decide +kernel

theorem rowEval18434 (x : Key → ℝ) : Integer.Sparse.eval row18434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18434, Integer.Sparse.eval_collectBalanced, rawRowCheck18434]

theorem rawRowCheck18435 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18435 := by decide +kernel

theorem rowCheck18435 : row18435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18435 := by decide +kernel

theorem rowEval18435 (x : Key → ℝ) : Integer.Sparse.eval row18435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18435, Integer.Sparse.eval_collectBalanced, rawRowCheck18435]

theorem rawRowCheck18436 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0 = rawRow18436 := by decide +kernel

theorem rowCheck18436 : row18436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18436 := by decide +kernel

theorem rowEval18436 (x : Key → ℝ) : Integer.Sparse.eval row18436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18436, Integer.Sparse.eval_collectBalanced, rawRowCheck18436]

theorem rawRowCheck18437 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0 = rawRow18437 := by decide +kernel

theorem rowCheck18437 : row18437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18437 := by decide +kernel

theorem rowEval18437 (x : Key → ℝ) : Integer.Sparse.eval row18437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18437, Integer.Sparse.eval_collectBalanced, rawRowCheck18437]

theorem rawRowCheck18438 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0 = rawRow18438 := by decide +kernel

theorem rowCheck18438 : row18438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18438 := by decide +kernel

theorem rowEval18438 (x : Key → ℝ) : Integer.Sparse.eval row18438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18438, Integer.Sparse.eval_collectBalanced, rawRowCheck18438]

theorem rawRowCheck18439 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0 = rawRow18439 := by decide +kernel

theorem rowCheck18439 : row18439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18439 := by decide +kernel

theorem rowEval18439 (x : Key → ℝ) : Integer.Sparse.eval row18439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18439, Integer.Sparse.eval_collectBalanced, rawRowCheck18439]

theorem rawRowCheck18440 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0 = rawRow18440 := by decide +kernel

theorem rowCheck18440 : row18440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18440 := by decide +kernel

theorem rowEval18440 (x : Key → ℝ) : Integer.Sparse.eval row18440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18440, Integer.Sparse.eval_collectBalanced, rawRowCheck18440]

theorem rawRowCheck18441 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0 = rawRow18441 := by decide +kernel

theorem rowCheck18441 : row18441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18441 := by decide +kernel

theorem rowEval18441 (x : Key → ℝ) : Integer.Sparse.eval row18441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18441, Integer.Sparse.eval_collectBalanced, rawRowCheck18441]

theorem rawRowCheck18442 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18442 := by decide +kernel

theorem rowCheck18442 : row18442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18442 := by decide +kernel

theorem rowEval18442 (x : Key → ℝ) : Integer.Sparse.eval row18442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18442, Integer.Sparse.eval_collectBalanced, rawRowCheck18442]

theorem rawRowCheck18443 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18443 := by decide +kernel

theorem rowCheck18443 : row18443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18443 := by decide +kernel

theorem rowEval18443 (x : Key → ℝ) : Integer.Sparse.eval row18443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18443, Integer.Sparse.eval_collectBalanced, rawRowCheck18443]

theorem rawRowCheck18444 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18444 := by decide +kernel

theorem rowCheck18444 : row18444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18444 := by decide +kernel

theorem rowEval18444 (x : Key → ℝ) : Integer.Sparse.eval row18444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18444, Integer.Sparse.eval_collectBalanced, rawRowCheck18444]

theorem rawRowCheck18445 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18445 := by decide +kernel

theorem rowCheck18445 : row18445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18445 := by decide +kernel

theorem rowEval18445 (x : Key → ℝ) : Integer.Sparse.eval row18445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18445, Integer.Sparse.eval_collectBalanced, rawRowCheck18445]

theorem rawRowCheck18446 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18446 := by decide +kernel

theorem rowCheck18446 : row18446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18446 := by decide +kernel

theorem rowEval18446 (x : Key → ℝ) : Integer.Sparse.eval row18446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18446, Integer.Sparse.eval_collectBalanced, rawRowCheck18446]

theorem rawRowCheck18447 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18447 := by decide +kernel

theorem rowCheck18447 : row18447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18447 := by decide +kernel

theorem rowEval18447 (x : Key → ℝ) : Integer.Sparse.eval row18447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18447, Integer.Sparse.eval_collectBalanced, rawRowCheck18447]

theorem rawRowCheck18448 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18448 := by decide +kernel

theorem rowCheck18448 : row18448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18448 := by decide +kernel

theorem rowEval18448 (x : Key → ℝ) : Integer.Sparse.eval row18448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18448, Integer.Sparse.eval_collectBalanced, rawRowCheck18448]

theorem rawRowCheck18449 : GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18449 := by decide +kernel

theorem rowCheck18449 : row18449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18449 := by decide +kernel

theorem rowEval18449 (x : Key → ℝ) : Integer.Sparse.eval row18449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -3, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18449, Integer.Sparse.eval_collectBalanced, rawRowCheck18449]

theorem rawRowCheck18450 : GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18450 := by decide +kernel

theorem rowCheck18450 : row18450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18450 := by decide +kernel

theorem rowEval18450 (x : Key → ℝ) : Integer.Sparse.eval row18450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18450, Integer.Sparse.eval_collectBalanced, rawRowCheck18450]

theorem rawRowCheck18451 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18451 := by decide +kernel

theorem rowCheck18451 : row18451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18451 := by decide +kernel

theorem rowEval18451 (x : Key → ℝ) : Integer.Sparse.eval row18451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18451, Integer.Sparse.eval_collectBalanced, rawRowCheck18451]

theorem rawRowCheck18452 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18452 := by decide +kernel

theorem rowCheck18452 : row18452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18452 := by decide +kernel

theorem rowEval18452 (x : Key → ℝ) : Integer.Sparse.eval row18452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18452, Integer.Sparse.eval_collectBalanced, rawRowCheck18452]

theorem rawRowCheck18453 : GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18453 := by decide +kernel

theorem rowCheck18453 : row18453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18453 := by decide +kernel

theorem rowEval18453 (x : Key → ℝ) : Integer.Sparse.eval row18453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18453, Integer.Sparse.eval_collectBalanced, rawRowCheck18453]

theorem rawRowCheck18459 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18459 := by decide +kernel

theorem rowCheck18459 : row18459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18459 := by decide +kernel

theorem rowEval18459 (x : Key → ℝ) : Integer.Sparse.eval row18459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18459, Integer.Sparse.eval_collectBalanced, rawRowCheck18459]

theorem rawRowCheck18460 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18460 := by decide +kernel

theorem rowCheck18460 : row18460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18460 := by decide +kernel

theorem rowEval18460 (x : Key → ℝ) : Integer.Sparse.eval row18460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18460, Integer.Sparse.eval_collectBalanced, rawRowCheck18460]

theorem rawRowCheck18461 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18461 := by decide +kernel

theorem rowCheck18461 : row18461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18461 := by decide +kernel

theorem rowEval18461 (x : Key → ℝ) : Integer.Sparse.eval row18461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18461, Integer.Sparse.eval_collectBalanced, rawRowCheck18461]

theorem rawRowCheck18462 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow18462 := by decide +kernel

theorem rowCheck18462 : row18462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18462 := by decide +kernel

theorem rowEval18462 (x : Key → ℝ) : Integer.Sparse.eval row18462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18462, Integer.Sparse.eval_collectBalanced, rawRowCheck18462]

theorem rawRowCheck18463 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow18463 := by decide +kernel

theorem rowCheck18463 : row18463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18463 := by decide +kernel

theorem rowEval18463 (x : Key → ℝ) : Integer.Sparse.eval row18463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18463, Integer.Sparse.eval_collectBalanced, rawRowCheck18463]

theorem rawRowCheck18464 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow18464 := by decide +kernel

theorem rowCheck18464 : row18464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18464 := by decide +kernel

theorem rowEval18464 (x : Key → ℝ) : Integer.Sparse.eval row18464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18464, Integer.Sparse.eval_collectBalanced, rawRowCheck18464]

theorem rawRowCheck18465 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow18465 := by decide +kernel

theorem rowCheck18465 : row18465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18465 := by decide +kernel

theorem rowEval18465 (x : Key → ℝ) : Integer.Sparse.eval row18465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18465, Integer.Sparse.eval_collectBalanced, rawRowCheck18465]

theorem rawRowCheck18466 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow18466 := by decide +kernel

theorem rowCheck18466 : row18466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18466 := by decide +kernel

theorem rowEval18466 (x : Key → ℝ) : Integer.Sparse.eval row18466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18466, Integer.Sparse.eval_collectBalanced, rawRowCheck18466]

theorem rawRowCheck18467 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow18467 := by decide +kernel

theorem rowCheck18467 : row18467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18467 := by decide +kernel

theorem rowEval18467 (x : Key → ℝ) : Integer.Sparse.eval row18467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18467, Integer.Sparse.eval_collectBalanced, rawRowCheck18467]

theorem rawRowCheck18468 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18468 := by decide +kernel

theorem rowCheck18468 : row18468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18468 := by decide +kernel

theorem rowEval18468 (x : Key → ℝ) : Integer.Sparse.eval row18468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18468, Integer.Sparse.eval_collectBalanced, rawRowCheck18468]

theorem rawRowCheck18469 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18469 := by decide +kernel

theorem rowCheck18469 : row18469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18469 := by decide +kernel

theorem rowEval18469 (x : Key → ℝ) : Integer.Sparse.eval row18469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18469, Integer.Sparse.eval_collectBalanced, rawRowCheck18469]

theorem rawRowCheck18470 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18470 := by decide +kernel

theorem rowCheck18470 : row18470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18470 := by decide +kernel

theorem rowEval18470 (x : Key → ℝ) : Integer.Sparse.eval row18470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18470, Integer.Sparse.eval_collectBalanced, rawRowCheck18470]

theorem rawRowCheck18471 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18471 := by decide +kernel

theorem rowCheck18471 : row18471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18471 := by decide +kernel

theorem rowEval18471 (x : Key → ℝ) : Integer.Sparse.eval row18471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18471, Integer.Sparse.eval_collectBalanced, rawRowCheck18471]

theorem rawRowCheck18472 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18472 := by decide +kernel

theorem rowCheck18472 : row18472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18472 := by decide +kernel

theorem rowEval18472 (x : Key → ℝ) : Integer.Sparse.eval row18472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18472, Integer.Sparse.eval_collectBalanced, rawRowCheck18472]

theorem rawRowCheck18473 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18473 := by decide +kernel

theorem rowCheck18473 : row18473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18473 := by decide +kernel

theorem rowEval18473 (x : Key → ℝ) : Integer.Sparse.eval row18473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18473, Integer.Sparse.eval_collectBalanced, rawRowCheck18473]

theorem rawRowCheck18474 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow18474 := by decide +kernel

theorem rowCheck18474 : row18474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18474 := by decide +kernel

theorem rowEval18474 (x : Key → ℝ) : Integer.Sparse.eval row18474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18474, Integer.Sparse.eval_collectBalanced, rawRowCheck18474]

theorem rawRowCheck18475 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow18475 := by decide +kernel

theorem rowCheck18475 : row18475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18475 := by decide +kernel

theorem rowEval18475 (x : Key → ℝ) : Integer.Sparse.eval row18475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18475, Integer.Sparse.eval_collectBalanced, rawRowCheck18475]

theorem rawRowCheck18476 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow18476 := by decide +kernel

theorem rowCheck18476 : row18476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18476 := by decide +kernel

theorem rowEval18476 (x : Key → ℝ) : Integer.Sparse.eval row18476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18476, Integer.Sparse.eval_collectBalanced, rawRowCheck18476]

theorem rawRowCheck18477 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow18477 := by decide +kernel

theorem rowCheck18477 : row18477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18477 := by decide +kernel

theorem rowEval18477 (x : Key → ℝ) : Integer.Sparse.eval row18477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18477, Integer.Sparse.eval_collectBalanced, rawRowCheck18477]

theorem rawRowCheck18478 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow18478 := by decide +kernel

theorem rowCheck18478 : row18478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18478 := by decide +kernel

theorem rowEval18478 (x : Key → ℝ) : Integer.Sparse.eval row18478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18478, Integer.Sparse.eval_collectBalanced, rawRowCheck18478]

theorem rawRowCheck18479 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow18479 := by decide +kernel

theorem rowCheck18479 : row18479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18479 := by decide +kernel

theorem rowEval18479 (x : Key → ℝ) : Integer.Sparse.eval row18479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18479, Integer.Sparse.eval_collectBalanced, rawRowCheck18479]

theorem rawRowCheck18480 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18480 := by decide +kernel

theorem rowCheck18480 : row18480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18480 := by decide +kernel

theorem rowEval18480 (x : Key → ℝ) : Integer.Sparse.eval row18480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18480, Integer.Sparse.eval_collectBalanced, rawRowCheck18480]

theorem rawRowCheck18481 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18481 := by decide +kernel

theorem rowCheck18481 : row18481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18481 := by decide +kernel

theorem rowEval18481 (x : Key → ℝ) : Integer.Sparse.eval row18481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18481, Integer.Sparse.eval_collectBalanced, rawRowCheck18481]

theorem rawRowCheck18482 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18482 := by decide +kernel

theorem rowCheck18482 : row18482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18482 := by decide +kernel

theorem rowEval18482 (x : Key → ℝ) : Integer.Sparse.eval row18482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18482, Integer.Sparse.eval_collectBalanced, rawRowCheck18482]

theorem rawRowCheck18483 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0 = rawRow18483 := by decide +kernel

theorem rowCheck18483 : row18483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18483 := by decide +kernel

theorem rowEval18483 (x : Key → ℝ) : Integer.Sparse.eval row18483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18483, Integer.Sparse.eval_collectBalanced, rawRowCheck18483]

theorem rawRowCheck18484 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0 = rawRow18484 := by decide +kernel

theorem rowCheck18484 : row18484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18484 := by decide +kernel

theorem rowEval18484 (x : Key → ℝ) : Integer.Sparse.eval row18484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18484, Integer.Sparse.eval_collectBalanced, rawRowCheck18484]

theorem rawRowCheck18485 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0 = rawRow18485 := by decide +kernel

theorem rowCheck18485 : row18485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18485 := by decide +kernel

theorem rowEval18485 (x : Key → ℝ) : Integer.Sparse.eval row18485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18485, Integer.Sparse.eval_collectBalanced, rawRowCheck18485]

theorem rawRowCheck18486 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0 = rawRow18486 := by decide +kernel

theorem rowCheck18486 : row18486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18486 := by decide +kernel

theorem rowEval18486 (x : Key → ℝ) : Integer.Sparse.eval row18486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18486, Integer.Sparse.eval_collectBalanced, rawRowCheck18486]

theorem rawRowCheck18487 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0 = rawRow18487 := by decide +kernel

theorem rowCheck18487 : row18487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18487 := by decide +kernel

theorem rowEval18487 (x : Key → ℝ) : Integer.Sparse.eval row18487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18487, Integer.Sparse.eval_collectBalanced, rawRowCheck18487]

theorem rawRowCheck18488 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0 = rawRow18488 := by decide +kernel

theorem rowCheck18488 : row18488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18488 := by decide +kernel

theorem rowEval18488 (x : Key → ℝ) : Integer.Sparse.eval row18488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18488, Integer.Sparse.eval_collectBalanced, rawRowCheck18488]

theorem rawRowCheck18489 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0 = rawRow18489 := by decide +kernel

theorem rowCheck18489 : row18489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18489 := by decide +kernel

theorem rowEval18489 (x : Key → ℝ) : Integer.Sparse.eval row18489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18489, Integer.Sparse.eval_collectBalanced, rawRowCheck18489]

theorem rawRowCheck18490 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0 = rawRow18490 := by decide +kernel

theorem rowCheck18490 : row18490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18490 := by decide +kernel

theorem rowEval18490 (x : Key → ℝ) : Integer.Sparse.eval row18490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18490, Integer.Sparse.eval_collectBalanced, rawRowCheck18490]

theorem rawRowCheck18491 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0 = rawRow18491 := by decide +kernel

theorem rowCheck18491 : row18491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18491 := by decide +kernel

theorem rowEval18491 (x : Key → ℝ) : Integer.Sparse.eval row18491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18491, Integer.Sparse.eval_collectBalanced, rawRowCheck18491]

theorem rawRowCheck18492 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0 = rawRow18492 := by decide +kernel

theorem rowCheck18492 : row18492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18492 := by decide +kernel

theorem rowEval18492 (x : Key → ℝ) : Integer.Sparse.eval row18492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18492, Integer.Sparse.eval_collectBalanced, rawRowCheck18492]

theorem rawRowCheck18493 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0 = rawRow18493 := by decide +kernel

theorem rowCheck18493 : row18493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18493 := by decide +kernel

theorem rowEval18493 (x : Key → ℝ) : Integer.Sparse.eval row18493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18493, Integer.Sparse.eval_collectBalanced, rawRowCheck18493]

theorem rawRowCheck18494 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0 = rawRow18494 := by decide +kernel

theorem rowCheck18494 : row18494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18494 := by decide +kernel

theorem rowEval18494 (x : Key → ℝ) : Integer.Sparse.eval row18494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18494, Integer.Sparse.eval_collectBalanced, rawRowCheck18494]

theorem rawRowCheck18495 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0 = rawRow18495 := by decide +kernel

theorem rowCheck18495 : row18495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18495 := by decide +kernel

theorem rowEval18495 (x : Key → ℝ) : Integer.Sparse.eval row18495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18495, Integer.Sparse.eval_collectBalanced, rawRowCheck18495]

theorem rawRowCheck18496 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0 = rawRow18496 := by decide +kernel

theorem rowCheck18496 : row18496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18496 := by decide +kernel

theorem rowEval18496 (x : Key → ℝ) : Integer.Sparse.eval row18496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18496, Integer.Sparse.eval_collectBalanced, rawRowCheck18496]

theorem rawRowCheck18497 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0 = rawRow18497 := by decide +kernel

theorem rowCheck18497 : row18497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18497 := by decide +kernel

theorem rowEval18497 (x : Key → ℝ) : Integer.Sparse.eval row18497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18497, Integer.Sparse.eval_collectBalanced, rawRowCheck18497]

theorem rawRowCheck18498 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0 = rawRow18498 := by decide +kernel

theorem rowCheck18498 : row18498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18498 := by decide +kernel

theorem rowEval18498 (x : Key → ℝ) : Integer.Sparse.eval row18498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18498, Integer.Sparse.eval_collectBalanced, rawRowCheck18498]

theorem rawRowCheck18499 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0 = rawRow18499 := by decide +kernel

theorem rowCheck18499 : row18499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18499 := by decide +kernel

theorem rowEval18499 (x : Key → ℝ) : Integer.Sparse.eval row18499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18499, Integer.Sparse.eval_collectBalanced, rawRowCheck18499]

theorem rawRowCheck18500 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0 = rawRow18500 := by decide +kernel

theorem rowCheck18500 : row18500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18500 := by decide +kernel

theorem rowEval18500 (x : Key → ℝ) : Integer.Sparse.eval row18500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18500, Integer.Sparse.eval_collectBalanced, rawRowCheck18500]

theorem rawRowCheck18501 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0 = rawRow18501 := by decide +kernel

theorem rowCheck18501 : row18501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18501 := by decide +kernel

theorem rowEval18501 (x : Key → ℝ) : Integer.Sparse.eval row18501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18501, Integer.Sparse.eval_collectBalanced, rawRowCheck18501]

theorem rawRowCheck18502 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0 = rawRow18502 := by decide +kernel

theorem rowCheck18502 : row18502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18502 := by decide +kernel

theorem rowEval18502 (x : Key → ℝ) : Integer.Sparse.eval row18502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18502, Integer.Sparse.eval_collectBalanced, rawRowCheck18502]

theorem rawRowCheck18503 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0 = rawRow18503 := by decide +kernel

theorem rowCheck18503 : row18503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18503 := by decide +kernel

theorem rowEval18503 (x : Key → ℝ) : Integer.Sparse.eval row18503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18503, Integer.Sparse.eval_collectBalanced, rawRowCheck18503]

theorem rawRowCheck18504 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0 = rawRow18504 := by decide +kernel

theorem rowCheck18504 : row18504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18504 := by decide +kernel

theorem rowEval18504 (x : Key → ℝ) : Integer.Sparse.eval row18504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18504, Integer.Sparse.eval_collectBalanced, rawRowCheck18504]

theorem rawRowCheck18505 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0 = rawRow18505 := by decide +kernel

theorem rowCheck18505 : row18505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18505 := by decide +kernel

theorem rowEval18505 (x : Key → ℝ) : Integer.Sparse.eval row18505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18505, Integer.Sparse.eval_collectBalanced, rawRowCheck18505]

theorem rawRowCheck18506 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0 = rawRow18506 := by decide +kernel

theorem rowCheck18506 : row18506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18506 := by decide +kernel

theorem rowEval18506 (x : Key → ℝ) : Integer.Sparse.eval row18506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18506, Integer.Sparse.eval_collectBalanced, rawRowCheck18506]

theorem rawRowCheck18507 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18507 := by decide +kernel

theorem rowCheck18507 : row18507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18507 := by decide +kernel

theorem rowEval18507 (x : Key → ℝ) : Integer.Sparse.eval row18507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18507, Integer.Sparse.eval_collectBalanced, rawRowCheck18507]

theorem rawRowCheck18508 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18508 := by decide +kernel

theorem rowCheck18508 : row18508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18508 := by decide +kernel

theorem rowEval18508 (x : Key → ℝ) : Integer.Sparse.eval row18508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18508, Integer.Sparse.eval_collectBalanced, rawRowCheck18508]

theorem rawRowCheck18509 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18509 := by decide +kernel

theorem rowCheck18509 : row18509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18509 := by decide +kernel

theorem rowEval18509 (x : Key → ℝ) : Integer.Sparse.eval row18509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18509, Integer.Sparse.eval_collectBalanced, rawRowCheck18509]

theorem rawRowCheck18510 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18510 := by decide +kernel

theorem rowCheck18510 : row18510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18510 := by decide +kernel

theorem rowEval18510 (x : Key → ℝ) : Integer.Sparse.eval row18510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18510, Integer.Sparse.eval_collectBalanced, rawRowCheck18510]

theorem rawRowCheck18511 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18511 := by decide +kernel

theorem rowCheck18511 : row18511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18511 := by decide +kernel

theorem rowEval18511 (x : Key → ℝ) : Integer.Sparse.eval row18511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18511, Integer.Sparse.eval_collectBalanced, rawRowCheck18511]

theorem rawRowCheck18512 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18512 := by decide +kernel

theorem rowCheck18512 : row18512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18512 := by decide +kernel

theorem rowEval18512 (x : Key → ℝ) : Integer.Sparse.eval row18512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18512, Integer.Sparse.eval_collectBalanced, rawRowCheck18512]

theorem rawRowCheck18513 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow18513 := by decide +kernel

theorem rowCheck18513 : row18513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18513 := by decide +kernel

theorem rowEval18513 (x : Key → ℝ) : Integer.Sparse.eval row18513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18513, Integer.Sparse.eval_collectBalanced, rawRowCheck18513]

theorem rawRowCheck18514 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow18514 := by decide +kernel

theorem rowCheck18514 : row18514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18514 := by decide +kernel

theorem rowEval18514 (x : Key → ℝ) : Integer.Sparse.eval row18514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18514, Integer.Sparse.eval_collectBalanced, rawRowCheck18514]

theorem rawRowCheck18515 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow18515 := by decide +kernel

theorem rowCheck18515 : row18515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18515 := by decide +kernel

theorem rowEval18515 (x : Key → ℝ) : Integer.Sparse.eval row18515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18515, Integer.Sparse.eval_collectBalanced, rawRowCheck18515]

theorem rawRowCheck18516 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow18516 := by decide +kernel

theorem rowCheck18516 : row18516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18516 := by decide +kernel

theorem rowEval18516 (x : Key → ℝ) : Integer.Sparse.eval row18516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18516, Integer.Sparse.eval_collectBalanced, rawRowCheck18516]

theorem rawRowCheck18517 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow18517 := by decide +kernel

theorem rowCheck18517 : row18517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18517 := by decide +kernel

theorem rowEval18517 (x : Key → ℝ) : Integer.Sparse.eval row18517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18517, Integer.Sparse.eval_collectBalanced, rawRowCheck18517]

theorem rawRowCheck18518 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow18518 := by decide +kernel

theorem rowCheck18518 : row18518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18518 := by decide +kernel

theorem rowEval18518 (x : Key → ℝ) : Integer.Sparse.eval row18518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18518, Integer.Sparse.eval_collectBalanced, rawRowCheck18518]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block5.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form0.terms k).tag (GramFunctions.Block5.form0.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18429 x
  · exact rowEval18430 x
  · exact rowEval18431 x
  · exact rowEval18432 x
  · exact rowEval18433 x
  · exact rowEval18434 x
  · exact rowEval18435 x
  · exact rowEval18436 x
  · exact rowEval18437 x
  · exact rowEval18438 x
  · exact rowEval18439 x
  · exact rowEval18440 x
  · exact rowEval18441 x
  · exact rowEval18442 x
  · exact rowEval18443 x
  · exact rowEval18444 x
  · exact rowEval18445 x
  · exact rowEval18446 x
  · exact rowEval18447 x
  · exact rowEval18448 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block5.form0.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form0 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block5.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form1.terms k).tag (GramFunctions.Block5.form1.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18449 x
  · exact rowEval18450 x
  · exact rowEval18451 x
  · exact rowEval18452 x
  · exact rowEval18453 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block5.form1.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form1 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

end MUB6.Certificate.GramEntries.Block5

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

theorem rawRowCheck19384 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19384 := by decide +kernel

theorem rowCheck19384 : row19384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19384 := by decide +kernel

theorem rowEval19384 (x : Key → ℝ) : Integer.Sparse.eval row19384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19384, Integer.Sparse.eval_collectBalanced, rawRowCheck19384]

theorem rawRowCheck19385 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19385 := by decide +kernel

theorem rowCheck19385 : row19385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19385 := by decide +kernel

theorem rowEval19385 (x : Key → ℝ) : Integer.Sparse.eval row19385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19385, Integer.Sparse.eval_collectBalanced, rawRowCheck19385]

theorem rawRowCheck19386 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19386 := by decide +kernel

theorem rowCheck19386 : row19386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19386 := by decide +kernel

theorem rowEval19386 (x : Key → ℝ) : Integer.Sparse.eval row19386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19386, Integer.Sparse.eval_collectBalanced, rawRowCheck19386]

theorem rawRowCheck19387 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19387 := by decide +kernel

theorem rowCheck19387 : row19387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19387 := by decide +kernel

theorem rowEval19387 (x : Key → ℝ) : Integer.Sparse.eval row19387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19387, Integer.Sparse.eval_collectBalanced, rawRowCheck19387]

theorem rawRowCheck19388 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19388 := by decide +kernel

theorem rowCheck19388 : row19388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19388 := by decide +kernel

theorem rowEval19388 (x : Key → ℝ) : Integer.Sparse.eval row19388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19388, Integer.Sparse.eval_collectBalanced, rawRowCheck19388]

theorem rawRowCheck19389 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19389 := by decide +kernel

theorem rowCheck19389 : row19389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19389 := by decide +kernel

theorem rowEval19389 (x : Key → ℝ) : Integer.Sparse.eval row19389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19389, Integer.Sparse.eval_collectBalanced, rawRowCheck19389]

theorem rawRowCheck19390 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19390 := by decide +kernel

theorem rowCheck19390 : row19390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19390 := by decide +kernel

theorem rowEval19390 (x : Key → ℝ) : Integer.Sparse.eval row19390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19390, Integer.Sparse.eval_collectBalanced, rawRowCheck19390]

theorem rawRowCheck19391 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19391 := by decide +kernel

theorem rowCheck19391 : row19391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19391 := by decide +kernel

theorem rowEval19391 (x : Key → ℝ) : Integer.Sparse.eval row19391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19391, Integer.Sparse.eval_collectBalanced, rawRowCheck19391]

theorem rawRowCheck19392 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19392 := by decide +kernel

theorem rowCheck19392 : row19392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19392 := by decide +kernel

theorem rowEval19392 (x : Key → ℝ) : Integer.Sparse.eval row19392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19392, Integer.Sparse.eval_collectBalanced, rawRowCheck19392]

theorem rawRowCheck19393 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19393 := by decide +kernel

theorem rowCheck19393 : row19393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19393 := by decide +kernel

theorem rowEval19393 (x : Key → ℝ) : Integer.Sparse.eval row19393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19393, Integer.Sparse.eval_collectBalanced, rawRowCheck19393]

theorem rawRowCheck19394 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19394 := by decide +kernel

theorem rowCheck19394 : row19394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19394 := by decide +kernel

theorem rowEval19394 (x : Key → ℝ) : Integer.Sparse.eval row19394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19394, Integer.Sparse.eval_collectBalanced, rawRowCheck19394]

theorem rawRowCheck19395 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19395 := by decide +kernel

theorem rowCheck19395 : row19395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19395 := by decide +kernel

theorem rowEval19395 (x : Key → ℝ) : Integer.Sparse.eval row19395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19395, Integer.Sparse.eval_collectBalanced, rawRowCheck19395]

theorem rawRowCheck19396 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19396 := by decide +kernel

theorem rowCheck19396 : row19396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19396 := by decide +kernel

theorem rowEval19396 (x : Key → ℝ) : Integer.Sparse.eval row19396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19396, Integer.Sparse.eval_collectBalanced, rawRowCheck19396]

theorem rawRowCheck19397 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19397 := by decide +kernel

theorem rowCheck19397 : row19397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19397 := by decide +kernel

theorem rowEval19397 (x : Key → ℝ) : Integer.Sparse.eval row19397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19397, Integer.Sparse.eval_collectBalanced, rawRowCheck19397]

theorem rawRowCheck19398 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19398 := by decide +kernel

theorem rowCheck19398 : row19398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19398 := by decide +kernel

theorem rowEval19398 (x : Key → ℝ) : Integer.Sparse.eval row19398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19398, Integer.Sparse.eval_collectBalanced, rawRowCheck19398]

theorem rawRowCheck19399 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19399 := by decide +kernel

theorem rowCheck19399 : row19399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19399 := by decide +kernel

theorem rowEval19399 (x : Key → ℝ) : Integer.Sparse.eval row19399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19399, Integer.Sparse.eval_collectBalanced, rawRowCheck19399]

theorem rawRowCheck19400 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19400 := by decide +kernel

theorem rowCheck19400 : row19400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19400 := by decide +kernel

theorem rowEval19400 (x : Key → ℝ) : Integer.Sparse.eval row19400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19400, Integer.Sparse.eval_collectBalanced, rawRowCheck19400]

theorem rawRowCheck19401 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19401 := by decide +kernel

theorem rowCheck19401 : row19401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19401 := by decide +kernel

theorem rowEval19401 (x : Key → ℝ) : Integer.Sparse.eval row19401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19401, Integer.Sparse.eval_collectBalanced, rawRowCheck19401]

theorem rawRowCheck19402 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19402 := by decide +kernel

theorem rowCheck19402 : row19402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19402 := by decide +kernel

theorem rowEval19402 (x : Key → ℝ) : Integer.Sparse.eval row19402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19402, Integer.Sparse.eval_collectBalanced, rawRowCheck19402]

theorem rawRowCheck19403 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19403 := by decide +kernel

theorem rowCheck19403 : row19403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19403 := by decide +kernel

theorem rowEval19403 (x : Key → ℝ) : Integer.Sparse.eval row19403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19403, Integer.Sparse.eval_collectBalanced, rawRowCheck19403]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19604 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19604 := by decide +kernel

theorem rowCheck19604 : row19604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19604 := by decide +kernel

theorem rowEval19604 (x : Key → ℝ) : Integer.Sparse.eval row19604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19604, Integer.Sparse.eval_collectBalanced, rawRowCheck19604]

theorem rawRowCheck19605 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19605 := by decide +kernel

theorem rowCheck19605 : row19605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19605 := by decide +kernel

theorem rowEval19605 (x : Key → ℝ) : Integer.Sparse.eval row19605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19605, Integer.Sparse.eval_collectBalanced, rawRowCheck19605]

theorem rawRowCheck19606 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19606 := by decide +kernel

theorem rowCheck19606 : row19606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19606 := by decide +kernel

theorem rowEval19606 (x : Key → ℝ) : Integer.Sparse.eval row19606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19606, Integer.Sparse.eval_collectBalanced, rawRowCheck19606]

theorem rawRowCheck19607 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19607 := by decide +kernel

theorem rowCheck19607 : row19607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19607 := by decide +kernel

theorem rowEval19607 (x : Key → ℝ) : Integer.Sparse.eval row19607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19607, Integer.Sparse.eval_collectBalanced, rawRowCheck19607]

theorem rawRowCheck19608 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19608 := by decide +kernel

theorem rowCheck19608 : row19608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19608 := by decide +kernel

theorem rowEval19608 (x : Key → ℝ) : Integer.Sparse.eval row19608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19608, Integer.Sparse.eval_collectBalanced, rawRowCheck19608]

theorem rawRowCheck19609 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19609 := by decide +kernel

theorem rowCheck19609 : row19609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19609 := by decide +kernel

theorem rowEval19609 (x : Key → ℝ) : Integer.Sparse.eval row19609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19609, Integer.Sparse.eval_collectBalanced, rawRowCheck19609]

theorem rawRowCheck19610 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19610 := by decide +kernel

theorem rowCheck19610 : row19610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19610 := by decide +kernel

theorem rowEval19610 (x : Key → ℝ) : Integer.Sparse.eval row19610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19610, Integer.Sparse.eval_collectBalanced, rawRowCheck19610]

theorem rawRowCheck19611 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19611 := by decide +kernel

theorem rowCheck19611 : row19611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19611 := by decide +kernel

theorem rowEval19611 (x : Key → ℝ) : Integer.Sparse.eval row19611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19611, Integer.Sparse.eval_collectBalanced, rawRowCheck19611]

theorem rawRowCheck19612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19612 := by decide +kernel

theorem rowCheck19612 : row19612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19612 := by decide +kernel

theorem rowEval19612 (x : Key → ℝ) : Integer.Sparse.eval row19612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19612, Integer.Sparse.eval_collectBalanced, rawRowCheck19612]

theorem rawRowCheck19613 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19613 := by decide +kernel

theorem rowCheck19613 : row19613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19613 := by decide +kernel

theorem rowEval19613 (x : Key → ℝ) : Integer.Sparse.eval row19613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19613, Integer.Sparse.eval_collectBalanced, rawRowCheck19613]

theorem rawRowCheck19614 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19614 := by decide +kernel

theorem rowCheck19614 : row19614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19614 := by decide +kernel

theorem rowEval19614 (x : Key → ℝ) : Integer.Sparse.eval row19614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19614, Integer.Sparse.eval_collectBalanced, rawRowCheck19614]

theorem rawRowCheck19615 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19615 := by decide +kernel

theorem rowCheck19615 : row19615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19615 := by decide +kernel

theorem rowEval19615 (x : Key → ℝ) : Integer.Sparse.eval row19615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19615, Integer.Sparse.eval_collectBalanced, rawRowCheck19615]

theorem rawRowCheck19616 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19616 := by decide +kernel

theorem rowCheck19616 : row19616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19616 := by decide +kernel

theorem rowEval19616 (x : Key → ℝ) : Integer.Sparse.eval row19616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19616, Integer.Sparse.eval_collectBalanced, rawRowCheck19616]

theorem rawRowCheck19617 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19617 := by decide +kernel

theorem rowCheck19617 : row19617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19617 := by decide +kernel

theorem rowEval19617 (x : Key → ℝ) : Integer.Sparse.eval row19617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19617, Integer.Sparse.eval_collectBalanced, rawRowCheck19617]

theorem rawRowCheck19618 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19618 := by decide +kernel

theorem rowCheck19618 : row19618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19618 := by decide +kernel

theorem rowEval19618 (x : Key → ℝ) : Integer.Sparse.eval row19618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19618, Integer.Sparse.eval_collectBalanced, rawRowCheck19618]

theorem rawRowCheck19619 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19619 := by decide +kernel

theorem rowCheck19619 : row19619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19619 := by decide +kernel

theorem rowEval19619 (x : Key → ℝ) : Integer.Sparse.eval row19619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19619, Integer.Sparse.eval_collectBalanced, rawRowCheck19619]

theorem rawRowCheck19620 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19620 := by decide +kernel

theorem rowCheck19620 : row19620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19620 := by decide +kernel

theorem rowEval19620 (x : Key → ℝ) : Integer.Sparse.eval row19620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19620, Integer.Sparse.eval_collectBalanced, rawRowCheck19620]

theorem rawRowCheck19621 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19621 := by decide +kernel

theorem rowCheck19621 : row19621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19621 := by decide +kernel

theorem rowEval19621 (x : Key → ℝ) : Integer.Sparse.eval row19621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19621, Integer.Sparse.eval_collectBalanced, rawRowCheck19621]

theorem rawRowCheck19622 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19622 := by decide +kernel

theorem rowCheck19622 : row19622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19622 := by decide +kernel

theorem rowEval19622 (x : Key → ℝ) : Integer.Sparse.eval row19622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19622, Integer.Sparse.eval_collectBalanced, rawRowCheck19622]

theorem rawRowCheck19623 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19623 := by decide +kernel

theorem rowCheck19623 : row19623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19623 := by decide +kernel

theorem rowEval19623 (x : Key → ℝ) : Integer.Sparse.eval row19623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19623, Integer.Sparse.eval_collectBalanced, rawRowCheck19623]

theorem rawRowCheck19624 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19624 := by decide +kernel

theorem rowCheck19624 : row19624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19624 := by decide +kernel

theorem rowEval19624 (x : Key → ℝ) : Integer.Sparse.eval row19624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19624, Integer.Sparse.eval_collectBalanced, rawRowCheck19624]

theorem rawRowCheck19625 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19625 := by decide +kernel

theorem rowCheck19625 : row19625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19625 := by decide +kernel

theorem rowEval19625 (x : Key → ℝ) : Integer.Sparse.eval row19625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19625, Integer.Sparse.eval_collectBalanced, rawRowCheck19625]

theorem rawRowCheck19626 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19626 := by decide +kernel

theorem rowCheck19626 : row19626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19626 := by decide +kernel

theorem rowEval19626 (x : Key → ℝ) : Integer.Sparse.eval row19626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19626, Integer.Sparse.eval_collectBalanced, rawRowCheck19626]

theorem rawRowCheck19627 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19627 := by decide +kernel

theorem rowCheck19627 : row19627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19627 := by decide +kernel

theorem rowEval19627 (x : Key → ℝ) : Integer.Sparse.eval row19627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19627, Integer.Sparse.eval_collectBalanced, rawRowCheck19627]

theorem rawRowCheck19628 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19628 := by decide +kernel

theorem rowCheck19628 : row19628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19628 := by decide +kernel

theorem rowEval19628 (x : Key → ℝ) : Integer.Sparse.eval row19628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19628, Integer.Sparse.eval_collectBalanced, rawRowCheck19628]

theorem rawRowCheck19629 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19629 := by decide +kernel

theorem rowCheck19629 : row19629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19629 := by decide +kernel

theorem rowEval19629 (x : Key → ℝ) : Integer.Sparse.eval row19629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19629, Integer.Sparse.eval_collectBalanced, rawRowCheck19629]

theorem rawRowCheck19630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19630 := by decide +kernel

theorem rowCheck19630 : row19630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19630 := by decide +kernel

theorem rowEval19630 (x : Key → ℝ) : Integer.Sparse.eval row19630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19630, Integer.Sparse.eval_collectBalanced, rawRowCheck19630]

theorem rawRowCheck19631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19631 := by decide +kernel

theorem rowCheck19631 : row19631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19631 := by decide +kernel

theorem rowEval19631 (x : Key → ℝ) : Integer.Sparse.eval row19631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19631, Integer.Sparse.eval_collectBalanced, rawRowCheck19631]

theorem rawRowCheck19632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19632 := by decide +kernel

theorem rowCheck19632 : row19632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19632 := by decide +kernel

theorem rowEval19632 (x : Key → ℝ) : Integer.Sparse.eval row19632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19632, Integer.Sparse.eval_collectBalanced, rawRowCheck19632]

theorem rawRowCheck19633 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19633 := by decide +kernel

theorem rowCheck19633 : row19633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19633 := by decide +kernel

theorem rowEval19633 (x : Key → ℝ) : Integer.Sparse.eval row19633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19633, Integer.Sparse.eval_collectBalanced, rawRowCheck19633]

theorem rawRowCheck19634 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19634 := by decide +kernel

theorem rowCheck19634 : row19634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19634 := by decide +kernel

theorem rowEval19634 (x : Key → ℝ) : Integer.Sparse.eval row19634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19634, Integer.Sparse.eval_collectBalanced, rawRowCheck19634]

theorem rawRowCheck19635 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19635 := by decide +kernel

theorem rowCheck19635 : row19635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19635 := by decide +kernel

theorem rowEval19635 (x : Key → ℝ) : Integer.Sparse.eval row19635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19635, Integer.Sparse.eval_collectBalanced, rawRowCheck19635]

theorem rawRowCheck19636 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19636 := by decide +kernel

theorem rowCheck19636 : row19636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19636 := by decide +kernel

theorem rowEval19636 (x : Key → ℝ) : Integer.Sparse.eval row19636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19636, Integer.Sparse.eval_collectBalanced, rawRowCheck19636]

theorem rawRowCheck19637 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19637 := by decide +kernel

theorem rowCheck19637 : row19637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19637 := by decide +kernel

theorem rowEval19637 (x : Key → ℝ) : Integer.Sparse.eval row19637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19637, Integer.Sparse.eval_collectBalanced, rawRowCheck19637]

theorem rawRowCheck19638 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19638 := by decide +kernel

theorem rowCheck19638 : row19638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19638 := by decide +kernel

theorem rowEval19638 (x : Key → ℝ) : Integer.Sparse.eval row19638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19638, Integer.Sparse.eval_collectBalanced, rawRowCheck19638]

theorem rawRowCheck19639 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19639 := by decide +kernel

theorem rowCheck19639 : row19639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19639 := by decide +kernel

theorem rowEval19639 (x : Key → ℝ) : Integer.Sparse.eval row19639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19639, Integer.Sparse.eval_collectBalanced, rawRowCheck19639]

theorem rawRowCheck19640 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0 = rawRow19640 := by decide +kernel

theorem rowCheck19640 : row19640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19640 := by decide +kernel

theorem rowEval19640 (x : Key → ℝ) : Integer.Sparse.eval row19640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19640, Integer.Sparse.eval_collectBalanced, rawRowCheck19640]

theorem rawRowCheck19641 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0 = rawRow19641 := by decide +kernel

theorem rowCheck19641 : row19641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19641 := by decide +kernel

theorem rowEval19641 (x : Key → ℝ) : Integer.Sparse.eval row19641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19641, Integer.Sparse.eval_collectBalanced, rawRowCheck19641]

theorem rawRowCheck19642 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0 = rawRow19642 := by decide +kernel

theorem rowCheck19642 : row19642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19642 := by decide +kernel

theorem rowEval19642 (x : Key → ℝ) : Integer.Sparse.eval row19642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19642, Integer.Sparse.eval_collectBalanced, rawRowCheck19642]

theorem rawRowCheck19643 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0 = rawRow19643 := by decide +kernel

theorem rowCheck19643 : row19643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19643 := by decide +kernel

theorem rowEval19643 (x : Key → ℝ) : Integer.Sparse.eval row19643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19643, Integer.Sparse.eval_collectBalanced, rawRowCheck19643]

theorem rawRowCheck19644 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0 = rawRow19644 := by decide +kernel

theorem rowCheck19644 : row19644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19644 := by decide +kernel

theorem rowEval19644 (x : Key → ℝ) : Integer.Sparse.eval row19644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19644, Integer.Sparse.eval_collectBalanced, rawRowCheck19644]

theorem rawRowCheck19645 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0 = rawRow19645 := by decide +kernel

theorem rowCheck19645 : row19645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19645 := by decide +kernel

theorem rowEval19645 (x : Key → ℝ) : Integer.Sparse.eval row19645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19645, Integer.Sparse.eval_collectBalanced, rawRowCheck19645]

theorem rawRowCheck19646 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19646 := by decide +kernel

theorem rowCheck19646 : row19646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19646 := by decide +kernel

theorem rowEval19646 (x : Key → ℝ) : Integer.Sparse.eval row19646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19646, Integer.Sparse.eval_collectBalanced, rawRowCheck19646]

theorem rawRowCheck19647 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19647 := by decide +kernel

theorem rowCheck19647 : row19647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19647 := by decide +kernel

theorem rowEval19647 (x : Key → ℝ) : Integer.Sparse.eval row19647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19647, Integer.Sparse.eval_collectBalanced, rawRowCheck19647]

theorem rawRowCheck19648 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19648 := by decide +kernel

theorem rowCheck19648 : row19648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19648 := by decide +kernel

theorem rowEval19648 (x : Key → ℝ) : Integer.Sparse.eval row19648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19648, Integer.Sparse.eval_collectBalanced, rawRowCheck19648]

theorem rawRowCheck19649 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19649 := by decide +kernel

theorem rowCheck19649 : row19649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19649 := by decide +kernel

theorem rowEval19649 (x : Key → ℝ) : Integer.Sparse.eval row19649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19649, Integer.Sparse.eval_collectBalanced, rawRowCheck19649]

theorem rawRowCheck19650 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19650 := by decide +kernel

theorem rowCheck19650 : row19650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19650 := by decide +kernel

theorem rowEval19650 (x : Key → ℝ) : Integer.Sparse.eval row19650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19650, Integer.Sparse.eval_collectBalanced, rawRowCheck19650]

theorem rawRowCheck19651 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19651 := by decide +kernel

theorem rowCheck19651 : row19651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19651 := by decide +kernel

theorem rowEval19651 (x : Key → ℝ) : Integer.Sparse.eval row19651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19651, Integer.Sparse.eval_collectBalanced, rawRowCheck19651]

theorem rawRowCheck19652 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19652 := by decide +kernel

theorem rowCheck19652 : row19652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19652 := by decide +kernel

theorem rowEval19652 (x : Key → ℝ) : Integer.Sparse.eval row19652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19652, Integer.Sparse.eval_collectBalanced, rawRowCheck19652]

theorem rawRowCheck19653 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19653 := by decide +kernel

theorem rowCheck19653 : row19653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19653 := by decide +kernel

theorem rowEval19653 (x : Key → ℝ) : Integer.Sparse.eval row19653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19653, Integer.Sparse.eval_collectBalanced, rawRowCheck19653]

theorem rawRowCheck19654 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19654 := by decide +kernel

theorem rowCheck19654 : row19654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19654 := by decide +kernel

theorem rowEval19654 (x : Key → ℝ) : Integer.Sparse.eval row19654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19654, Integer.Sparse.eval_collectBalanced, rawRowCheck19654]

theorem rawRowCheck19655 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19655 := by decide +kernel

theorem rowCheck19655 : row19655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19655 := by decide +kernel

theorem rowEval19655 (x : Key → ℝ) : Integer.Sparse.eval row19655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19655, Integer.Sparse.eval_collectBalanced, rawRowCheck19655]

theorem rawRowCheck19656 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19656 := by decide +kernel

theorem rowCheck19656 : row19656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19656 := by decide +kernel

theorem rowEval19656 (x : Key → ℝ) : Integer.Sparse.eval row19656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19656, Integer.Sparse.eval_collectBalanced, rawRowCheck19656]

theorem rawRowCheck19657 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19657 := by decide +kernel

theorem rowCheck19657 : row19657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19657 := by decide +kernel

theorem rowEval19657 (x : Key → ℝ) : Integer.Sparse.eval row19657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19657, Integer.Sparse.eval_collectBalanced, rawRowCheck19657]

theorem rawRowCheck19658 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19658 := by decide +kernel

theorem rowCheck19658 : row19658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19658 := by decide +kernel

theorem rowEval19658 (x : Key → ℝ) : Integer.Sparse.eval row19658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19658, Integer.Sparse.eval_collectBalanced, rawRowCheck19658]

theorem rawRowCheck19659 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19659 := by decide +kernel

theorem rowCheck19659 : row19659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19659 := by decide +kernel

theorem rowEval19659 (x : Key → ℝ) : Integer.Sparse.eval row19659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19659, Integer.Sparse.eval_collectBalanced, rawRowCheck19659]

theorem rawRowCheck19660 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19660 := by decide +kernel

theorem rowCheck19660 : row19660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19660 := by decide +kernel

theorem rowEval19660 (x : Key → ℝ) : Integer.Sparse.eval row19660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19660, Integer.Sparse.eval_collectBalanced, rawRowCheck19660]

theorem rawRowCheck19661 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19661 := by decide +kernel

theorem rowCheck19661 : row19661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19661 := by decide +kernel

theorem rowEval19661 (x : Key → ℝ) : Integer.Sparse.eval row19661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19661, Integer.Sparse.eval_collectBalanced, rawRowCheck19661]

theorem rawRowCheck19662 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19662 := by decide +kernel

theorem rowCheck19662 : row19662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19662 := by decide +kernel

theorem rowEval19662 (x : Key → ℝ) : Integer.Sparse.eval row19662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19662, Integer.Sparse.eval_collectBalanced, rawRowCheck19662]

theorem rawRowCheck19663 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19663 := by decide +kernel

theorem rowCheck19663 : row19663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19663 := by decide +kernel

theorem rowEval19663 (x : Key → ℝ) : Integer.Sparse.eval row19663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19663, Integer.Sparse.eval_collectBalanced, rawRowCheck19663]

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

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19384 x
  · exact rowEval19385 x
  · exact rowEval19386 x
  · exact rowEval19387 x
  · exact rowEval19388 x
  · exact rowEval19389 x
  · exact rowEval19390 x
  · exact rowEval19391 x
  · exact rowEval19392 x
  · exact rowEval19393 x
  · exact rowEval19394 x
  · exact rowEval19395 x
  · exact rowEval19396 x
  · exact rowEval19397 x
  · exact rowEval19398 x
  · exact rowEval19399 x
  · exact rowEval19400 x
  · exact rowEval19401 x
  · exact rowEval19402 x
  · exact rowEval19403 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

end MUB6.Certificate.GramEntries.Block5

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

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19604 x
  · exact rowEval19605 x
  · exact rowEval19606 x
  · exact rowEval19607 x
  · exact rowEval19608 x
  · exact rowEval19609 x
  · exact rowEval19610 x
  · exact rowEval19611 x
  · exact rowEval19612 x
  · exact rowEval19613 x
  · exact rowEval19614 x
  · exact rowEval19615 x
  · exact rowEval19616 x
  · exact rowEval19617 x
  · exact rowEval19618 x
  · exact rowEval19619 x
  · exact rowEval19620 x
  · exact rowEval19621 x
  · exact rowEval19622 x
  · exact rowEval19623 x
  · exact rowEval19624 x
  · exact rowEval19625 x
  · exact rowEval19626 x
  · exact rowEval19627 x
  · exact rowEval19628 x
  · exact rowEval19629 x
  · exact rowEval19630 x
  · exact rowEval19631 x
  · exact rowEval19632 x
  · exact rowEval19633 x
  · exact rowEval19634 x
  · exact rowEval19635 x
  · exact rowEval19636 x
  · exact rowEval19637 x
  · exact rowEval19638 x
  · exact rowEval19639 x
  · exact rowEval19640 x
  · exact rowEval19641 x
  · exact rowEval19642 x
  · exact rowEval19643 x
  · exact rowEval19644 x
  · exact rowEval19645 x
  · exact rowEval19646 x
  · exact rowEval19647 x
  · exact rowEval19648 x
  · exact rowEval19649 x
  · exact rowEval19650 x
  · exact rowEval19651 x
  · exact rowEval19652 x
  · exact rowEval19653 x
  · exact rowEval19654 x
  · exact rowEval19655 x
  · exact rowEval19656 x
  · exact rowEval19657 x
  · exact rowEval19658 x
  · exact rowEval19659 x
  · exact rowEval19660 x
  · exact rowEval19661 x
  · exact rowEval19662 x
  · exact rowEval19663 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

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

theorem rawRowCheck18659 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18659 := by decide +kernel

theorem rowCheck18659 : row18659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18659 := by decide +kernel

theorem rowEval18659 (x : Key → ℝ) : Integer.Sparse.eval row18659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18659, Integer.Sparse.eval_collectBalanced, rawRowCheck18659]

theorem rawRowCheck18660 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18660 := by decide +kernel

theorem rowCheck18660 : row18660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18660 := by decide +kernel

theorem rowEval18660 (x : Key → ℝ) : Integer.Sparse.eval row18660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18660, Integer.Sparse.eval_collectBalanced, rawRowCheck18660]

theorem rawRowCheck18661 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18661 := by decide +kernel

theorem rowCheck18661 : row18661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18661 := by decide +kernel

theorem rowEval18661 (x : Key → ℝ) : Integer.Sparse.eval row18661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18661, Integer.Sparse.eval_collectBalanced, rawRowCheck18661]

theorem rawRowCheck18662 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18662 := by decide +kernel

theorem rowCheck18662 : row18662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18662 := by decide +kernel

theorem rowEval18662 (x : Key → ℝ) : Integer.Sparse.eval row18662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18662, Integer.Sparse.eval_collectBalanced, rawRowCheck18662]

theorem rawRowCheck18663 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18663 := by decide +kernel

theorem rowCheck18663 : row18663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18663 := by decide +kernel

theorem rowEval18663 (x : Key → ℝ) : Integer.Sparse.eval row18663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18663, Integer.Sparse.eval_collectBalanced, rawRowCheck18663]

theorem rawRowCheck18664 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18664 := by decide +kernel

theorem rowCheck18664 : row18664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18664 := by decide +kernel

theorem rowEval18664 (x : Key → ℝ) : Integer.Sparse.eval row18664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18664, Integer.Sparse.eval_collectBalanced, rawRowCheck18664]

theorem rawRowCheck18665 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18665 := by decide +kernel

theorem rowCheck18665 : row18665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18665 := by decide +kernel

theorem rowEval18665 (x : Key → ℝ) : Integer.Sparse.eval row18665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18665, Integer.Sparse.eval_collectBalanced, rawRowCheck18665]

theorem rawRowCheck18666 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0 = rawRow18666 := by decide +kernel

theorem rowCheck18666 : row18666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18666 := by decide +kernel

theorem rowEval18666 (x : Key → ℝ) : Integer.Sparse.eval row18666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18666, Integer.Sparse.eval_collectBalanced, rawRowCheck18666]

theorem rawRowCheck18667 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0 = rawRow18667 := by decide +kernel

theorem rowCheck18667 : row18667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18667 := by decide +kernel

theorem rowEval18667 (x : Key → ℝ) : Integer.Sparse.eval row18667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18667, Integer.Sparse.eval_collectBalanced, rawRowCheck18667]

theorem rawRowCheck18668 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0 = rawRow18668 := by decide +kernel

theorem rowCheck18668 : row18668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18668 := by decide +kernel

theorem rowEval18668 (x : Key → ℝ) : Integer.Sparse.eval row18668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18668, Integer.Sparse.eval_collectBalanced, rawRowCheck18668]

theorem rawRowCheck18669 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0 = rawRow18669 := by decide +kernel

theorem rowCheck18669 : row18669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18669 := by decide +kernel

theorem rowEval18669 (x : Key → ℝ) : Integer.Sparse.eval row18669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18669, Integer.Sparse.eval_collectBalanced, rawRowCheck18669]

theorem rawRowCheck18670 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0 = rawRow18670 := by decide +kernel

theorem rowCheck18670 : row18670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18670 := by decide +kernel

theorem rowEval18670 (x : Key → ℝ) : Integer.Sparse.eval row18670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18670, Integer.Sparse.eval_collectBalanced, rawRowCheck18670]

theorem rawRowCheck18671 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0 = rawRow18671 := by decide +kernel

theorem rowCheck18671 : row18671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18671 := by decide +kernel

theorem rowEval18671 (x : Key → ℝ) : Integer.Sparse.eval row18671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18671, Integer.Sparse.eval_collectBalanced, rawRowCheck18671]

theorem rawRowCheck18672 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18672 := by decide +kernel

theorem rowCheck18672 : row18672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18672 := by decide +kernel

theorem rowEval18672 (x : Key → ℝ) : Integer.Sparse.eval row18672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18672, Integer.Sparse.eval_collectBalanced, rawRowCheck18672]

theorem rawRowCheck18673 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18673 := by decide +kernel

theorem rowCheck18673 : row18673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18673 := by decide +kernel

theorem rowEval18673 (x : Key → ℝ) : Integer.Sparse.eval row18673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18673, Integer.Sparse.eval_collectBalanced, rawRowCheck18673]

theorem rawRowCheck18674 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18674 := by decide +kernel

theorem rowCheck18674 : row18674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18674 := by decide +kernel

theorem rowEval18674 (x : Key → ℝ) : Integer.Sparse.eval row18674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18674, Integer.Sparse.eval_collectBalanced, rawRowCheck18674]

theorem rawRowCheck18675 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0 = rawRow18675 := by decide +kernel

theorem rowCheck18675 : row18675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18675 := by decide +kernel

theorem rowEval18675 (x : Key → ℝ) : Integer.Sparse.eval row18675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18675, Integer.Sparse.eval_collectBalanced, rawRowCheck18675]

theorem rawRowCheck18676 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18676 := by decide +kernel

theorem rowCheck18676 : row18676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18676 := by decide +kernel

theorem rowEval18676 (x : Key → ℝ) : Integer.Sparse.eval row18676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18676, Integer.Sparse.eval_collectBalanced, rawRowCheck18676]

theorem rawRowCheck18677 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18677 := by decide +kernel

theorem rowCheck18677 : row18677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18677 := by decide +kernel

theorem rowEval18677 (x : Key → ℝ) : Integer.Sparse.eval row18677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18677, Integer.Sparse.eval_collectBalanced, rawRowCheck18677]

theorem rawRowCheck18678 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18678 := by decide +kernel

theorem rowCheck18678 : row18678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18678 := by decide +kernel

theorem rowEval18678 (x : Key → ℝ) : Integer.Sparse.eval row18678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18678, Integer.Sparse.eval_collectBalanced, rawRowCheck18678]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18459 x
  · exact rowEval18460 x
  · exact rowEval18461 x
  · exact rowEval18462 x
  · exact rowEval18463 x
  · exact rowEval18464 x
  · exact rowEval18465 x
  · exact rowEval18466 x
  · exact rowEval18467 x
  · exact rowEval18468 x
  · exact rowEval18469 x
  · exact rowEval18470 x
  · exact rowEval18471 x
  · exact rowEval18472 x
  · exact rowEval18473 x
  · exact rowEval18474 x
  · exact rowEval18475 x
  · exact rowEval18476 x
  · exact rowEval18477 x
  · exact rowEval18478 x
  · exact rowEval18479 x
  · exact rowEval18480 x
  · exact rowEval18481 x
  · exact rowEval18482 x
  · exact rowEval18483 x
  · exact rowEval18484 x
  · exact rowEval18485 x
  · exact rowEval18486 x
  · exact rowEval18487 x
  · exact rowEval18488 x
  · exact rowEval18489 x
  · exact rowEval18490 x
  · exact rowEval18491 x
  · exact rowEval18492 x
  · exact rowEval18493 x
  · exact rowEval18494 x
  · exact rowEval18495 x
  · exact rowEval18496 x
  · exact rowEval18497 x
  · exact rowEval18498 x
  · exact rowEval18499 x
  · exact rowEval18500 x
  · exact rowEval18501 x
  · exact rowEval18502 x
  · exact rowEval18503 x
  · exact rowEval18504 x
  · exact rowEval18505 x
  · exact rowEval18506 x
  · exact rowEval18507 x
  · exact rowEval18508 x
  · exact rowEval18509 x
  · exact rowEval18510 x
  · exact rowEval18511 x
  · exact rowEval18512 x
  · exact rowEval18513 x
  · exact rowEval18514 x
  · exact rowEval18515 x
  · exact rowEval18516 x
  · exact rowEval18517 x
  · exact rowEval18518 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block5.form2.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form2 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

end MUB6.Certificate.GramEntries.Block5

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

theorem rawRowCheck18759 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18759 := by decide +kernel

theorem rowCheck18759 : row18759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18759 := by decide +kernel

theorem rowEval18759 (x : Key → ℝ) : Integer.Sparse.eval row18759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18759, Integer.Sparse.eval_collectBalanced, rawRowCheck18759]

theorem rawRowCheck18760 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18760 := by decide +kernel

theorem rowCheck18760 : row18760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18760 := by decide +kernel

theorem rowEval18760 (x : Key → ℝ) : Integer.Sparse.eval row18760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18760, Integer.Sparse.eval_collectBalanced, rawRowCheck18760]

theorem rawRowCheck18761 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18761 := by decide +kernel

theorem rowCheck18761 : row18761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18761 := by decide +kernel

theorem rowEval18761 (x : Key → ℝ) : Integer.Sparse.eval row18761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18761, Integer.Sparse.eval_collectBalanced, rawRowCheck18761]

theorem rawRowCheck18762 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18762 := by decide +kernel

theorem rowCheck18762 : row18762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18762 := by decide +kernel

theorem rowEval18762 (x : Key → ℝ) : Integer.Sparse.eval row18762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18762, Integer.Sparse.eval_collectBalanced, rawRowCheck18762]

theorem rawRowCheck18763 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18763 := by decide +kernel

theorem rowCheck18763 : row18763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18763 := by decide +kernel

theorem rowEval18763 (x : Key → ℝ) : Integer.Sparse.eval row18763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18763, Integer.Sparse.eval_collectBalanced, rawRowCheck18763]

theorem rawRowCheck18764 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18764 := by decide +kernel

theorem rowCheck18764 : row18764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18764 := by decide +kernel

theorem rowEval18764 (x : Key → ℝ) : Integer.Sparse.eval row18764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18764, Integer.Sparse.eval_collectBalanced, rawRowCheck18764]

theorem rawRowCheck18765 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0 = rawRow18765 := by decide +kernel

theorem rowCheck18765 : row18765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18765 := by decide +kernel

theorem rowEval18765 (x : Key → ℝ) : Integer.Sparse.eval row18765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18765, Integer.Sparse.eval_collectBalanced, rawRowCheck18765]

theorem rawRowCheck18766 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0 = rawRow18766 := by decide +kernel

theorem rowCheck18766 : row18766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18766 := by decide +kernel

theorem rowEval18766 (x : Key → ℝ) : Integer.Sparse.eval row18766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18766, Integer.Sparse.eval_collectBalanced, rawRowCheck18766]

theorem rawRowCheck18767 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0 = rawRow18767 := by decide +kernel

theorem rowCheck18767 : row18767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18767 := by decide +kernel

theorem rowEval18767 (x : Key → ℝ) : Integer.Sparse.eval row18767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18767, Integer.Sparse.eval_collectBalanced, rawRowCheck18767]

theorem rawRowCheck18768 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0 = rawRow18768 := by decide +kernel

theorem rowCheck18768 : row18768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18768 := by decide +kernel

theorem rowEval18768 (x : Key → ℝ) : Integer.Sparse.eval row18768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18768, Integer.Sparse.eval_collectBalanced, rawRowCheck18768]

theorem rawRowCheck18769 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0 = rawRow18769 := by decide +kernel

theorem rowCheck18769 : row18769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18769 := by decide +kernel

theorem rowEval18769 (x : Key → ℝ) : Integer.Sparse.eval row18769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18769, Integer.Sparse.eval_collectBalanced, rawRowCheck18769]

theorem rawRowCheck18770 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0 = rawRow18770 := by decide +kernel

theorem rowCheck18770 : row18770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18770 := by decide +kernel

theorem rowEval18770 (x : Key → ℝ) : Integer.Sparse.eval row18770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18770, Integer.Sparse.eval_collectBalanced, rawRowCheck18770]

theorem rawRowCheck18771 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18771 := by decide +kernel

theorem rowCheck18771 : row18771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18771 := by decide +kernel

theorem rowEval18771 (x : Key → ℝ) : Integer.Sparse.eval row18771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18771, Integer.Sparse.eval_collectBalanced, rawRowCheck18771]

theorem rawRowCheck18772 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18772 := by decide +kernel

theorem rowCheck18772 : row18772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18772 := by decide +kernel

theorem rowEval18772 (x : Key → ℝ) : Integer.Sparse.eval row18772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18772, Integer.Sparse.eval_collectBalanced, rawRowCheck18772]

theorem rawRowCheck18773 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18773 := by decide +kernel

theorem rowCheck18773 : row18773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18773 := by decide +kernel

theorem rowEval18773 (x : Key → ℝ) : Integer.Sparse.eval row18773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18773, Integer.Sparse.eval_collectBalanced, rawRowCheck18773]

theorem rawRowCheck18774 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18774 := by decide +kernel

theorem rowCheck18774 : row18774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18774 := by decide +kernel

theorem rowEval18774 (x : Key → ℝ) : Integer.Sparse.eval row18774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18774, Integer.Sparse.eval_collectBalanced, rawRowCheck18774]

theorem rawRowCheck18775 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18775 := by decide +kernel

theorem rowCheck18775 : row18775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18775 := by decide +kernel

theorem rowEval18775 (x : Key → ℝ) : Integer.Sparse.eval row18775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18775, Integer.Sparse.eval_collectBalanced, rawRowCheck18775]

theorem rawRowCheck18776 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18776 := by decide +kernel

theorem rowCheck18776 : row18776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18776 := by decide +kernel

theorem rowEval18776 (x : Key → ℝ) : Integer.Sparse.eval row18776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18776, Integer.Sparse.eval_collectBalanced, rawRowCheck18776]

theorem rawRowCheck18777 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0 = rawRow18777 := by decide +kernel

theorem rowCheck18777 : row18777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18777 := by decide +kernel

theorem rowEval18777 (x : Key → ℝ) : Integer.Sparse.eval row18777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18777, Integer.Sparse.eval_collectBalanced, rawRowCheck18777]

theorem rawRowCheck18778 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0 = rawRow18778 := by decide +kernel

theorem rowCheck18778 : row18778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18778 := by decide +kernel

theorem rowEval18778 (x : Key → ℝ) : Integer.Sparse.eval row18778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18778, Integer.Sparse.eval_collectBalanced, rawRowCheck18778]

theorem rawRowCheck18779 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0 = rawRow18779 := by decide +kernel

theorem rowCheck18779 : row18779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18779 := by decide +kernel

theorem rowEval18779 (x : Key → ℝ) : Integer.Sparse.eval row18779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18779, Integer.Sparse.eval_collectBalanced, rawRowCheck18779]

theorem rawRowCheck18780 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0 = rawRow18780 := by decide +kernel

theorem rowCheck18780 : row18780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18780 := by decide +kernel

theorem rowEval18780 (x : Key → ℝ) : Integer.Sparse.eval row18780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18780, Integer.Sparse.eval_collectBalanced, rawRowCheck18780]

theorem rawRowCheck18781 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0 = rawRow18781 := by decide +kernel

theorem rowCheck18781 : row18781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18781 := by decide +kernel

theorem rowEval18781 (x : Key → ℝ) : Integer.Sparse.eval row18781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18781, Integer.Sparse.eval_collectBalanced, rawRowCheck18781]

theorem rawRowCheck18782 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0 = rawRow18782 := by decide +kernel

theorem rowCheck18782 : row18782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18782 := by decide +kernel

theorem rowEval18782 (x : Key → ℝ) : Integer.Sparse.eval row18782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18782, Integer.Sparse.eval_collectBalanced, rawRowCheck18782]

theorem rawRowCheck18783 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0 = rawRow18783 := by decide +kernel

theorem rowCheck18783 : row18783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18783 := by decide +kernel

theorem rowEval18783 (x : Key → ℝ) : Integer.Sparse.eval row18783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18783, Integer.Sparse.eval_collectBalanced, rawRowCheck18783]

theorem rawRowCheck18784 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0 = rawRow18784 := by decide +kernel

theorem rowCheck18784 : row18784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18784 := by decide +kernel

theorem rowEval18784 (x : Key → ℝ) : Integer.Sparse.eval row18784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18784, Integer.Sparse.eval_collectBalanced, rawRowCheck18784]

theorem rawRowCheck18785 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0 = rawRow18785 := by decide +kernel

theorem rowCheck18785 : row18785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18785 := by decide +kernel

theorem rowEval18785 (x : Key → ℝ) : Integer.Sparse.eval row18785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18785, Integer.Sparse.eval_collectBalanced, rawRowCheck18785]

theorem rawRowCheck18786 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0 = rawRow18786 := by decide +kernel

theorem rowCheck18786 : row18786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18786 := by decide +kernel

theorem rowEval18786 (x : Key → ℝ) : Integer.Sparse.eval row18786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18786, Integer.Sparse.eval_collectBalanced, rawRowCheck18786]

theorem rawRowCheck18787 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0 = rawRow18787 := by decide +kernel

theorem rowCheck18787 : row18787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18787 := by decide +kernel

theorem rowEval18787 (x : Key → ℝ) : Integer.Sparse.eval row18787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18787, Integer.Sparse.eval_collectBalanced, rawRowCheck18787]

theorem rawRowCheck18788 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0 = rawRow18788 := by decide +kernel

theorem rowCheck18788 : row18788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18788 := by decide +kernel

theorem rowEval18788 (x : Key → ℝ) : Integer.Sparse.eval row18788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form0) x := by
  rw [rowCheck18788, Integer.Sparse.eval_collectBalanced, rawRowCheck18788]

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

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18659 x
  · exact rowEval18660 x
  · exact rowEval18661 x
  · exact rowEval18662 x
  · exact rowEval18663 x
  · exact rowEval18664 x
  · exact rowEval18665 x
  · exact rowEval18666 x
  · exact rowEval18667 x
  · exact rowEval18668 x
  · exact rowEval18669 x
  · exact rowEval18670 x
  · exact rowEval18671 x
  · exact rowEval18672 x
  · exact rowEval18673 x
  · exact rowEval18674 x
  · exact rowEval18675 x
  · exact rowEval18676 x
  · exact rowEval18677 x
  · exact rowEval18678 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18759 x
  · exact rowEval18760 x
  · exact rowEval18761 x
  · exact rowEval18762 x
  · exact rowEval18763 x
  · exact rowEval18764 x
  · exact rowEval18765 x
  · exact rowEval18766 x
  · exact rowEval18767 x
  · exact rowEval18768 x
  · exact rowEval18769 x
  · exact rowEval18770 x
  · exact rowEval18771 x
  · exact rowEval18772 x
  · exact rowEval18773 x
  · exact rowEval18774 x
  · exact rowEval18775 x
  · exact rowEval18776 x
  · exact rowEval18777 x
  · exact rowEval18778 x
  · exact rowEval18779 x
  · exact rowEval18780 x
  · exact rowEval18781 x
  · exact rowEval18782 x
  · exact rowEval18783 x
  · exact rowEval18784 x
  · exact rowEval18785 x
  · exact rowEval18786 x
  · exact rowEval18787 x
  · exact rowEval18788 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

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

theorem rawRowCheck19079 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19079 := by decide +kernel

theorem rowCheck19079 : row19079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19079 := by decide +kernel

theorem rowEval19079 (x : Key → ℝ) : Integer.Sparse.eval row19079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19079, Integer.Sparse.eval_collectBalanced, rawRowCheck19079]

theorem rawRowCheck19080 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19080 := by decide +kernel

theorem rowCheck19080 : row19080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19080 := by decide +kernel

theorem rowEval19080 (x : Key → ℝ) : Integer.Sparse.eval row19080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19080, Integer.Sparse.eval_collectBalanced, rawRowCheck19080]

theorem rawRowCheck19081 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19081 := by decide +kernel

theorem rowCheck19081 : row19081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19081 := by decide +kernel

theorem rowEval19081 (x : Key → ℝ) : Integer.Sparse.eval row19081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19081, Integer.Sparse.eval_collectBalanced, rawRowCheck19081]

theorem rawRowCheck19082 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19082 := by decide +kernel

theorem rowCheck19082 : row19082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19082 := by decide +kernel

theorem rowEval19082 (x : Key → ℝ) : Integer.Sparse.eval row19082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19082, Integer.Sparse.eval_collectBalanced, rawRowCheck19082]

theorem rawRowCheck19083 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19083 := by decide +kernel

theorem rowCheck19083 : row19083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19083 := by decide +kernel

theorem rowEval19083 (x : Key → ℝ) : Integer.Sparse.eval row19083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19083, Integer.Sparse.eval_collectBalanced, rawRowCheck19083]

theorem rawRowCheck19084 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19084 := by decide +kernel

theorem rowCheck19084 : row19084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19084 := by decide +kernel

theorem rowEval19084 (x : Key → ℝ) : Integer.Sparse.eval row19084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19084, Integer.Sparse.eval_collectBalanced, rawRowCheck19084]

theorem rawRowCheck19085 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19085 := by decide +kernel

theorem rowCheck19085 : row19085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19085 := by decide +kernel

theorem rowEval19085 (x : Key → ℝ) : Integer.Sparse.eval row19085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19085, Integer.Sparse.eval_collectBalanced, rawRowCheck19085]

theorem rawRowCheck19086 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19086 := by decide +kernel

theorem rowCheck19086 : row19086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19086 := by decide +kernel

theorem rowEval19086 (x : Key → ℝ) : Integer.Sparse.eval row19086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19086, Integer.Sparse.eval_collectBalanced, rawRowCheck19086]

theorem rawRowCheck19087 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19087 := by decide +kernel

theorem rowCheck19087 : row19087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19087 := by decide +kernel

theorem rowEval19087 (x : Key → ℝ) : Integer.Sparse.eval row19087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19087, Integer.Sparse.eval_collectBalanced, rawRowCheck19087]

theorem rawRowCheck19088 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19088 := by decide +kernel

theorem rowCheck19088 : row19088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19088 := by decide +kernel

theorem rowEval19088 (x : Key → ℝ) : Integer.Sparse.eval row19088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19088, Integer.Sparse.eval_collectBalanced, rawRowCheck19088]

theorem rawRowCheck19089 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19089 := by decide +kernel

theorem rowCheck19089 : row19089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19089 := by decide +kernel

theorem rowEval19089 (x : Key → ℝ) : Integer.Sparse.eval row19089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19089, Integer.Sparse.eval_collectBalanced, rawRowCheck19089]

theorem rawRowCheck19090 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19090 := by decide +kernel

theorem rowCheck19090 : row19090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19090 := by decide +kernel

theorem rowEval19090 (x : Key → ℝ) : Integer.Sparse.eval row19090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19090, Integer.Sparse.eval_collectBalanced, rawRowCheck19090]

theorem rawRowCheck19091 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19091 := by decide +kernel

theorem rowCheck19091 : row19091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19091 := by decide +kernel

theorem rowEval19091 (x : Key → ℝ) : Integer.Sparse.eval row19091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19091, Integer.Sparse.eval_collectBalanced, rawRowCheck19091]

theorem rawRowCheck19092 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19092 := by decide +kernel

theorem rowCheck19092 : row19092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19092 := by decide +kernel

theorem rowEval19092 (x : Key → ℝ) : Integer.Sparse.eval row19092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19092, Integer.Sparse.eval_collectBalanced, rawRowCheck19092]

theorem rawRowCheck19093 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19093 := by decide +kernel

theorem rowCheck19093 : row19093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19093 := by decide +kernel

theorem rowEval19093 (x : Key → ℝ) : Integer.Sparse.eval row19093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19093, Integer.Sparse.eval_collectBalanced, rawRowCheck19093]

theorem rawRowCheck19094 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19094 := by decide +kernel

theorem rowCheck19094 : row19094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19094 := by decide +kernel

theorem rowEval19094 (x : Key → ℝ) : Integer.Sparse.eval row19094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19094, Integer.Sparse.eval_collectBalanced, rawRowCheck19094]

theorem rawRowCheck19095 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19095 := by decide +kernel

theorem rowCheck19095 : row19095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19095 := by decide +kernel

theorem rowEval19095 (x : Key → ℝ) : Integer.Sparse.eval row19095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19095, Integer.Sparse.eval_collectBalanced, rawRowCheck19095]

theorem rawRowCheck19096 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19096 := by decide +kernel

theorem rowCheck19096 : row19096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19096 := by decide +kernel

theorem rowEval19096 (x : Key → ℝ) : Integer.Sparse.eval row19096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19096, Integer.Sparse.eval_collectBalanced, rawRowCheck19096]

theorem rawRowCheck19097 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19097 := by decide +kernel

theorem rowCheck19097 : row19097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19097 := by decide +kernel

theorem rowEval19097 (x : Key → ℝ) : Integer.Sparse.eval row19097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19097, Integer.Sparse.eval_collectBalanced, rawRowCheck19097]

theorem rawRowCheck19098 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19098 := by decide +kernel

theorem rowCheck19098 : row19098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19098 := by decide +kernel

theorem rowEval19098 (x : Key → ℝ) : Integer.Sparse.eval row19098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19098, Integer.Sparse.eval_collectBalanced, rawRowCheck19098]

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

theorem rawRowCheck19284 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19284 := by decide +kernel

theorem rowCheck19284 : row19284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19284 := by decide +kernel

theorem rowEval19284 (x : Key → ℝ) : Integer.Sparse.eval row19284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19284, Integer.Sparse.eval_collectBalanced, rawRowCheck19284]

theorem rawRowCheck19285 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19285 := by decide +kernel

theorem rowCheck19285 : row19285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19285 := by decide +kernel

theorem rowEval19285 (x : Key → ℝ) : Integer.Sparse.eval row19285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19285, Integer.Sparse.eval_collectBalanced, rawRowCheck19285]

theorem rawRowCheck19286 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19286 := by decide +kernel

theorem rowCheck19286 : row19286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19286 := by decide +kernel

theorem rowEval19286 (x : Key → ℝ) : Integer.Sparse.eval row19286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19286, Integer.Sparse.eval_collectBalanced, rawRowCheck19286]

theorem rawRowCheck19287 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19287 := by decide +kernel

theorem rowCheck19287 : row19287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19287 := by decide +kernel

theorem rowEval19287 (x : Key → ℝ) : Integer.Sparse.eval row19287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19287, Integer.Sparse.eval_collectBalanced, rawRowCheck19287]

theorem rawRowCheck19288 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19288 := by decide +kernel

theorem rowCheck19288 : row19288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19288 := by decide +kernel

theorem rowEval19288 (x : Key → ℝ) : Integer.Sparse.eval row19288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19288, Integer.Sparse.eval_collectBalanced, rawRowCheck19288]

theorem rawRowCheck19289 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19289 := by decide +kernel

theorem rowCheck19289 : row19289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19289 := by decide +kernel

theorem rowEval19289 (x : Key → ℝ) : Integer.Sparse.eval row19289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19289, Integer.Sparse.eval_collectBalanced, rawRowCheck19289]

theorem rawRowCheck19290 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19290 := by decide +kernel

theorem rowCheck19290 : row19290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19290 := by decide +kernel

theorem rowEval19290 (x : Key → ℝ) : Integer.Sparse.eval row19290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19290, Integer.Sparse.eval_collectBalanced, rawRowCheck19290]

theorem rawRowCheck19291 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19291 := by decide +kernel

theorem rowCheck19291 : row19291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19291 := by decide +kernel

theorem rowEval19291 (x : Key → ℝ) : Integer.Sparse.eval row19291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19291, Integer.Sparse.eval_collectBalanced, rawRowCheck19291]

theorem rawRowCheck19292 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19292 := by decide +kernel

theorem rowCheck19292 : row19292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19292 := by decide +kernel

theorem rowEval19292 (x : Key → ℝ) : Integer.Sparse.eval row19292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19292, Integer.Sparse.eval_collectBalanced, rawRowCheck19292]

theorem rawRowCheck19293 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0 = rawRow19293 := by decide +kernel

theorem rowCheck19293 : row19293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19293 := by decide +kernel

theorem rowEval19293 (x : Key → ℝ) : Integer.Sparse.eval row19293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19293, Integer.Sparse.eval_collectBalanced, rawRowCheck19293]

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

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19079 x
  · exact rowEval19080 x
  · exact rowEval19081 x
  · exact rowEval19082 x
  · exact rowEval19083 x
  · exact rowEval19084 x
  · exact rowEval19085 x
  · exact rowEval19086 x
  · exact rowEval19087 x
  · exact rowEval19088 x
  · exact rowEval19089 x
  · exact rowEval19090 x
  · exact rowEval19091 x
  · exact rowEval19092 x
  · exact rowEval19093 x
  · exact rowEval19094 x
  · exact rowEval19095 x
  · exact rowEval19096 x
  · exact rowEval19097 x
  · exact rowEval19098 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

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

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19284 x
  · exact rowEval19285 x
  · exact rowEval19286 x
  · exact rowEval19287 x
  · exact rowEval19288 x
  · exact rowEval19289 x
  · exact rowEval19290 x
  · exact rowEval19291 x
  · exact rowEval19292 x
  · exact rowEval19293 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

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

theorem entryEvalRow0_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 0).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval0_0 B hB
  · exact (entryEval1_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval2_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0_e_oai
