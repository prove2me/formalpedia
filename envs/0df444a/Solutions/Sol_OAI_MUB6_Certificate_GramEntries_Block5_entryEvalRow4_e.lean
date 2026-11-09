-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:51:53.92489+00:00
-- url     : https://prove2.me/submissions/59e2e405-c4a6-41f0-a87e-e2f6b28c4d98

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
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_4_e

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

theorem rawRowCheck19328 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19328 := by decide +kernel

theorem rowCheck19328 : row19328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19328 := by decide +kernel

theorem rowEval19328 (x : Key → ℝ) : Integer.Sparse.eval row19328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19328, Integer.Sparse.eval_collectBalanced, rawRowCheck19328]

theorem rawRowCheck19329 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19329 := by decide +kernel

theorem rowCheck19329 : row19329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19329 := by decide +kernel

theorem rowEval19329 (x : Key → ℝ) : Integer.Sparse.eval row19329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19329, Integer.Sparse.eval_collectBalanced, rawRowCheck19329]

theorem rawRowCheck19330 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19330 := by decide +kernel

theorem rowCheck19330 : row19330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19330 := by decide +kernel

theorem rowEval19330 (x : Key → ℝ) : Integer.Sparse.eval row19330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19330, Integer.Sparse.eval_collectBalanced, rawRowCheck19330]

theorem rawRowCheck19331 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4 = rawRow19331 := by decide +kernel

theorem rowCheck19331 : row19331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19331 := by decide +kernel

theorem rowEval19331 (x : Key → ℝ) : Integer.Sparse.eval row19331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19331, Integer.Sparse.eval_collectBalanced, rawRowCheck19331]

theorem rawRowCheck19332 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4 = rawRow19332 := by decide +kernel

theorem rowCheck19332 : row19332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19332 := by decide +kernel

theorem rowEval19332 (x : Key → ℝ) : Integer.Sparse.eval row19332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19332, Integer.Sparse.eval_collectBalanced, rawRowCheck19332]

theorem rawRowCheck19333 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4 = rawRow19333 := by decide +kernel

theorem rowCheck19333 : row19333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19333 := by decide +kernel

theorem rowEval19333 (x : Key → ℝ) : Integer.Sparse.eval row19333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19333, Integer.Sparse.eval_collectBalanced, rawRowCheck19333]

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

theorem rawRowCheck19464 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19464 := by decide +kernel

theorem rowCheck19464 : row19464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19464 := by decide +kernel

theorem rowEval19464 (x : Key → ℝ) : Integer.Sparse.eval row19464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19464, Integer.Sparse.eval_collectBalanced, rawRowCheck19464]

theorem rawRowCheck19465 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19465 := by decide +kernel

theorem rowCheck19465 : row19465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19465 := by decide +kernel

theorem rowEval19465 (x : Key → ℝ) : Integer.Sparse.eval row19465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19465, Integer.Sparse.eval_collectBalanced, rawRowCheck19465]

theorem rawRowCheck19466 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19466 := by decide +kernel

theorem rowCheck19466 : row19466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19466 := by decide +kernel

theorem rowEval19466 (x : Key → ℝ) : Integer.Sparse.eval row19466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19466, Integer.Sparse.eval_collectBalanced, rawRowCheck19466]

theorem rawRowCheck19467 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19467 := by decide +kernel

theorem rowCheck19467 : row19467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19467 := by decide +kernel

theorem rowEval19467 (x : Key → ℝ) : Integer.Sparse.eval row19467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19467, Integer.Sparse.eval_collectBalanced, rawRowCheck19467]

theorem rawRowCheck19468 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19468 := by decide +kernel

theorem rowCheck19468 : row19468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19468 := by decide +kernel

theorem rowEval19468 (x : Key → ℝ) : Integer.Sparse.eval row19468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19468, Integer.Sparse.eval_collectBalanced, rawRowCheck19468]

theorem rawRowCheck19469 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19469 := by decide +kernel

theorem rowCheck19469 : row19469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19469 := by decide +kernel

theorem rowEval19469 (x : Key → ℝ) : Integer.Sparse.eval row19469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19469, Integer.Sparse.eval_collectBalanced, rawRowCheck19469]

theorem rawRowCheck19470 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19470 := by decide +kernel

theorem rowCheck19470 : row19470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19470 := by decide +kernel

theorem rowEval19470 (x : Key → ℝ) : Integer.Sparse.eval row19470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19470, Integer.Sparse.eval_collectBalanced, rawRowCheck19470]

theorem rawRowCheck19471 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4 = rawRow19471 := by decide +kernel

theorem rowCheck19471 : row19471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19471 := by decide +kernel

theorem rowEval19471 (x : Key → ℝ) : Integer.Sparse.eval row19471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19471, Integer.Sparse.eval_collectBalanced, rawRowCheck19471]

theorem rawRowCheck19472 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4 = rawRow19472 := by decide +kernel

theorem rowCheck19472 : row19472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19472 := by decide +kernel

theorem rowEval19472 (x : Key → ℝ) : Integer.Sparse.eval row19472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19472, Integer.Sparse.eval_collectBalanced, rawRowCheck19472]

theorem rawRowCheck19473 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4 = rawRow19473 := by decide +kernel

theorem rowCheck19473 : row19473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19473 := by decide +kernel

theorem rowEval19473 (x : Key → ℝ) : Integer.Sparse.eval row19473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19473, Integer.Sparse.eval_collectBalanced, rawRowCheck19473]

theorem rawRowCheck19474 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4 = rawRow19474 := by decide +kernel

theorem rowCheck19474 : row19474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19474 := by decide +kernel

theorem rowEval19474 (x : Key → ℝ) : Integer.Sparse.eval row19474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19474, Integer.Sparse.eval_collectBalanced, rawRowCheck19474]

theorem rawRowCheck19475 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4 = rawRow19475 := by decide +kernel

theorem rowCheck19475 : row19475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19475 := by decide +kernel

theorem rowEval19475 (x : Key → ℝ) : Integer.Sparse.eval row19475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19475, Integer.Sparse.eval_collectBalanced, rawRowCheck19475]

theorem rawRowCheck19476 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4 = rawRow19476 := by decide +kernel

theorem rowCheck19476 : row19476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19476 := by decide +kernel

theorem rowEval19476 (x : Key → ℝ) : Integer.Sparse.eval row19476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19476, Integer.Sparse.eval_collectBalanced, rawRowCheck19476]

theorem rawRowCheck19477 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19477 := by decide +kernel

theorem rowCheck19477 : row19477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19477 := by decide +kernel

theorem rowEval19477 (x : Key → ℝ) : Integer.Sparse.eval row19477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19477, Integer.Sparse.eval_collectBalanced, rawRowCheck19477]

theorem rawRowCheck19478 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19478 := by decide +kernel

theorem rowCheck19478 : row19478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19478 := by decide +kernel

theorem rowEval19478 (x : Key → ℝ) : Integer.Sparse.eval row19478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19478, Integer.Sparse.eval_collectBalanced, rawRowCheck19478]

theorem rawRowCheck19479 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19479 := by decide +kernel

theorem rowCheck19479 : row19479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19479 := by decide +kernel

theorem rowEval19479 (x : Key → ℝ) : Integer.Sparse.eval row19479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19479, Integer.Sparse.eval_collectBalanced, rawRowCheck19479]

theorem rawRowCheck19480 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19480 := by decide +kernel

theorem rowCheck19480 : row19480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19480 := by decide +kernel

theorem rowEval19480 (x : Key → ℝ) : Integer.Sparse.eval row19480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19480, Integer.Sparse.eval_collectBalanced, rawRowCheck19480]

theorem rawRowCheck19481 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19481 := by decide +kernel

theorem rowCheck19481 : row19481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19481 := by decide +kernel

theorem rowEval19481 (x : Key → ℝ) : Integer.Sparse.eval row19481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19481, Integer.Sparse.eval_collectBalanced, rawRowCheck19481]

theorem rawRowCheck19482 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19482 := by decide +kernel

theorem rowCheck19482 : row19482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19482 := by decide +kernel

theorem rowEval19482 (x : Key → ℝ) : Integer.Sparse.eval row19482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19482, Integer.Sparse.eval_collectBalanced, rawRowCheck19482]

theorem rawRowCheck19483 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19483 := by decide +kernel

theorem rowCheck19483 : row19483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19483 := by decide +kernel

theorem rowEval19483 (x : Key → ℝ) : Integer.Sparse.eval row19483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19483, Integer.Sparse.eval_collectBalanced, rawRowCheck19483]

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

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block5.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form10.terms k).tag (GramFunctions.Block5.form10.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19464 x
  · exact rowEval19465 x
  · exact rowEval19466 x
  · exact rowEval19467 x
  · exact rowEval19468 x
  · exact rowEval19469 x
  · exact rowEval19470 x
  · exact rowEval19471 x
  · exact rowEval19472 x
  · exact rowEval19473 x
  · exact rowEval19474 x
  · exact rowEval19475 x
  · exact rowEval19476 x
  · exact rowEval19477 x
  · exact rowEval19478 x
  · exact rowEval19479 x
  · exact rowEval19480 x
  · exact rowEval19481 x
  · exact rowEval19482 x
  · exact rowEval19483 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block5.form10.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form10 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

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

theorem rawRowCheck18679 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18679 := by decide +kernel

theorem rowCheck18679 : row18679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18679 := by decide +kernel

theorem rowEval18679 (x : Key → ℝ) : Integer.Sparse.eval row18679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18679, Integer.Sparse.eval_collectBalanced, rawRowCheck18679]

theorem rawRowCheck18680 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18680 := by decide +kernel

theorem rowCheck18680 : row18680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18680 := by decide +kernel

theorem rowEval18680 (x : Key → ℝ) : Integer.Sparse.eval row18680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18680, Integer.Sparse.eval_collectBalanced, rawRowCheck18680]

theorem rawRowCheck18681 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18681 := by decide +kernel

theorem rowCheck18681 : row18681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18681 := by decide +kernel

theorem rowEval18681 (x : Key → ℝ) : Integer.Sparse.eval row18681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18681, Integer.Sparse.eval_collectBalanced, rawRowCheck18681]

theorem rawRowCheck18682 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18682 := by decide +kernel

theorem rowCheck18682 : row18682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18682 := by decide +kernel

theorem rowEval18682 (x : Key → ℝ) : Integer.Sparse.eval row18682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18682, Integer.Sparse.eval_collectBalanced, rawRowCheck18682]

theorem rawRowCheck18683 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1 = rawRow18683 := by decide +kernel

theorem rowCheck18683 : row18683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18683 := by decide +kernel

theorem rowEval18683 (x : Key → ℝ) : Integer.Sparse.eval row18683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18683, Integer.Sparse.eval_collectBalanced, rawRowCheck18683]

theorem rawRowCheck18684 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1 = rawRow18684 := by decide +kernel

theorem rowCheck18684 : row18684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18684 := by decide +kernel

theorem rowEval18684 (x : Key → ℝ) : Integer.Sparse.eval row18684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18684, Integer.Sparse.eval_collectBalanced, rawRowCheck18684]

theorem rawRowCheck18685 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1 = rawRow18685 := by decide +kernel

theorem rowCheck18685 : row18685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18685 := by decide +kernel

theorem rowEval18685 (x : Key → ℝ) : Integer.Sparse.eval row18685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18685, Integer.Sparse.eval_collectBalanced, rawRowCheck18685]

theorem rawRowCheck18686 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1 = rawRow18686 := by decide +kernel

theorem rowCheck18686 : row18686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18686 := by decide +kernel

theorem rowEval18686 (x : Key → ℝ) : Integer.Sparse.eval row18686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18686, Integer.Sparse.eval_collectBalanced, rawRowCheck18686]

theorem rawRowCheck18687 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1 = rawRow18687 := by decide +kernel

theorem rowCheck18687 : row18687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18687 := by decide +kernel

theorem rowEval18687 (x : Key → ℝ) : Integer.Sparse.eval row18687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18687, Integer.Sparse.eval_collectBalanced, rawRowCheck18687]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck18688 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1 = rawRow18688 := by decide +kernel

theorem rowCheck18688 : row18688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18688 := by decide +kernel

theorem rowEval18688 (x : Key → ℝ) : Integer.Sparse.eval row18688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck18688, Integer.Sparse.eval_collectBalanced, rawRowCheck18688]

theorem rawRowCheck18689 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1 = rawRow18689 := by decide +kernel

theorem rowCheck18689 : row18689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18689 := by decide +kernel

theorem rowEval18689 (x : Key → ℝ) : Integer.Sparse.eval row18689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18689, Integer.Sparse.eval_collectBalanced, rawRowCheck18689]

theorem rawRowCheck18690 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1 = rawRow18690 := by decide +kernel

theorem rowCheck18690 : row18690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18690 := by decide +kernel

theorem rowEval18690 (x : Key → ℝ) : Integer.Sparse.eval row18690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18690, Integer.Sparse.eval_collectBalanced, rawRowCheck18690]

theorem rawRowCheck18691 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1 = rawRow18691 := by decide +kernel

theorem rowCheck18691 : row18691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18691 := by decide +kernel

theorem rowEval18691 (x : Key → ℝ) : Integer.Sparse.eval row18691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18691, Integer.Sparse.eval_collectBalanced, rawRowCheck18691]

theorem rawRowCheck18692 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18692 := by decide +kernel

theorem rowCheck18692 : row18692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18692 := by decide +kernel

theorem rowEval18692 (x : Key → ℝ) : Integer.Sparse.eval row18692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18692, Integer.Sparse.eval_collectBalanced, rawRowCheck18692]

theorem rawRowCheck18693 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18693 := by decide +kernel

theorem rowCheck18693 : row18693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18693 := by decide +kernel

theorem rowEval18693 (x : Key → ℝ) : Integer.Sparse.eval row18693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18693, Integer.Sparse.eval_collectBalanced, rawRowCheck18693]

theorem rawRowCheck18694 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18694 := by decide +kernel

theorem rowCheck18694 : row18694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18694 := by decide +kernel

theorem rowEval18694 (x : Key → ℝ) : Integer.Sparse.eval row18694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18694, Integer.Sparse.eval_collectBalanced, rawRowCheck18694]

theorem rawRowCheck18695 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1 = rawRow18695 := by decide +kernel

theorem rowCheck18695 : row18695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18695 := by decide +kernel

theorem rowEval18695 (x : Key → ℝ) : Integer.Sparse.eval row18695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18695, Integer.Sparse.eval_collectBalanced, rawRowCheck18695]

theorem rawRowCheck18696 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1 = rawRow18696 := by decide +kernel

theorem rowCheck18696 : row18696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18696 := by decide +kernel

theorem rowEval18696 (x : Key → ℝ) : Integer.Sparse.eval row18696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18696, Integer.Sparse.eval_collectBalanced, rawRowCheck18696]

theorem rawRowCheck18697 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1 = rawRow18697 := by decide +kernel

theorem rowCheck18697 : row18697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18697 := by decide +kernel

theorem rowEval18697 (x : Key → ℝ) : Integer.Sparse.eval row18697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck18697, Integer.Sparse.eval_collectBalanced, rawRowCheck18697]

theorem rawRowCheck18698 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1 = rawRow18698 := by decide +kernel

theorem rowCheck18698 : row18698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18698 := by decide +kernel

theorem rowEval18698 (x : Key → ℝ) : Integer.Sparse.eval row18698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form1) x := by
  rw [rowCheck18698, Integer.Sparse.eval_collectBalanced, rawRowCheck18698]

theorem rawRowCheck18699 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18699 := by decide +kernel

theorem rowCheck18699 : row18699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18699 := by decide +kernel

theorem rowEval18699 (x : Key → ℝ) : Integer.Sparse.eval row18699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18699, Integer.Sparse.eval_collectBalanced, rawRowCheck18699]

theorem rawRowCheck18700 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18700 := by decide +kernel

theorem rowCheck18700 : row18700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18700 := by decide +kernel

theorem rowEval18700 (x : Key → ℝ) : Integer.Sparse.eval row18700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18700, Integer.Sparse.eval_collectBalanced, rawRowCheck18700]

theorem rawRowCheck18701 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18701 := by decide +kernel

theorem rowCheck18701 : row18701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18701 := by decide +kernel

theorem rowEval18701 (x : Key → ℝ) : Integer.Sparse.eval row18701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18701, Integer.Sparse.eval_collectBalanced, rawRowCheck18701]

theorem rawRowCheck18702 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18702 := by decide +kernel

theorem rowCheck18702 : row18702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18702 := by decide +kernel

theorem rowEval18702 (x : Key → ℝ) : Integer.Sparse.eval row18702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18702, Integer.Sparse.eval_collectBalanced, rawRowCheck18702]

theorem rawRowCheck18703 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form2 = rawRow18703 := by decide +kernel

theorem rowCheck18703 : row18703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18703 := by decide +kernel

theorem rowEval18703 (x : Key → ℝ) : Integer.Sparse.eval row18703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18703, Integer.Sparse.eval_collectBalanced, rawRowCheck18703]

theorem rawRowCheck18704 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form2 = rawRow18704 := by decide +kernel

theorem rowCheck18704 : row18704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18704 := by decide +kernel

theorem rowEval18704 (x : Key → ℝ) : Integer.Sparse.eval row18704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18704, Integer.Sparse.eval_collectBalanced, rawRowCheck18704]

theorem rawRowCheck18705 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form2 = rawRow18705 := by decide +kernel

theorem rowCheck18705 : row18705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18705 := by decide +kernel

theorem rowEval18705 (x : Key → ℝ) : Integer.Sparse.eval row18705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18705, Integer.Sparse.eval_collectBalanced, rawRowCheck18705]

theorem rawRowCheck18706 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form2 = rawRow18706 := by decide +kernel

theorem rowCheck18706 : row18706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18706 := by decide +kernel

theorem rowEval18706 (x : Key → ℝ) : Integer.Sparse.eval row18706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18706, Integer.Sparse.eval_collectBalanced, rawRowCheck18706]

theorem rawRowCheck18707 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form2 = rawRow18707 := by decide +kernel

theorem rowCheck18707 : row18707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18707 := by decide +kernel

theorem rowEval18707 (x : Key → ℝ) : Integer.Sparse.eval row18707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18707, Integer.Sparse.eval_collectBalanced, rawRowCheck18707]

theorem rawRowCheck18708 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form2 = rawRow18708 := by decide +kernel

theorem rowCheck18708 : row18708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18708 := by decide +kernel

theorem rowEval18708 (x : Key → ℝ) : Integer.Sparse.eval row18708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck18708, Integer.Sparse.eval_collectBalanced, rawRowCheck18708]

theorem rawRowCheck18709 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form2 = rawRow18709 := by decide +kernel

theorem rowCheck18709 : row18709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18709 := by decide +kernel

theorem rowEval18709 (x : Key → ℝ) : Integer.Sparse.eval row18709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18709, Integer.Sparse.eval_collectBalanced, rawRowCheck18709]

theorem rawRowCheck18710 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form2 = rawRow18710 := by decide +kernel

theorem rowCheck18710 : row18710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18710 := by decide +kernel

theorem rowEval18710 (x : Key → ℝ) : Integer.Sparse.eval row18710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18710, Integer.Sparse.eval_collectBalanced, rawRowCheck18710]

theorem rawRowCheck18711 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form2 = rawRow18711 := by decide +kernel

theorem rowCheck18711 : row18711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18711 := by decide +kernel

theorem rowEval18711 (x : Key → ℝ) : Integer.Sparse.eval row18711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18711, Integer.Sparse.eval_collectBalanced, rawRowCheck18711]

theorem rawRowCheck18712 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18712 := by decide +kernel

theorem rowCheck18712 : row18712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18712 := by decide +kernel

theorem rowEval18712 (x : Key → ℝ) : Integer.Sparse.eval row18712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18712, Integer.Sparse.eval_collectBalanced, rawRowCheck18712]

theorem rawRowCheck18713 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18713 := by decide +kernel

theorem rowCheck18713 : row18713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18713 := by decide +kernel

theorem rowEval18713 (x : Key → ℝ) : Integer.Sparse.eval row18713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18713, Integer.Sparse.eval_collectBalanced, rawRowCheck18713]

theorem rawRowCheck18714 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18714 := by decide +kernel

theorem rowCheck18714 : row18714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18714 := by decide +kernel

theorem rowEval18714 (x : Key → ℝ) : Integer.Sparse.eval row18714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18714, Integer.Sparse.eval_collectBalanced, rawRowCheck18714]

theorem rawRowCheck18715 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form2 = rawRow18715 := by decide +kernel

theorem rowCheck18715 : row18715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18715 := by decide +kernel

theorem rowEval18715 (x : Key → ℝ) : Integer.Sparse.eval row18715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18715, Integer.Sparse.eval_collectBalanced, rawRowCheck18715]

theorem rawRowCheck18716 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form2 = rawRow18716 := by decide +kernel

theorem rowCheck18716 : row18716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18716 := by decide +kernel

theorem rowEval18716 (x : Key → ℝ) : Integer.Sparse.eval row18716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18716, Integer.Sparse.eval_collectBalanced, rawRowCheck18716]

theorem rawRowCheck18717 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form2 = rawRow18717 := by decide +kernel

theorem rowCheck18717 : row18717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18717 := by decide +kernel

theorem rowEval18717 (x : Key → ℝ) : Integer.Sparse.eval row18717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck18717, Integer.Sparse.eval_collectBalanced, rawRowCheck18717]

theorem rawRowCheck18718 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form2 = rawRow18718 := by decide +kernel

theorem rowCheck18718 : row18718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18718 := by decide +kernel

theorem rowEval18718 (x : Key → ℝ) : Integer.Sparse.eval row18718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form2) x := by
  rw [rowCheck18718, Integer.Sparse.eval_collectBalanced, rawRowCheck18718]

theorem rawRowCheck18719 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18719 := by decide +kernel

theorem rowCheck18719 : row18719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18719 := by decide +kernel

theorem rowEval18719 (x : Key → ℝ) : Integer.Sparse.eval row18719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18719, Integer.Sparse.eval_collectBalanced, rawRowCheck18719]

theorem rawRowCheck18720 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18720 := by decide +kernel

theorem rowCheck18720 : row18720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18720 := by decide +kernel

theorem rowEval18720 (x : Key → ℝ) : Integer.Sparse.eval row18720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18720, Integer.Sparse.eval_collectBalanced, rawRowCheck18720]

theorem rawRowCheck18721 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18721 := by decide +kernel

theorem rowCheck18721 : row18721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18721 := by decide +kernel

theorem rowEval18721 (x : Key → ℝ) : Integer.Sparse.eval row18721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18721, Integer.Sparse.eval_collectBalanced, rawRowCheck18721]

theorem rawRowCheck18722 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18722 := by decide +kernel

theorem rowCheck18722 : row18722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18722 := by decide +kernel

theorem rowEval18722 (x : Key → ℝ) : Integer.Sparse.eval row18722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18722, Integer.Sparse.eval_collectBalanced, rawRowCheck18722]

theorem rawRowCheck18723 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3 = rawRow18723 := by decide +kernel

theorem rowCheck18723 : row18723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18723 := by decide +kernel

theorem rowEval18723 (x : Key → ℝ) : Integer.Sparse.eval row18723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18723, Integer.Sparse.eval_collectBalanced, rawRowCheck18723]

theorem rawRowCheck18724 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3 = rawRow18724 := by decide +kernel

theorem rowCheck18724 : row18724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18724 := by decide +kernel

theorem rowEval18724 (x : Key → ℝ) : Integer.Sparse.eval row18724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18724, Integer.Sparse.eval_collectBalanced, rawRowCheck18724]

theorem rawRowCheck18725 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3 = rawRow18725 := by decide +kernel

theorem rowCheck18725 : row18725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18725 := by decide +kernel

theorem rowEval18725 (x : Key → ℝ) : Integer.Sparse.eval row18725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18725, Integer.Sparse.eval_collectBalanced, rawRowCheck18725]

theorem rawRowCheck18726 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3 = rawRow18726 := by decide +kernel

theorem rowCheck18726 : row18726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18726 := by decide +kernel

theorem rowEval18726 (x : Key → ℝ) : Integer.Sparse.eval row18726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18726, Integer.Sparse.eval_collectBalanced, rawRowCheck18726]

theorem rawRowCheck18727 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3 = rawRow18727 := by decide +kernel

theorem rowCheck18727 : row18727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18727 := by decide +kernel

theorem rowEval18727 (x : Key → ℝ) : Integer.Sparse.eval row18727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18727, Integer.Sparse.eval_collectBalanced, rawRowCheck18727]

theorem rawRowCheck18728 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3 = rawRow18728 := by decide +kernel

theorem rowCheck18728 : row18728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18728 := by decide +kernel

theorem rowEval18728 (x : Key → ℝ) : Integer.Sparse.eval row18728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck18728, Integer.Sparse.eval_collectBalanced, rawRowCheck18728]

theorem rawRowCheck18729 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3 = rawRow18729 := by decide +kernel

theorem rowCheck18729 : row18729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18729 := by decide +kernel

theorem rowEval18729 (x : Key → ℝ) : Integer.Sparse.eval row18729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18729, Integer.Sparse.eval_collectBalanced, rawRowCheck18729]

theorem rawRowCheck18730 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3 = rawRow18730 := by decide +kernel

theorem rowCheck18730 : row18730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18730 := by decide +kernel

theorem rowEval18730 (x : Key → ℝ) : Integer.Sparse.eval row18730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18730, Integer.Sparse.eval_collectBalanced, rawRowCheck18730]

theorem rawRowCheck18731 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3 = rawRow18731 := by decide +kernel

theorem rowCheck18731 : row18731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18731 := by decide +kernel

theorem rowEval18731 (x : Key → ℝ) : Integer.Sparse.eval row18731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18731, Integer.Sparse.eval_collectBalanced, rawRowCheck18731]

theorem rawRowCheck18732 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18732 := by decide +kernel

theorem rowCheck18732 : row18732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18732 := by decide +kernel

theorem rowEval18732 (x : Key → ℝ) : Integer.Sparse.eval row18732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18732, Integer.Sparse.eval_collectBalanced, rawRowCheck18732]

theorem rawRowCheck18733 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18733 := by decide +kernel

theorem rowCheck18733 : row18733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18733 := by decide +kernel

theorem rowEval18733 (x : Key → ℝ) : Integer.Sparse.eval row18733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18733, Integer.Sparse.eval_collectBalanced, rawRowCheck18733]

theorem rawRowCheck18734 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18734 := by decide +kernel

theorem rowCheck18734 : row18734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18734 := by decide +kernel

theorem rowEval18734 (x : Key → ℝ) : Integer.Sparse.eval row18734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18734, Integer.Sparse.eval_collectBalanced, rawRowCheck18734]

theorem rawRowCheck18735 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3 = rawRow18735 := by decide +kernel

theorem rowCheck18735 : row18735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18735 := by decide +kernel

theorem rowEval18735 (x : Key → ℝ) : Integer.Sparse.eval row18735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18735, Integer.Sparse.eval_collectBalanced, rawRowCheck18735]

theorem rawRowCheck18736 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3 = rawRow18736 := by decide +kernel

theorem rowCheck18736 : row18736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18736 := by decide +kernel

theorem rowEval18736 (x : Key → ℝ) : Integer.Sparse.eval row18736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18736, Integer.Sparse.eval_collectBalanced, rawRowCheck18736]

theorem rawRowCheck18737 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3 = rawRow18737 := by decide +kernel

theorem rowCheck18737 : row18737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18737 := by decide +kernel

theorem rowEval18737 (x : Key → ℝ) : Integer.Sparse.eval row18737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck18737, Integer.Sparse.eval_collectBalanced, rawRowCheck18737]

theorem rawRowCheck18738 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3 = rawRow18738 := by decide +kernel

theorem rowCheck18738 : row18738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18738 := by decide +kernel

theorem rowEval18738 (x : Key → ℝ) : Integer.Sparse.eval row18738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form3) x := by
  rw [rowCheck18738, Integer.Sparse.eval_collectBalanced, rawRowCheck18738]

theorem rawRowCheck18739 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow18739 := by decide +kernel

theorem rowCheck18739 : row18739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18739 := by decide +kernel

theorem rowEval18739 (x : Key → ℝ) : Integer.Sparse.eval row18739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18739, Integer.Sparse.eval_collectBalanced, rawRowCheck18739]

theorem rawRowCheck18740 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow18740 := by decide +kernel

theorem rowCheck18740 : row18740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18740 := by decide +kernel

theorem rowEval18740 (x : Key → ℝ) : Integer.Sparse.eval row18740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18740, Integer.Sparse.eval_collectBalanced, rawRowCheck18740]

theorem rawRowCheck18741 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow18741 := by decide +kernel

theorem rowCheck18741 : row18741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18741 := by decide +kernel

theorem rowEval18741 (x : Key → ℝ) : Integer.Sparse.eval row18741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18741, Integer.Sparse.eval_collectBalanced, rawRowCheck18741]

theorem rawRowCheck18742 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow18742 := by decide +kernel

theorem rowCheck18742 : row18742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18742 := by decide +kernel

theorem rowEval18742 (x : Key → ℝ) : Integer.Sparse.eval row18742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18742, Integer.Sparse.eval_collectBalanced, rawRowCheck18742]

theorem rawRowCheck18743 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form4 = rawRow18743 := by decide +kernel

theorem rowCheck18743 : row18743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18743 := by decide +kernel

theorem rowEval18743 (x : Key → ℝ) : Integer.Sparse.eval row18743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18743, Integer.Sparse.eval_collectBalanced, rawRowCheck18743]

theorem rawRowCheck18744 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form4 = rawRow18744 := by decide +kernel

theorem rowCheck18744 : row18744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18744 := by decide +kernel

theorem rowEval18744 (x : Key → ℝ) : Integer.Sparse.eval row18744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18744, Integer.Sparse.eval_collectBalanced, rawRowCheck18744]

theorem rawRowCheck18745 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form4 = rawRow18745 := by decide +kernel

theorem rowCheck18745 : row18745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18745 := by decide +kernel

theorem rowEval18745 (x : Key → ℝ) : Integer.Sparse.eval row18745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18745, Integer.Sparse.eval_collectBalanced, rawRowCheck18745]

theorem rawRowCheck18746 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form4 = rawRow18746 := by decide +kernel

theorem rowCheck18746 : row18746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18746 := by decide +kernel

theorem rowEval18746 (x : Key → ℝ) : Integer.Sparse.eval row18746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18746, Integer.Sparse.eval_collectBalanced, rawRowCheck18746]

theorem rawRowCheck18747 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form4 = rawRow18747 := by decide +kernel

theorem rowCheck18747 : row18747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18747 := by decide +kernel

theorem rowEval18747 (x : Key → ℝ) : Integer.Sparse.eval row18747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18747, Integer.Sparse.eval_collectBalanced, rawRowCheck18747]

theorem rawRowCheck18748 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form4 = rawRow18748 := by decide +kernel

theorem rowCheck18748 : row18748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18748 := by decide +kernel

theorem rowEval18748 (x : Key → ℝ) : Integer.Sparse.eval row18748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck18748, Integer.Sparse.eval_collectBalanced, rawRowCheck18748]

theorem rawRowCheck18749 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form4 = rawRow18749 := by decide +kernel

theorem rowCheck18749 : row18749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18749 := by decide +kernel

theorem rowEval18749 (x : Key → ℝ) : Integer.Sparse.eval row18749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18749, Integer.Sparse.eval_collectBalanced, rawRowCheck18749]

theorem rawRowCheck18750 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form4 = rawRow18750 := by decide +kernel

theorem rowCheck18750 : row18750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18750 := by decide +kernel

theorem rowEval18750 (x : Key → ℝ) : Integer.Sparse.eval row18750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18750, Integer.Sparse.eval_collectBalanced, rawRowCheck18750]

theorem rawRowCheck18751 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form4 = rawRow18751 := by decide +kernel

theorem rowCheck18751 : row18751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18751 := by decide +kernel

theorem rowEval18751 (x : Key → ℝ) : Integer.Sparse.eval row18751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18751, Integer.Sparse.eval_collectBalanced, rawRowCheck18751]

theorem rawRowCheck18752 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18752 := by decide +kernel

theorem rowCheck18752 : row18752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18752 := by decide +kernel

theorem rowEval18752 (x : Key → ℝ) : Integer.Sparse.eval row18752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18752, Integer.Sparse.eval_collectBalanced, rawRowCheck18752]

theorem rawRowCheck18753 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18753 := by decide +kernel

theorem rowCheck18753 : row18753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18753 := by decide +kernel

theorem rowEval18753 (x : Key → ℝ) : Integer.Sparse.eval row18753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18753, Integer.Sparse.eval_collectBalanced, rawRowCheck18753]

theorem rawRowCheck18754 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18754 := by decide +kernel

theorem rowCheck18754 : row18754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18754 := by decide +kernel

theorem rowEval18754 (x : Key → ℝ) : Integer.Sparse.eval row18754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18754, Integer.Sparse.eval_collectBalanced, rawRowCheck18754]

theorem rawRowCheck18755 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form4 = rawRow18755 := by decide +kernel

theorem rowCheck18755 : row18755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18755 := by decide +kernel

theorem rowEval18755 (x : Key → ℝ) : Integer.Sparse.eval row18755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18755, Integer.Sparse.eval_collectBalanced, rawRowCheck18755]

theorem rawRowCheck18756 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18756 := by decide +kernel

theorem rowCheck18756 : row18756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18756 := by decide +kernel

theorem rowEval18756 (x : Key → ℝ) : Integer.Sparse.eval row18756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18756, Integer.Sparse.eval_collectBalanced, rawRowCheck18756]

theorem rawRowCheck18757 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18757 := by decide +kernel

theorem rowCheck18757 : row18757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18757 := by decide +kernel

theorem rowEval18757 (x : Key → ℝ) : Integer.Sparse.eval row18757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18757, Integer.Sparse.eval_collectBalanced, rawRowCheck18757]

theorem rawRowCheck18758 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18758 := by decide +kernel

theorem rowCheck18758 : row18758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18758 := by decide +kernel

theorem rowEval18758 (x : Key → ℝ) : Integer.Sparse.eval row18758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18758, Integer.Sparse.eval_collectBalanced, rawRowCheck18758]

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

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18679 x
  · exact rowEval18680 x
  · exact rowEval18681 x
  · exact rowEval18682 x
  · exact rowEval18683 x
  · exact rowEval18684 x
  · exact rowEval18685 x
  · exact rowEval18686 x
  · exact rowEval18687 x
  · exact rowEval18688 x
  · exact rowEval18689 x
  · exact rowEval18690 x
  · exact rowEval18691 x
  · exact rowEval18692 x
  · exact rowEval18693 x
  · exact rowEval18694 x
  · exact rowEval18695 x
  · exact rowEval18696 x
  · exact rowEval18697 x
  · exact rowEval18698 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18699 x
  · exact rowEval18700 x
  · exact rowEval18701 x
  · exact rowEval18702 x
  · exact rowEval18703 x
  · exact rowEval18704 x
  · exact rowEval18705 x
  · exact rowEval18706 x
  · exact rowEval18707 x
  · exact rowEval18708 x
  · exact rowEval18709 x
  · exact rowEval18710 x
  · exact rowEval18711 x
  · exact rowEval18712 x
  · exact rowEval18713 x
  · exact rowEval18714 x
  · exact rowEval18715 x
  · exact rowEval18716 x
  · exact rowEval18717 x
  · exact rowEval18718 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form3) x := by
  fin_cases k
  · exact rowEval18719 x
  · exact rowEval18720 x
  · exact rowEval18721 x
  · exact rowEval18722 x
  · exact rowEval18723 x
  · exact rowEval18724 x
  · exact rowEval18725 x
  · exact rowEval18726 x
  · exact rowEval18727 x
  · exact rowEval18728 x
  · exact rowEval18729 x
  · exact rowEval18730 x
  · exact rowEval18731 x
  · exact rowEval18732 x
  · exact rowEval18733 x
  · exact rowEval18734 x
  · exact rowEval18735 x
  · exact rowEval18736 x
  · exact rowEval18737 x
  · exact rowEval18738 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block5.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form4.terms k).tag (GramFunctions.Block5.form4.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval18739 x
  · exact rowEval18740 x
  · exact rowEval18741 x
  · exact rowEval18742 x
  · exact rowEval18743 x
  · exact rowEval18744 x
  · exact rowEval18745 x
  · exact rowEval18746 x
  · exact rowEval18747 x
  · exact rowEval18748 x
  · exact rowEval18749 x
  · exact rowEval18750 x
  · exact rowEval18751 x
  · exact rowEval18752 x
  · exact rowEval18753 x
  · exact rowEval18754 x
  · exact rowEval18755 x
  · exact rowEval18756 x
  · exact rowEval18757 x
  · exact rowEval18758 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block5.form4.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form4 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

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

theorem rawRowCheck18879 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18879 := by decide +kernel

theorem rowCheck18879 : row18879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18879 := by decide +kernel

theorem rowEval18879 (x : Key → ℝ) : Integer.Sparse.eval row18879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18879, Integer.Sparse.eval_collectBalanced, rawRowCheck18879]

theorem rawRowCheck18880 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18880 := by decide +kernel

theorem rowCheck18880 : row18880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18880 := by decide +kernel

theorem rowEval18880 (x : Key → ℝ) : Integer.Sparse.eval row18880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18880, Integer.Sparse.eval_collectBalanced, rawRowCheck18880]

theorem rawRowCheck18881 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18881 := by decide +kernel

theorem rowCheck18881 : row18881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18881 := by decide +kernel

theorem rowEval18881 (x : Key → ℝ) : Integer.Sparse.eval row18881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18881, Integer.Sparse.eval_collectBalanced, rawRowCheck18881]

theorem rawRowCheck18882 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18882 := by decide +kernel

theorem rowCheck18882 : row18882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18882 := by decide +kernel

theorem rowEval18882 (x : Key → ℝ) : Integer.Sparse.eval row18882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18882, Integer.Sparse.eval_collectBalanced, rawRowCheck18882]

theorem rawRowCheck18883 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18883 := by decide +kernel

theorem rowCheck18883 : row18883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18883 := by decide +kernel

theorem rowEval18883 (x : Key → ℝ) : Integer.Sparse.eval row18883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18883, Integer.Sparse.eval_collectBalanced, rawRowCheck18883]

theorem rawRowCheck18884 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18884 := by decide +kernel

theorem rowCheck18884 : row18884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18884 := by decide +kernel

theorem rowEval18884 (x : Key → ℝ) : Integer.Sparse.eval row18884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18884, Integer.Sparse.eval_collectBalanced, rawRowCheck18884]

theorem rawRowCheck18885 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4 = rawRow18885 := by decide +kernel

theorem rowCheck18885 : row18885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18885 := by decide +kernel

theorem rowEval18885 (x : Key → ℝ) : Integer.Sparse.eval row18885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18885, Integer.Sparse.eval_collectBalanced, rawRowCheck18885]

theorem rawRowCheck18886 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4 = rawRow18886 := by decide +kernel

theorem rowCheck18886 : row18886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18886 := by decide +kernel

theorem rowEval18886 (x : Key → ℝ) : Integer.Sparse.eval row18886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18886, Integer.Sparse.eval_collectBalanced, rawRowCheck18886]

theorem rawRowCheck18887 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4 = rawRow18887 := by decide +kernel

theorem rowCheck18887 : row18887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18887 := by decide +kernel

theorem rowEval18887 (x : Key → ℝ) : Integer.Sparse.eval row18887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18887, Integer.Sparse.eval_collectBalanced, rawRowCheck18887]

theorem rawRowCheck18888 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4 = rawRow18888 := by decide +kernel

theorem rowCheck18888 : row18888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18888 := by decide +kernel

theorem rowEval18888 (x : Key → ℝ) : Integer.Sparse.eval row18888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18888, Integer.Sparse.eval_collectBalanced, rawRowCheck18888]

theorem rawRowCheck18889 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4 = rawRow18889 := by decide +kernel

theorem rowCheck18889 : row18889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18889 := by decide +kernel

theorem rowEval18889 (x : Key → ℝ) : Integer.Sparse.eval row18889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18889, Integer.Sparse.eval_collectBalanced, rawRowCheck18889]

theorem rawRowCheck18890 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4 = rawRow18890 := by decide +kernel

theorem rowCheck18890 : row18890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18890 := by decide +kernel

theorem rowEval18890 (x : Key → ℝ) : Integer.Sparse.eval row18890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18890, Integer.Sparse.eval_collectBalanced, rawRowCheck18890]

theorem rawRowCheck18891 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18891 := by decide +kernel

theorem rowCheck18891 : row18891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18891 := by decide +kernel

theorem rowEval18891 (x : Key → ℝ) : Integer.Sparse.eval row18891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18891, Integer.Sparse.eval_collectBalanced, rawRowCheck18891]

theorem rawRowCheck18892 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18892 := by decide +kernel

theorem rowCheck18892 : row18892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18892 := by decide +kernel

theorem rowEval18892 (x : Key → ℝ) : Integer.Sparse.eval row18892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18892, Integer.Sparse.eval_collectBalanced, rawRowCheck18892]

theorem rawRowCheck18893 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18893 := by decide +kernel

theorem rowCheck18893 : row18893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18893 := by decide +kernel

theorem rowEval18893 (x : Key → ℝ) : Integer.Sparse.eval row18893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18893, Integer.Sparse.eval_collectBalanced, rawRowCheck18893]

theorem rawRowCheck18894 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18894 := by decide +kernel

theorem rowCheck18894 : row18894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18894 := by decide +kernel

theorem rowEval18894 (x : Key → ℝ) : Integer.Sparse.eval row18894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18894, Integer.Sparse.eval_collectBalanced, rawRowCheck18894]

theorem rawRowCheck18895 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18895 := by decide +kernel

theorem rowCheck18895 : row18895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18895 := by decide +kernel

theorem rowEval18895 (x : Key → ℝ) : Integer.Sparse.eval row18895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18895, Integer.Sparse.eval_collectBalanced, rawRowCheck18895]

theorem rawRowCheck18896 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18896 := by decide +kernel

theorem rowCheck18896 : row18896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18896 := by decide +kernel

theorem rowEval18896 (x : Key → ℝ) : Integer.Sparse.eval row18896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18896, Integer.Sparse.eval_collectBalanced, rawRowCheck18896]

theorem rawRowCheck18897 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4 = rawRow18897 := by decide +kernel

theorem rowCheck18897 : row18897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18897 := by decide +kernel

theorem rowEval18897 (x : Key → ℝ) : Integer.Sparse.eval row18897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18897, Integer.Sparse.eval_collectBalanced, rawRowCheck18897]

theorem rawRowCheck18898 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4 = rawRow18898 := by decide +kernel

theorem rowCheck18898 : row18898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18898 := by decide +kernel

theorem rowEval18898 (x : Key → ℝ) : Integer.Sparse.eval row18898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18898, Integer.Sparse.eval_collectBalanced, rawRowCheck18898]

theorem rawRowCheck18899 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4 = rawRow18899 := by decide +kernel

theorem rowCheck18899 : row18899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18899 := by decide +kernel

theorem rowEval18899 (x : Key → ℝ) : Integer.Sparse.eval row18899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18899, Integer.Sparse.eval_collectBalanced, rawRowCheck18899]

theorem rawRowCheck18900 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4 = rawRow18900 := by decide +kernel

theorem rowCheck18900 : row18900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18900 := by decide +kernel

theorem rowEval18900 (x : Key → ℝ) : Integer.Sparse.eval row18900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18900, Integer.Sparse.eval_collectBalanced, rawRowCheck18900]

theorem rawRowCheck18901 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4 = rawRow18901 := by decide +kernel

theorem rowCheck18901 : row18901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18901 := by decide +kernel

theorem rowEval18901 (x : Key → ℝ) : Integer.Sparse.eval row18901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18901, Integer.Sparse.eval_collectBalanced, rawRowCheck18901]

theorem rawRowCheck18902 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4 = rawRow18902 := by decide +kernel

theorem rowCheck18902 : row18902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18902 := by decide +kernel

theorem rowEval18902 (x : Key → ℝ) : Integer.Sparse.eval row18902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block5.form4) x := by
  rw [rowCheck18902, Integer.Sparse.eval_collectBalanced, rawRowCheck18902]

theorem rawRowCheck18903 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4 = rawRow18903 := by decide +kernel

theorem rowCheck18903 : row18903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18903 := by decide +kernel

theorem rowEval18903 (x : Key → ℝ) : Integer.Sparse.eval row18903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18903, Integer.Sparse.eval_collectBalanced, rawRowCheck18903]

theorem rawRowCheck18904 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4 = rawRow18904 := by decide +kernel

theorem rowCheck18904 : row18904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18904 := by decide +kernel

theorem rowEval18904 (x : Key → ℝ) : Integer.Sparse.eval row18904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18904, Integer.Sparse.eval_collectBalanced, rawRowCheck18904]

theorem rawRowCheck18905 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4 = rawRow18905 := by decide +kernel

theorem rowCheck18905 : row18905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18905 := by decide +kernel

theorem rowEval18905 (x : Key → ℝ) : Integer.Sparse.eval row18905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18905, Integer.Sparse.eval_collectBalanced, rawRowCheck18905]

theorem rawRowCheck18906 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4 = rawRow18906 := by decide +kernel

theorem rowCheck18906 : row18906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18906 := by decide +kernel

theorem rowEval18906 (x : Key → ℝ) : Integer.Sparse.eval row18906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18906, Integer.Sparse.eval_collectBalanced, rawRowCheck18906]

theorem rawRowCheck18907 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4 = rawRow18907 := by decide +kernel

theorem rowCheck18907 : row18907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18907 := by decide +kernel

theorem rowEval18907 (x : Key → ℝ) : Integer.Sparse.eval row18907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck18907, Integer.Sparse.eval_collectBalanced, rawRowCheck18907]

theorem rawRowCheck18908 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4 = rawRow18908 := by decide +kernel

theorem rowCheck18908 : row18908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18908 := by decide +kernel

theorem rowEval18908 (x : Key → ℝ) : Integer.Sparse.eval row18908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block5.form4) x := by
  rw [rowCheck18908, Integer.Sparse.eval_collectBalanced, rawRowCheck18908]

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

theorem entryCheck5_4 : entry5_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form5.terms k).coefficient) (rows5_4 k)) := by decide +kernel

theorem rowsSound5_4 (k : Fin GramFunctions.Block5.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form5.terms k).tag (GramFunctions.Block5.form5.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval18879 x
  · exact rowEval18880 x
  · exact rowEval18881 x
  · exact rowEval18882 x
  · exact rowEval18883 x
  · exact rowEval18884 x
  · exact rowEval18885 x
  · exact rowEval18886 x
  · exact rowEval18887 x
  · exact rowEval18888 x
  · exact rowEval18889 x
  · exact rowEval18890 x
  · exact rowEval18891 x
  · exact rowEval18892 x
  · exact rowEval18893 x
  · exact rowEval18894 x
  · exact rowEval18895 x
  · exact rowEval18896 x
  · exact rowEval18897 x
  · exact rowEval18898 x
  · exact rowEval18899 x
  · exact rowEval18900 x
  · exact rowEval18901 x
  · exact rowEval18902 x
  · exact rowEval18903 x
  · exact rowEval18904 x
  · exact rowEval18905 x
  · exact rowEval18906 x
  · exact rowEval18907 x
  · exact rowEval18908 x

theorem entryEval5_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_4 (GramNormalization.eval B) = GramFunctions.Block5.form5.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck5_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form5 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_4]

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

theorem rawRowCheck19159 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19159 := by decide +kernel

theorem rowCheck19159 : row19159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19159 := by decide +kernel

theorem rowEval19159 (x : Key → ℝ) : Integer.Sparse.eval row19159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19159, Integer.Sparse.eval_collectBalanced, rawRowCheck19159]

theorem rawRowCheck19160 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19160 := by decide +kernel

theorem rowCheck19160 : row19160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19160 := by decide +kernel

theorem rowEval19160 (x : Key → ℝ) : Integer.Sparse.eval row19160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19160, Integer.Sparse.eval_collectBalanced, rawRowCheck19160]

theorem rawRowCheck19161 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19161 := by decide +kernel

theorem rowCheck19161 : row19161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19161 := by decide +kernel

theorem rowEval19161 (x : Key → ℝ) : Integer.Sparse.eval row19161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19161, Integer.Sparse.eval_collectBalanced, rawRowCheck19161]

theorem rawRowCheck19162 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19162 := by decide +kernel

theorem rowCheck19162 : row19162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19162 := by decide +kernel

theorem rowEval19162 (x : Key → ℝ) : Integer.Sparse.eval row19162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19162, Integer.Sparse.eval_collectBalanced, rawRowCheck19162]

theorem rawRowCheck19163 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19163 := by decide +kernel

theorem rowCheck19163 : row19163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19163 := by decide +kernel

theorem rowEval19163 (x : Key → ℝ) : Integer.Sparse.eval row19163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19163, Integer.Sparse.eval_collectBalanced, rawRowCheck19163]

theorem rawRowCheck19164 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19164 := by decide +kernel

theorem rowCheck19164 : row19164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19164 := by decide +kernel

theorem rowEval19164 (x : Key → ℝ) : Integer.Sparse.eval row19164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19164, Integer.Sparse.eval_collectBalanced, rawRowCheck19164]

theorem rawRowCheck19165 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19165 := by decide +kernel

theorem rowCheck19165 : row19165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19165 := by decide +kernel

theorem rowEval19165 (x : Key → ℝ) : Integer.Sparse.eval row19165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19165, Integer.Sparse.eval_collectBalanced, rawRowCheck19165]

theorem rawRowCheck19166 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19166 := by decide +kernel

theorem rowCheck19166 : row19166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19166 := by decide +kernel

theorem rowEval19166 (x : Key → ℝ) : Integer.Sparse.eval row19166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19166, Integer.Sparse.eval_collectBalanced, rawRowCheck19166]

theorem rawRowCheck19167 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19167 := by decide +kernel

theorem rowCheck19167 : row19167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19167 := by decide +kernel

theorem rowEval19167 (x : Key → ℝ) : Integer.Sparse.eval row19167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19167, Integer.Sparse.eval_collectBalanced, rawRowCheck19167]

theorem rawRowCheck19168 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19168 := by decide +kernel

theorem rowCheck19168 : row19168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19168 := by decide +kernel

theorem rowEval19168 (x : Key → ℝ) : Integer.Sparse.eval row19168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19168, Integer.Sparse.eval_collectBalanced, rawRowCheck19168]

theorem rawRowCheck19169 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19169 := by decide +kernel

theorem rowCheck19169 : row19169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19169 := by decide +kernel

theorem rowEval19169 (x : Key → ℝ) : Integer.Sparse.eval row19169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19169, Integer.Sparse.eval_collectBalanced, rawRowCheck19169]

theorem rawRowCheck19170 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19170 := by decide +kernel

theorem rowCheck19170 : row19170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19170 := by decide +kernel

theorem rowEval19170 (x : Key → ℝ) : Integer.Sparse.eval row19170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19170, Integer.Sparse.eval_collectBalanced, rawRowCheck19170]

theorem rawRowCheck19171 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19171 := by decide +kernel

theorem rowCheck19171 : row19171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19171 := by decide +kernel

theorem rowEval19171 (x : Key → ℝ) : Integer.Sparse.eval row19171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19171, Integer.Sparse.eval_collectBalanced, rawRowCheck19171]

theorem rawRowCheck19172 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19172 := by decide +kernel

theorem rowCheck19172 : row19172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19172 := by decide +kernel

theorem rowEval19172 (x : Key → ℝ) : Integer.Sparse.eval row19172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19172, Integer.Sparse.eval_collectBalanced, rawRowCheck19172]

theorem rawRowCheck19173 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4 = rawRow19173 := by decide +kernel

theorem rowCheck19173 : row19173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19173 := by decide +kernel

theorem rowEval19173 (x : Key → ℝ) : Integer.Sparse.eval row19173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19173, Integer.Sparse.eval_collectBalanced, rawRowCheck19173]

theorem rawRowCheck19174 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4 = rawRow19174 := by decide +kernel

theorem rowCheck19174 : row19174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19174 := by decide +kernel

theorem rowEval19174 (x : Key → ℝ) : Integer.Sparse.eval row19174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19174, Integer.Sparse.eval_collectBalanced, rawRowCheck19174]

theorem rawRowCheck19175 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4 = rawRow19175 := by decide +kernel

theorem rowCheck19175 : row19175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19175 := by decide +kernel

theorem rowEval19175 (x : Key → ℝ) : Integer.Sparse.eval row19175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19175, Integer.Sparse.eval_collectBalanced, rawRowCheck19175]

theorem rawRowCheck19176 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4 = rawRow19176 := by decide +kernel

theorem rowCheck19176 : row19176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19176 := by decide +kernel

theorem rowEval19176 (x : Key → ℝ) : Integer.Sparse.eval row19176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19176, Integer.Sparse.eval_collectBalanced, rawRowCheck19176]

theorem rawRowCheck19177 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4 = rawRow19177 := by decide +kernel

theorem rowCheck19177 : row19177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19177 := by decide +kernel

theorem rowEval19177 (x : Key → ℝ) : Integer.Sparse.eval row19177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19177, Integer.Sparse.eval_collectBalanced, rawRowCheck19177]

theorem rawRowCheck19178 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4 = rawRow19178 := by decide +kernel

theorem rowCheck19178 : row19178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19178 := by decide +kernel

theorem rowEval19178 (x : Key → ℝ) : Integer.Sparse.eval row19178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19178, Integer.Sparse.eval_collectBalanced, rawRowCheck19178]

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

theorem rawRowCheck19259 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19259 := by decide +kernel

theorem rowCheck19259 : row19259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19259 := by decide +kernel

theorem rowEval19259 (x : Key → ℝ) : Integer.Sparse.eval row19259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19259, Integer.Sparse.eval_collectBalanced, rawRowCheck19259]

theorem rawRowCheck19260 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19260 := by decide +kernel

theorem rowCheck19260 : row19260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19260 := by decide +kernel

theorem rowEval19260 (x : Key → ℝ) : Integer.Sparse.eval row19260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19260, Integer.Sparse.eval_collectBalanced, rawRowCheck19260]

theorem rawRowCheck19261 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19261 := by decide +kernel

theorem rowCheck19261 : row19261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19261 := by decide +kernel

theorem rowEval19261 (x : Key → ℝ) : Integer.Sparse.eval row19261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19261, Integer.Sparse.eval_collectBalanced, rawRowCheck19261]

theorem rawRowCheck19262 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19262 := by decide +kernel

theorem rowCheck19262 : row19262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19262 := by decide +kernel

theorem rowEval19262 (x : Key → ℝ) : Integer.Sparse.eval row19262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19262, Integer.Sparse.eval_collectBalanced, rawRowCheck19262]

theorem rawRowCheck19263 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19263 := by decide +kernel

theorem rowCheck19263 : row19263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19263 := by decide +kernel

theorem rowEval19263 (x : Key → ℝ) : Integer.Sparse.eval row19263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19263, Integer.Sparse.eval_collectBalanced, rawRowCheck19263]

theorem rawRowCheck19324 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19324 := by decide +kernel

theorem rowCheck19324 : row19324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19324 := by decide +kernel

theorem rowEval19324 (x : Key → ℝ) : Integer.Sparse.eval row19324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19324, Integer.Sparse.eval_collectBalanced, rawRowCheck19324]

theorem rawRowCheck19325 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19325 := by decide +kernel

theorem rowCheck19325 : row19325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19325 := by decide +kernel

theorem rowEval19325 (x : Key → ℝ) : Integer.Sparse.eval row19325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19325, Integer.Sparse.eval_collectBalanced, rawRowCheck19325]

theorem rawRowCheck19326 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19326 := by decide +kernel

theorem rowCheck19326 : row19326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19326 := by decide +kernel

theorem rowEval19326 (x : Key → ℝ) : Integer.Sparse.eval row19326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19326, Integer.Sparse.eval_collectBalanced, rawRowCheck19326]

theorem rawRowCheck19327 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19327 := by decide +kernel

theorem rowCheck19327 : row19327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19327 := by decide +kernel

theorem rowEval19327 (x : Key → ℝ) : Integer.Sparse.eval row19327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19327, Integer.Sparse.eval_collectBalanced, rawRowCheck19327]

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

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19159 x
  · exact rowEval19160 x
  · exact rowEval19161 x
  · exact rowEval19162 x
  · exact rowEval19163 x
  · exact rowEval19164 x
  · exact rowEval19165 x
  · exact rowEval19166 x
  · exact rowEval19167 x
  · exact rowEval19168 x
  · exact rowEval19169 x
  · exact rowEval19170 x
  · exact rowEval19171 x
  · exact rowEval19172 x
  · exact rowEval19173 x
  · exact rowEval19174 x
  · exact rowEval19175 x
  · exact rowEval19176 x
  · exact rowEval19177 x
  · exact rowEval19178 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block5.form7.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form7 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

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

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block5.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form8.terms k).tag (GramFunctions.Block5.form8.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19259 x
  · exact rowEval19260 x
  · exact rowEval19261 x
  · exact rowEval19262 x
  · exact rowEval19263 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block5.form8.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form8 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

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

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block5.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form9.terms k).tag (GramFunctions.Block5.form9.terms k).charge GramFunctions.Block5.form4) x := by
  fin_cases k
  · exact rowEval19324 x
  · exact rowEval19325 x
  · exact rowEval19326 x
  · exact rowEval19327 x
  · exact rowEval19328 x
  · exact rowEval19329 x
  · exact rowEval19330 x
  · exact rowEval19331 x
  · exact rowEval19332 x
  · exact rowEval19333 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block5.form9.mixedGram GramFunctions.Block5.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form9 GramFunctions.Block5.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

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

theorem entryEvalRow4_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 4).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval4_0 B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2 B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4_e_oai
