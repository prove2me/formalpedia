-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:52:47.507204+00:00
-- url     : https://prove2.me/submissions/62fe93e9-5287-4a87-8f29-7c6cf5e486d5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E027
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E053
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval4_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval4_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval5_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval6_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval7_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_4_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7138 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7138 := by decide +kernel

theorem rowCheck7138 : row7138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7138 := by decide +kernel

theorem rowEval7138 (x : Key → ℝ) : Integer.Sparse.eval row7138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7138, Integer.Sparse.eval_collectBalanced, rawRowCheck7138]

theorem rawRowCheck7139 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7139 := by decide +kernel

theorem rowCheck7139 : row7139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7139 := by decide +kernel

theorem rowEval7139 (x : Key → ℝ) : Integer.Sparse.eval row7139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7139, Integer.Sparse.eval_collectBalanced, rawRowCheck7139]

theorem rawRowCheck7140 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7140 := by decide +kernel

theorem rowCheck7140 : row7140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7140 := by decide +kernel

theorem rowEval7140 (x : Key → ℝ) : Integer.Sparse.eval row7140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7140, Integer.Sparse.eval_collectBalanced, rawRowCheck7140]

theorem rawRowCheck7141 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7141 := by decide +kernel

theorem rowCheck7141 : row7141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7141 := by decide +kernel

theorem rowEval7141 (x : Key → ℝ) : Integer.Sparse.eval row7141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7141, Integer.Sparse.eval_collectBalanced, rawRowCheck7141]

theorem rawRowCheck7142 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7142 := by decide +kernel

theorem rowCheck7142 : row7142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7142 := by decide +kernel

theorem rowEval7142 (x : Key → ℝ) : Integer.Sparse.eval row7142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7142, Integer.Sparse.eval_collectBalanced, rawRowCheck7142]

theorem rawRowCheck7143 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7143 := by decide +kernel

theorem rowCheck7143 : row7143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7143 := by decide +kernel

theorem rowEval7143 (x : Key → ℝ) : Integer.Sparse.eval row7143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7143, Integer.Sparse.eval_collectBalanced, rawRowCheck7143]

theorem rawRowCheck7144 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7144 := by decide +kernel

theorem rowCheck7144 : row7144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7144 := by decide +kernel

theorem rowEval7144 (x : Key → ℝ) : Integer.Sparse.eval row7144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7144, Integer.Sparse.eval_collectBalanced, rawRowCheck7144]

theorem rawRowCheck7145 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7145 := by decide +kernel

theorem rowCheck7145 : row7145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7145 := by decide +kernel

theorem rowEval7145 (x : Key → ℝ) : Integer.Sparse.eval row7145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7145, Integer.Sparse.eval_collectBalanced, rawRowCheck7145]

theorem rawRowCheck7146 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7146 := by decide +kernel

theorem rowCheck7146 : row7146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7146 := by decide +kernel

theorem rowEval7146 (x : Key → ℝ) : Integer.Sparse.eval row7146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7146, Integer.Sparse.eval_collectBalanced, rawRowCheck7146]

theorem rawRowCheck7147 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4 = rawRow7147 := by decide +kernel

theorem rowCheck7147 : row7147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7147 := by decide +kernel

theorem rowEval7147 (x : Key → ℝ) : Integer.Sparse.eval row7147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7147, Integer.Sparse.eval_collectBalanced, rawRowCheck7147]

theorem rawRowCheck7148 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4 = rawRow7148 := by decide +kernel

theorem rowCheck7148 : row7148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7148 := by decide +kernel

theorem rowEval7148 (x : Key → ℝ) : Integer.Sparse.eval row7148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7148, Integer.Sparse.eval_collectBalanced, rawRowCheck7148]

theorem rawRowCheck7149 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4 = rawRow7149 := by decide +kernel

theorem rowCheck7149 : row7149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7149 := by decide +kernel

theorem rowEval7149 (x : Key → ℝ) : Integer.Sparse.eval row7149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7149, Integer.Sparse.eval_collectBalanced, rawRowCheck7149]

theorem rawRowCheck7150 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7150 := by decide +kernel

theorem rowCheck7150 : row7150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7150 := by decide +kernel

theorem rowEval7150 (x : Key → ℝ) : Integer.Sparse.eval row7150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7150, Integer.Sparse.eval_collectBalanced, rawRowCheck7150]

theorem rawRowCheck7151 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7151 := by decide +kernel

theorem rowCheck7151 : row7151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7151 := by decide +kernel

theorem rowEval7151 (x : Key → ℝ) : Integer.Sparse.eval row7151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7151, Integer.Sparse.eval_collectBalanced, rawRowCheck7151]

theorem rawRowCheck7152 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7152 := by decide +kernel

theorem rowCheck7152 : row7152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7152 := by decide +kernel

theorem rowEval7152 (x : Key → ℝ) : Integer.Sparse.eval row7152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7152, Integer.Sparse.eval_collectBalanced, rawRowCheck7152]

theorem rawRowCheck7153 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7153 := by decide +kernel

theorem rowCheck7153 : row7153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7153 := by decide +kernel

theorem rowEval7153 (x : Key → ℝ) : Integer.Sparse.eval row7153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7153, Integer.Sparse.eval_collectBalanced, rawRowCheck7153]

theorem rawRowCheck7154 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7154 := by decide +kernel

theorem rowCheck7154 : row7154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7154 := by decide +kernel

theorem rowEval7154 (x : Key → ℝ) : Integer.Sparse.eval row7154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7154, Integer.Sparse.eval_collectBalanced, rawRowCheck7154]

theorem rawRowCheck7155 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7155 := by decide +kernel

theorem rowCheck7155 : row7155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7155 := by decide +kernel

theorem rowEval7155 (x : Key → ℝ) : Integer.Sparse.eval row7155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7155, Integer.Sparse.eval_collectBalanced, rawRowCheck7155]

theorem rawRowCheck7156 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7156 := by decide +kernel

theorem rowCheck7156 : row7156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7156 := by decide +kernel

theorem rowEval7156 (x : Key → ℝ) : Integer.Sparse.eval row7156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7156, Integer.Sparse.eval_collectBalanced, rawRowCheck7156]

theorem rawRowCheck7157 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7157 := by decide +kernel

theorem rowCheck7157 : row7157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7157 := by decide +kernel

theorem rowEval7157 (x : Key → ℝ) : Integer.Sparse.eval row7157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7157, Integer.Sparse.eval_collectBalanced, rawRowCheck7157]

theorem rawRowCheck7158 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7158 := by decide +kernel

theorem rowCheck7158 : row7158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7158 := by decide +kernel

theorem rowEval7158 (x : Key → ℝ) : Integer.Sparse.eval row7158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7158, Integer.Sparse.eval_collectBalanced, rawRowCheck7158]

theorem rawRowCheck7159 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7159 := by decide +kernel

theorem rowCheck7159 : row7159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7159 := by decide +kernel

theorem rowEval7159 (x : Key → ℝ) : Integer.Sparse.eval row7159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7159, Integer.Sparse.eval_collectBalanced, rawRowCheck7159]

theorem rawRowCheck7160 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7160 := by decide +kernel

theorem rowCheck7160 : row7160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7160 := by decide +kernel

theorem rowEval7160 (x : Key → ℝ) : Integer.Sparse.eval row7160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7160, Integer.Sparse.eval_collectBalanced, rawRowCheck7160]

theorem rawRowCheck7161 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7161 := by decide +kernel

theorem rowCheck7161 : row7161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7161 := by decide +kernel

theorem rowEval7161 (x : Key → ℝ) : Integer.Sparse.eval row7161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7161, Integer.Sparse.eval_collectBalanced, rawRowCheck7161]

theorem rawRowCheck7162 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7162 := by decide +kernel

theorem rowCheck7162 : row7162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7162 := by decide +kernel

theorem rowEval7162 (x : Key → ℝ) : Integer.Sparse.eval row7162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7162, Integer.Sparse.eval_collectBalanced, rawRowCheck7162]

theorem rawRowCheck7163 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7163 := by decide +kernel

theorem rowCheck7163 : row7163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7163 := by decide +kernel

theorem rowEval7163 (x : Key → ℝ) : Integer.Sparse.eval row7163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7163, Integer.Sparse.eval_collectBalanced, rawRowCheck7163]

theorem rawRowCheck7164 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7164 := by decide +kernel

theorem rowCheck7164 : row7164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7164 := by decide +kernel

theorem rowEval7164 (x : Key → ℝ) : Integer.Sparse.eval row7164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7164, Integer.Sparse.eval_collectBalanced, rawRowCheck7164]

theorem rawRowCheck7165 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow7165 := by decide +kernel

theorem rowCheck7165 : row7165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7165 := by decide +kernel

theorem rowEval7165 (x : Key → ℝ) : Integer.Sparse.eval row7165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7165, Integer.Sparse.eval_collectBalanced, rawRowCheck7165]

theorem rawRowCheck7166 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow7166 := by decide +kernel

theorem rowCheck7166 : row7166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7166 := by decide +kernel

theorem rowEval7166 (x : Key → ℝ) : Integer.Sparse.eval row7166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7166, Integer.Sparse.eval_collectBalanced, rawRowCheck7166]

theorem rawRowCheck7167 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow7167 := by decide +kernel

theorem rowCheck7167 : row7167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7167 := by decide +kernel

theorem rowEval7167 (x : Key → ℝ) : Integer.Sparse.eval row7167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7167, Integer.Sparse.eval_collectBalanced, rawRowCheck7167]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval7138 x
  · exact rowEval7139 x
  · exact rowEval7140 x
  · exact rowEval7141 x
  · exact rowEval7142 x
  · exact rowEval7143 x
  · exact rowEval7144 x
  · exact rowEval7145 x
  · exact rowEval7146 x
  · exact rowEval7147 x
  · exact rowEval7148 x
  · exact rowEval7149 x
  · exact rowEval7150 x
  · exact rowEval7151 x
  · exact rowEval7152 x
  · exact rowEval7153 x
  · exact rowEval7154 x
  · exact rowEval7155 x
  · exact rowEval7156 x
  · exact rowEval7157 x
  · exact rowEval7158 x
  · exact rowEval7159 x
  · exact rowEval7160 x
  · exact rowEval7161 x
  · exact rowEval7162 x
  · exact rowEval7163 x
  · exact rowEval7164 x
  · exact rowEval7165 x
  · exact rowEval7166 x
  · exact rowEval7167 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5538 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5538 := by decide +kernel

theorem rowCheck5538 : row5538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5538 := by decide +kernel

theorem rowEval5538 (x : Key → ℝ) : Integer.Sparse.eval row5538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5538, Integer.Sparse.eval_collectBalanced, rawRowCheck5538]

theorem rawRowCheck5539 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5539 := by decide +kernel

theorem rowCheck5539 : row5539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5539 := by decide +kernel

theorem rowEval5539 (x : Key → ℝ) : Integer.Sparse.eval row5539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5539, Integer.Sparse.eval_collectBalanced, rawRowCheck5539]

theorem rawRowCheck5540 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5540 := by decide +kernel

theorem rowCheck5540 : row5540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5540 := by decide +kernel

theorem rowEval5540 (x : Key → ℝ) : Integer.Sparse.eval row5540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5540, Integer.Sparse.eval_collectBalanced, rawRowCheck5540]

theorem rawRowCheck5541 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5541 := by decide +kernel

theorem rowCheck5541 : row5541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5541 := by decide +kernel

theorem rowEval5541 (x : Key → ℝ) : Integer.Sparse.eval row5541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5541, Integer.Sparse.eval_collectBalanced, rawRowCheck5541]

theorem rawRowCheck5542 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5542 := by decide +kernel

theorem rowCheck5542 : row5542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5542 := by decide +kernel

theorem rowEval5542 (x : Key → ℝ) : Integer.Sparse.eval row5542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5542, Integer.Sparse.eval_collectBalanced, rawRowCheck5542]

theorem rawRowCheck5543 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5543 := by decide +kernel

theorem rowCheck5543 : row5543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5543 := by decide +kernel

theorem rowEval5543 (x : Key → ℝ) : Integer.Sparse.eval row5543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5543, Integer.Sparse.eval_collectBalanced, rawRowCheck5543]

theorem rawRowCheck5544 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5544 := by decide +kernel

theorem rowCheck5544 : row5544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5544 := by decide +kernel

theorem rowEval5544 (x : Key → ℝ) : Integer.Sparse.eval row5544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5544, Integer.Sparse.eval_collectBalanced, rawRowCheck5544]

theorem rawRowCheck5545 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5545 := by decide +kernel

theorem rowCheck5545 : row5545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5545 := by decide +kernel

theorem rowEval5545 (x : Key → ℝ) : Integer.Sparse.eval row5545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5545, Integer.Sparse.eval_collectBalanced, rawRowCheck5545]

theorem rawRowCheck5546 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5546 := by decide +kernel

theorem rowCheck5546 : row5546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5546 := by decide +kernel

theorem rowEval5546 (x : Key → ℝ) : Integer.Sparse.eval row5546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5546, Integer.Sparse.eval_collectBalanced, rawRowCheck5546]

theorem rawRowCheck5547 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1 = rawRow5547 := by decide +kernel

theorem rowCheck5547 : row5547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5547 := by decide +kernel

theorem rowEval5547 (x : Key → ℝ) : Integer.Sparse.eval row5547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5547, Integer.Sparse.eval_collectBalanced, rawRowCheck5547]

theorem rawRowCheck5548 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1 = rawRow5548 := by decide +kernel

theorem rowCheck5548 : row5548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5548 := by decide +kernel

theorem rowEval5548 (x : Key → ℝ) : Integer.Sparse.eval row5548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5548, Integer.Sparse.eval_collectBalanced, rawRowCheck5548]

theorem rawRowCheck5549 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1 = rawRow5549 := by decide +kernel

theorem rowCheck5549 : row5549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5549 := by decide +kernel

theorem rowEval5549 (x : Key → ℝ) : Integer.Sparse.eval row5549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5549, Integer.Sparse.eval_collectBalanced, rawRowCheck5549]

theorem rawRowCheck5550 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5550 := by decide +kernel

theorem rowCheck5550 : row5550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5550 := by decide +kernel

theorem rowEval5550 (x : Key → ℝ) : Integer.Sparse.eval row5550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5550, Integer.Sparse.eval_collectBalanced, rawRowCheck5550]

theorem rawRowCheck5551 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5551 := by decide +kernel

theorem rowCheck5551 : row5551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5551 := by decide +kernel

theorem rowEval5551 (x : Key → ℝ) : Integer.Sparse.eval row5551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5551, Integer.Sparse.eval_collectBalanced, rawRowCheck5551]

theorem rawRowCheck5552 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5552 := by decide +kernel

theorem rowCheck5552 : row5552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5552 := by decide +kernel

theorem rowEval5552 (x : Key → ℝ) : Integer.Sparse.eval row5552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5552, Integer.Sparse.eval_collectBalanced, rawRowCheck5552]

theorem rawRowCheck5553 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5553 := by decide +kernel

theorem rowCheck5553 : row5553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5553 := by decide +kernel

theorem rowEval5553 (x : Key → ℝ) : Integer.Sparse.eval row5553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5553, Integer.Sparse.eval_collectBalanced, rawRowCheck5553]

theorem rawRowCheck5554 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5554 := by decide +kernel

theorem rowCheck5554 : row5554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5554 := by decide +kernel

theorem rowEval5554 (x : Key → ℝ) : Integer.Sparse.eval row5554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5554, Integer.Sparse.eval_collectBalanced, rawRowCheck5554]

theorem rawRowCheck5555 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5555 := by decide +kernel

theorem rowCheck5555 : row5555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5555 := by decide +kernel

theorem rowEval5555 (x : Key → ℝ) : Integer.Sparse.eval row5555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5555, Integer.Sparse.eval_collectBalanced, rawRowCheck5555]

theorem rawRowCheck5556 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5556 := by decide +kernel

theorem rowCheck5556 : row5556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5556 := by decide +kernel

theorem rowEval5556 (x : Key → ℝ) : Integer.Sparse.eval row5556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5556, Integer.Sparse.eval_collectBalanced, rawRowCheck5556]

theorem rawRowCheck5557 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5557 := by decide +kernel

theorem rowCheck5557 : row5557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5557 := by decide +kernel

theorem rowEval5557 (x : Key → ℝ) : Integer.Sparse.eval row5557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5557, Integer.Sparse.eval_collectBalanced, rawRowCheck5557]

theorem rawRowCheck5558 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5558 := by decide +kernel

theorem rowCheck5558 : row5558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5558 := by decide +kernel

theorem rowEval5558 (x : Key → ℝ) : Integer.Sparse.eval row5558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5558, Integer.Sparse.eval_collectBalanced, rawRowCheck5558]

theorem rawRowCheck5559 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5559 := by decide +kernel

theorem rowCheck5559 : row5559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5559 := by decide +kernel

theorem rowEval5559 (x : Key → ℝ) : Integer.Sparse.eval row5559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5559, Integer.Sparse.eval_collectBalanced, rawRowCheck5559]

theorem rawRowCheck5560 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5560 := by decide +kernel

theorem rowCheck5560 : row5560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5560 := by decide +kernel

theorem rowEval5560 (x : Key → ℝ) : Integer.Sparse.eval row5560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5560, Integer.Sparse.eval_collectBalanced, rawRowCheck5560]

theorem rawRowCheck5561 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5561 := by decide +kernel

theorem rowCheck5561 : row5561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5561 := by decide +kernel

theorem rowEval5561 (x : Key → ℝ) : Integer.Sparse.eval row5561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5561, Integer.Sparse.eval_collectBalanced, rawRowCheck5561]

theorem rawRowCheck5562 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5562 := by decide +kernel

theorem rowCheck5562 : row5562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5562 := by decide +kernel

theorem rowEval5562 (x : Key → ℝ) : Integer.Sparse.eval row5562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5562, Integer.Sparse.eval_collectBalanced, rawRowCheck5562]

theorem rawRowCheck5563 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5563 := by decide +kernel

theorem rowCheck5563 : row5563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5563 := by decide +kernel

theorem rowEval5563 (x : Key → ℝ) : Integer.Sparse.eval row5563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5563, Integer.Sparse.eval_collectBalanced, rawRowCheck5563]

theorem rawRowCheck5564 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5564 := by decide +kernel

theorem rowCheck5564 : row5564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5564 := by decide +kernel

theorem rowEval5564 (x : Key → ℝ) : Integer.Sparse.eval row5564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5564, Integer.Sparse.eval_collectBalanced, rawRowCheck5564]

theorem rawRowCheck5565 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1 = rawRow5565 := by decide +kernel

theorem rowCheck5565 : row5565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5565 := by decide +kernel

theorem rowEval5565 (x : Key → ℝ) : Integer.Sparse.eval row5565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5565, Integer.Sparse.eval_collectBalanced, rawRowCheck5565]

theorem rawRowCheck5566 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1 = rawRow5566 := by decide +kernel

theorem rowCheck5566 : row5566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5566 := by decide +kernel

theorem rowEval5566 (x : Key → ℝ) : Integer.Sparse.eval row5566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5566, Integer.Sparse.eval_collectBalanced, rawRowCheck5566]

theorem rawRowCheck5567 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1 = rawRow5567 := by decide +kernel

theorem rowCheck5567 : row5567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5567 := by decide +kernel

theorem rowEval5567 (x : Key → ℝ) : Integer.Sparse.eval row5567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5567, Integer.Sparse.eval_collectBalanced, rawRowCheck5567]

theorem rawRowCheck5598 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5598 := by decide +kernel

theorem rowCheck5598 : row5598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5598 := by decide +kernel

theorem rowEval5598 (x : Key → ℝ) : Integer.Sparse.eval row5598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5598, Integer.Sparse.eval_collectBalanced, rawRowCheck5598]

theorem rawRowCheck5599 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5599 := by decide +kernel

theorem rowCheck5599 : row5599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5599 := by decide +kernel

theorem rowEval5599 (x : Key → ℝ) : Integer.Sparse.eval row5599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5599, Integer.Sparse.eval_collectBalanced, rawRowCheck5599]

theorem rawRowCheck5600 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5600 := by decide +kernel

theorem rowCheck5600 : row5600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5600 := by decide +kernel

theorem rowEval5600 (x : Key → ℝ) : Integer.Sparse.eval row5600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5600, Integer.Sparse.eval_collectBalanced, rawRowCheck5600]

theorem rawRowCheck5601 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5601 := by decide +kernel

theorem rowCheck5601 : row5601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5601 := by decide +kernel

theorem rowEval5601 (x : Key → ℝ) : Integer.Sparse.eval row5601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5601, Integer.Sparse.eval_collectBalanced, rawRowCheck5601]

theorem rawRowCheck5602 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5602 := by decide +kernel

theorem rowCheck5602 : row5602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5602 := by decide +kernel

theorem rowEval5602 (x : Key → ℝ) : Integer.Sparse.eval row5602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5602, Integer.Sparse.eval_collectBalanced, rawRowCheck5602]

theorem rawRowCheck5603 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5603 := by decide +kernel

theorem rowCheck5603 : row5603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5603 := by decide +kernel

theorem rowEval5603 (x : Key → ℝ) : Integer.Sparse.eval row5603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5603, Integer.Sparse.eval_collectBalanced, rawRowCheck5603]

theorem rawRowCheck5604 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5604 := by decide +kernel

theorem rowCheck5604 : row5604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5604 := by decide +kernel

theorem rowEval5604 (x : Key → ℝ) : Integer.Sparse.eval row5604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5604, Integer.Sparse.eval_collectBalanced, rawRowCheck5604]

theorem rawRowCheck5605 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5605 := by decide +kernel

theorem rowCheck5605 : row5605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5605 := by decide +kernel

theorem rowEval5605 (x : Key → ℝ) : Integer.Sparse.eval row5605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5605, Integer.Sparse.eval_collectBalanced, rawRowCheck5605]

theorem rawRowCheck5606 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5606 := by decide +kernel

theorem rowCheck5606 : row5606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5606 := by decide +kernel

theorem rowEval5606 (x : Key → ℝ) : Integer.Sparse.eval row5606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5606, Integer.Sparse.eval_collectBalanced, rawRowCheck5606]

theorem rawRowCheck5607 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3 = rawRow5607 := by decide +kernel

theorem rowCheck5607 : row5607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5607 := by decide +kernel

theorem rowEval5607 (x : Key → ℝ) : Integer.Sparse.eval row5607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5607, Integer.Sparse.eval_collectBalanced, rawRowCheck5607]

theorem rawRowCheck5608 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3 = rawRow5608 := by decide +kernel

theorem rowCheck5608 : row5608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5608 := by decide +kernel

theorem rowEval5608 (x : Key → ℝ) : Integer.Sparse.eval row5608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5608, Integer.Sparse.eval_collectBalanced, rawRowCheck5608]

theorem rawRowCheck5609 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3 = rawRow5609 := by decide +kernel

theorem rowCheck5609 : row5609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5609 := by decide +kernel

theorem rowEval5609 (x : Key → ℝ) : Integer.Sparse.eval row5609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5609, Integer.Sparse.eval_collectBalanced, rawRowCheck5609]

theorem rawRowCheck5610 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5610 := by decide +kernel

theorem rowCheck5610 : row5610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5610 := by decide +kernel

theorem rowEval5610 (x : Key → ℝ) : Integer.Sparse.eval row5610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5610, Integer.Sparse.eval_collectBalanced, rawRowCheck5610]

theorem rawRowCheck5611 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5611 := by decide +kernel

theorem rowCheck5611 : row5611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5611 := by decide +kernel

theorem rowEval5611 (x : Key → ℝ) : Integer.Sparse.eval row5611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5611, Integer.Sparse.eval_collectBalanced, rawRowCheck5611]

theorem rawRowCheck5612 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5612 := by decide +kernel

theorem rowCheck5612 : row5612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5612 := by decide +kernel

theorem rowEval5612 (x : Key → ℝ) : Integer.Sparse.eval row5612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5612, Integer.Sparse.eval_collectBalanced, rawRowCheck5612]

theorem rawRowCheck5613 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5613 := by decide +kernel

theorem rowCheck5613 : row5613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5613 := by decide +kernel

theorem rowEval5613 (x : Key → ℝ) : Integer.Sparse.eval row5613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5613, Integer.Sparse.eval_collectBalanced, rawRowCheck5613]

theorem rawRowCheck5614 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5614 := by decide +kernel

theorem rowCheck5614 : row5614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5614 := by decide +kernel

theorem rowEval5614 (x : Key → ℝ) : Integer.Sparse.eval row5614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5614, Integer.Sparse.eval_collectBalanced, rawRowCheck5614]

theorem rawRowCheck5615 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5615 := by decide +kernel

theorem rowCheck5615 : row5615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5615 := by decide +kernel

theorem rowEval5615 (x : Key → ℝ) : Integer.Sparse.eval row5615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5615, Integer.Sparse.eval_collectBalanced, rawRowCheck5615]

theorem rawRowCheck5616 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5616 := by decide +kernel

theorem rowCheck5616 : row5616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5616 := by decide +kernel

theorem rowEval5616 (x : Key → ℝ) : Integer.Sparse.eval row5616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5616, Integer.Sparse.eval_collectBalanced, rawRowCheck5616]

theorem rawRowCheck5617 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5617 := by decide +kernel

theorem rowCheck5617 : row5617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5617 := by decide +kernel

theorem rowEval5617 (x : Key → ℝ) : Integer.Sparse.eval row5617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5617, Integer.Sparse.eval_collectBalanced, rawRowCheck5617]

theorem rawRowCheck5618 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5618 := by decide +kernel

theorem rowCheck5618 : row5618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5618 := by decide +kernel

theorem rowEval5618 (x : Key → ℝ) : Integer.Sparse.eval row5618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5618, Integer.Sparse.eval_collectBalanced, rawRowCheck5618]

theorem rawRowCheck5619 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5619 := by decide +kernel

theorem rowCheck5619 : row5619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5619 := by decide +kernel

theorem rowEval5619 (x : Key → ℝ) : Integer.Sparse.eval row5619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5619, Integer.Sparse.eval_collectBalanced, rawRowCheck5619]

theorem rawRowCheck5620 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5620 := by decide +kernel

theorem rowCheck5620 : row5620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5620 := by decide +kernel

theorem rowEval5620 (x : Key → ℝ) : Integer.Sparse.eval row5620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5620, Integer.Sparse.eval_collectBalanced, rawRowCheck5620]

theorem rawRowCheck5621 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5621 := by decide +kernel

theorem rowCheck5621 : row5621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5621 := by decide +kernel

theorem rowEval5621 (x : Key → ℝ) : Integer.Sparse.eval row5621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5621, Integer.Sparse.eval_collectBalanced, rawRowCheck5621]

theorem rawRowCheck5622 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5622 := by decide +kernel

theorem rowCheck5622 : row5622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5622 := by decide +kernel

theorem rowEval5622 (x : Key → ℝ) : Integer.Sparse.eval row5622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5622, Integer.Sparse.eval_collectBalanced, rawRowCheck5622]

theorem rawRowCheck5623 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5623 := by decide +kernel

theorem rowCheck5623 : row5623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5623 := by decide +kernel

theorem rowEval5623 (x : Key → ℝ) : Integer.Sparse.eval row5623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5623, Integer.Sparse.eval_collectBalanced, rawRowCheck5623]

theorem rawRowCheck5624 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5624 := by decide +kernel

theorem rowCheck5624 : row5624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5624 := by decide +kernel

theorem rowEval5624 (x : Key → ℝ) : Integer.Sparse.eval row5624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5624, Integer.Sparse.eval_collectBalanced, rawRowCheck5624]

theorem rawRowCheck5625 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3 = rawRow5625 := by decide +kernel

theorem rowCheck5625 : row5625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5625 := by decide +kernel

theorem rowEval5625 (x : Key → ℝ) : Integer.Sparse.eval row5625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5625, Integer.Sparse.eval_collectBalanced, rawRowCheck5625]

theorem rawRowCheck5626 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3 = rawRow5626 := by decide +kernel

theorem rowCheck5626 : row5626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5626 := by decide +kernel

theorem rowEval5626 (x : Key → ℝ) : Integer.Sparse.eval row5626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5626, Integer.Sparse.eval_collectBalanced, rawRowCheck5626]

theorem rawRowCheck5627 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3 = rawRow5627 := by decide +kernel

theorem rowCheck5627 : row5627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5627 := by decide +kernel

theorem rowEval5627 (x : Key → ℝ) : Integer.Sparse.eval row5627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5627, Integer.Sparse.eval_collectBalanced, rawRowCheck5627]

theorem rawRowCheck5628 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form4 = rawRow5628 := by decide +kernel

theorem rowCheck5628 : row5628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5628 := by decide +kernel

theorem rowEval5628 (x : Key → ℝ) : Integer.Sparse.eval row5628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5628, Integer.Sparse.eval_collectBalanced, rawRowCheck5628]

theorem rawRowCheck5629 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form4 = rawRow5629 := by decide +kernel

theorem rowCheck5629 : row5629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5629 := by decide +kernel

theorem rowEval5629 (x : Key → ℝ) : Integer.Sparse.eval row5629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5629, Integer.Sparse.eval_collectBalanced, rawRowCheck5629]

theorem rawRowCheck5630 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form4 = rawRow5630 := by decide +kernel

theorem rowCheck5630 : row5630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5630 := by decide +kernel

theorem rowEval5630 (x : Key → ℝ) : Integer.Sparse.eval row5630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5630, Integer.Sparse.eval_collectBalanced, rawRowCheck5630]

theorem rawRowCheck5631 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow5631 := by decide +kernel

theorem rowCheck5631 : row5631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5631 := by decide +kernel

theorem rowEval5631 (x : Key → ℝ) : Integer.Sparse.eval row5631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5631, Integer.Sparse.eval_collectBalanced, rawRowCheck5631]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5632 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow5632 := by decide +kernel

theorem rowCheck5632 : row5632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5632 := by decide +kernel

theorem rowEval5632 (x : Key → ℝ) : Integer.Sparse.eval row5632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5632, Integer.Sparse.eval_collectBalanced, rawRowCheck5632]

theorem rawRowCheck5633 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow5633 := by decide +kernel

theorem rowCheck5633 : row5633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5633 := by decide +kernel

theorem rowEval5633 (x : Key → ℝ) : Integer.Sparse.eval row5633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5633, Integer.Sparse.eval_collectBalanced, rawRowCheck5633]

theorem rawRowCheck5634 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form4 = rawRow5634 := by decide +kernel

theorem rowCheck5634 : row5634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5634 := by decide +kernel

theorem rowEval5634 (x : Key → ℝ) : Integer.Sparse.eval row5634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5634, Integer.Sparse.eval_collectBalanced, rawRowCheck5634]

theorem rawRowCheck5635 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form4 = rawRow5635 := by decide +kernel

theorem rowCheck5635 : row5635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5635 := by decide +kernel

theorem rowEval5635 (x : Key → ℝ) : Integer.Sparse.eval row5635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5635, Integer.Sparse.eval_collectBalanced, rawRowCheck5635]

theorem rawRowCheck5636 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form4 = rawRow5636 := by decide +kernel

theorem rowCheck5636 : row5636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5636 := by decide +kernel

theorem rowEval5636 (x : Key → ℝ) : Integer.Sparse.eval row5636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5636, Integer.Sparse.eval_collectBalanced, rawRowCheck5636]

theorem rawRowCheck5637 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form4 = rawRow5637 := by decide +kernel

theorem rowCheck5637 : row5637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5637 := by decide +kernel

theorem rowEval5637 (x : Key → ℝ) : Integer.Sparse.eval row5637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5637, Integer.Sparse.eval_collectBalanced, rawRowCheck5637]

theorem rawRowCheck5638 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form4 = rawRow5638 := by decide +kernel

theorem rowCheck5638 : row5638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5638 := by decide +kernel

theorem rowEval5638 (x : Key → ℝ) : Integer.Sparse.eval row5638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5638, Integer.Sparse.eval_collectBalanced, rawRowCheck5638]

theorem rawRowCheck5639 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form4 = rawRow5639 := by decide +kernel

theorem rowCheck5639 : row5639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5639 := by decide +kernel

theorem rowEval5639 (x : Key → ℝ) : Integer.Sparse.eval row5639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5639, Integer.Sparse.eval_collectBalanced, rawRowCheck5639]

theorem rawRowCheck5640 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form4 = rawRow5640 := by decide +kernel

theorem rowCheck5640 : row5640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5640 := by decide +kernel

theorem rowEval5640 (x : Key → ℝ) : Integer.Sparse.eval row5640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5640, Integer.Sparse.eval_collectBalanced, rawRowCheck5640]

theorem rawRowCheck5641 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form4 = rawRow5641 := by decide +kernel

theorem rowCheck5641 : row5641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5641 := by decide +kernel

theorem rowEval5641 (x : Key → ℝ) : Integer.Sparse.eval row5641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5641, Integer.Sparse.eval_collectBalanced, rawRowCheck5641]

theorem rawRowCheck5642 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form4 = rawRow5642 := by decide +kernel

theorem rowCheck5642 : row5642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5642 := by decide +kernel

theorem rowEval5642 (x : Key → ℝ) : Integer.Sparse.eval row5642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5642, Integer.Sparse.eval_collectBalanced, rawRowCheck5642]

theorem rawRowCheck5643 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form4 = rawRow5643 := by decide +kernel

theorem rowCheck5643 : row5643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5643 := by decide +kernel

theorem rowEval5643 (x : Key → ℝ) : Integer.Sparse.eval row5643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5643, Integer.Sparse.eval_collectBalanced, rawRowCheck5643]

theorem rawRowCheck5644 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form4 = rawRow5644 := by decide +kernel

theorem rowCheck5644 : row5644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5644 := by decide +kernel

theorem rowEval5644 (x : Key → ℝ) : Integer.Sparse.eval row5644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5644, Integer.Sparse.eval_collectBalanced, rawRowCheck5644]

theorem rawRowCheck5645 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form4 = rawRow5645 := by decide +kernel

theorem rowCheck5645 : row5645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5645 := by decide +kernel

theorem rowEval5645 (x : Key → ℝ) : Integer.Sparse.eval row5645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5645, Integer.Sparse.eval_collectBalanced, rawRowCheck5645]

theorem rawRowCheck5646 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form4 = rawRow5646 := by decide +kernel

theorem rowCheck5646 : row5646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5646 := by decide +kernel

theorem rowEval5646 (x : Key → ℝ) : Integer.Sparse.eval row5646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5646, Integer.Sparse.eval_collectBalanced, rawRowCheck5646]

theorem rawRowCheck5647 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form4 = rawRow5647 := by decide +kernel

theorem rowCheck5647 : row5647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5647 := by decide +kernel

theorem rowEval5647 (x : Key → ℝ) : Integer.Sparse.eval row5647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5647, Integer.Sparse.eval_collectBalanced, rawRowCheck5647]

theorem rawRowCheck5648 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form4 = rawRow5648 := by decide +kernel

theorem rowCheck5648 : row5648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5648 := by decide +kernel

theorem rowEval5648 (x : Key → ℝ) : Integer.Sparse.eval row5648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5648, Integer.Sparse.eval_collectBalanced, rawRowCheck5648]

theorem rawRowCheck5649 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form4 = rawRow5649 := by decide +kernel

theorem rowCheck5649 : row5649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5649 := by decide +kernel

theorem rowEval5649 (x : Key → ℝ) : Integer.Sparse.eval row5649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5649, Integer.Sparse.eval_collectBalanced, rawRowCheck5649]

theorem rawRowCheck5650 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form4 = rawRow5650 := by decide +kernel

theorem rowCheck5650 : row5650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5650 := by decide +kernel

theorem rowEval5650 (x : Key → ℝ) : Integer.Sparse.eval row5650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5650, Integer.Sparse.eval_collectBalanced, rawRowCheck5650]

theorem rawRowCheck5651 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form4 = rawRow5651 := by decide +kernel

theorem rowCheck5651 : row5651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5651 := by decide +kernel

theorem rowEval5651 (x : Key → ℝ) : Integer.Sparse.eval row5651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5651, Integer.Sparse.eval_collectBalanced, rawRowCheck5651]

theorem rawRowCheck5652 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form4 = rawRow5652 := by decide +kernel

theorem rowCheck5652 : row5652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5652 := by decide +kernel

theorem rowEval5652 (x : Key → ℝ) : Integer.Sparse.eval row5652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5652, Integer.Sparse.eval_collectBalanced, rawRowCheck5652]

theorem rawRowCheck5653 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form4 = rawRow5653 := by decide +kernel

theorem rowCheck5653 : row5653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5653 := by decide +kernel

theorem rowEval5653 (x : Key → ℝ) : Integer.Sparse.eval row5653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5653, Integer.Sparse.eval_collectBalanced, rawRowCheck5653]

theorem rawRowCheck5654 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form4 = rawRow5654 := by decide +kernel

theorem rowCheck5654 : row5654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5654 := by decide +kernel

theorem rowEval5654 (x : Key → ℝ) : Integer.Sparse.eval row5654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5654, Integer.Sparse.eval_collectBalanced, rawRowCheck5654]

theorem rawRowCheck5655 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form4 = rawRow5655 := by decide +kernel

theorem rowCheck5655 : row5655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5655 := by decide +kernel

theorem rowEval5655 (x : Key → ℝ) : Integer.Sparse.eval row5655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5655, Integer.Sparse.eval_collectBalanced, rawRowCheck5655]

theorem rawRowCheck5656 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form4 = rawRow5656 := by decide +kernel

theorem rowCheck5656 : row5656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5656 := by decide +kernel

theorem rowEval5656 (x : Key → ℝ) : Integer.Sparse.eval row5656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5656, Integer.Sparse.eval_collectBalanced, rawRowCheck5656]

theorem rawRowCheck5657 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form4 = rawRow5657 := by decide +kernel

theorem rowCheck5657 : row5657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5657 := by decide +kernel

theorem rowEval5657 (x : Key → ℝ) : Integer.Sparse.eval row5657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5657, Integer.Sparse.eval_collectBalanced, rawRowCheck5657]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5538 x
  · exact rowEval5539 x
  · exact rowEval5540 x
  · exact rowEval5541 x
  · exact rowEval5542 x
  · exact rowEval5543 x
  · exact rowEval5544 x
  · exact rowEval5545 x
  · exact rowEval5546 x
  · exact rowEval5547 x
  · exact rowEval5548 x
  · exact rowEval5549 x
  · exact rowEval5550 x
  · exact rowEval5551 x
  · exact rowEval5552 x
  · exact rowEval5553 x
  · exact rowEval5554 x
  · exact rowEval5555 x
  · exact rowEval5556 x
  · exact rowEval5557 x
  · exact rowEval5558 x
  · exact rowEval5559 x
  · exact rowEval5560 x
  · exact rowEval5561 x
  · exact rowEval5562 x
  · exact rowEval5563 x
  · exact rowEval5564 x
  · exact rowEval5565 x
  · exact rowEval5566 x
  · exact rowEval5567 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval5598 x
  · exact rowEval5599 x
  · exact rowEval5600 x
  · exact rowEval5601 x
  · exact rowEval5602 x
  · exact rowEval5603 x
  · exact rowEval5604 x
  · exact rowEval5605 x
  · exact rowEval5606 x
  · exact rowEval5607 x
  · exact rowEval5608 x
  · exact rowEval5609 x
  · exact rowEval5610 x
  · exact rowEval5611 x
  · exact rowEval5612 x
  · exact rowEval5613 x
  · exact rowEval5614 x
  · exact rowEval5615 x
  · exact rowEval5616 x
  · exact rowEval5617 x
  · exact rowEval5618 x
  · exact rowEval5619 x
  · exact rowEval5620 x
  · exact rowEval5621 x
  · exact rowEval5622 x
  · exact rowEval5623 x
  · exact rowEval5624 x
  · exact rowEval5625 x
  · exact rowEval5626 x
  · exact rowEval5627 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block2.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form4.terms k).tag (GramFunctions.Block2.form4.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval5628 x
  · exact rowEval5629 x
  · exact rowEval5630 x
  · exact rowEval5631 x
  · exact rowEval5632 x
  · exact rowEval5633 x
  · exact rowEval5634 x
  · exact rowEval5635 x
  · exact rowEval5636 x
  · exact rowEval5637 x
  · exact rowEval5638 x
  · exact rowEval5639 x
  · exact rowEval5640 x
  · exact rowEval5641 x
  · exact rowEval5642 x
  · exact rowEval5643 x
  · exact rowEval5644 x
  · exact rowEval5645 x
  · exact rowEval5646 x
  · exact rowEval5647 x
  · exact rowEval5648 x
  · exact rowEval5649 x
  · exact rowEval5650 x
  · exact rowEval5651 x
  · exact rowEval5652 x
  · exact rowEval5653 x
  · exact rowEval5654 x
  · exact rowEval5655 x
  · exact rowEval5656 x
  · exact rowEval5657 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block2.form4.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form4 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck6838 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow6838 := by decide +kernel

theorem rowCheck6838 : row6838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6838 := by decide +kernel

theorem rowEval6838 (x : Key → ℝ) : Integer.Sparse.eval row6838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6838, Integer.Sparse.eval_collectBalanced, rawRowCheck6838]

theorem rawRowCheck6839 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow6839 := by decide +kernel

theorem rowCheck6839 : row6839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6839 := by decide +kernel

theorem rowEval6839 (x : Key → ℝ) : Integer.Sparse.eval row6839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6839, Integer.Sparse.eval_collectBalanced, rawRowCheck6839]

theorem rawRowCheck6840 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow6840 := by decide +kernel

theorem rowCheck6840 : row6840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6840 := by decide +kernel

theorem rowEval6840 (x : Key → ℝ) : Integer.Sparse.eval row6840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6840, Integer.Sparse.eval_collectBalanced, rawRowCheck6840]

theorem rawRowCheck6841 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6841 := by decide +kernel

theorem rowCheck6841 : row6841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6841 := by decide +kernel

theorem rowEval6841 (x : Key → ℝ) : Integer.Sparse.eval row6841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6841, Integer.Sparse.eval_collectBalanced, rawRowCheck6841]

theorem rawRowCheck6842 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6842 := by decide +kernel

theorem rowCheck6842 : row6842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6842 := by decide +kernel

theorem rowEval6842 (x : Key → ℝ) : Integer.Sparse.eval row6842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6842, Integer.Sparse.eval_collectBalanced, rawRowCheck6842]

theorem rawRowCheck6843 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6843 := by decide +kernel

theorem rowCheck6843 : row6843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6843 := by decide +kernel

theorem rowEval6843 (x : Key → ℝ) : Integer.Sparse.eval row6843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6843, Integer.Sparse.eval_collectBalanced, rawRowCheck6843]

theorem rawRowCheck6844 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6844 := by decide +kernel

theorem rowCheck6844 : row6844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6844 := by decide +kernel

theorem rowEval6844 (x : Key → ℝ) : Integer.Sparse.eval row6844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6844, Integer.Sparse.eval_collectBalanced, rawRowCheck6844]

theorem rawRowCheck6845 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6845 := by decide +kernel

theorem rowCheck6845 : row6845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6845 := by decide +kernel

theorem rowEval6845 (x : Key → ℝ) : Integer.Sparse.eval row6845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6845, Integer.Sparse.eval_collectBalanced, rawRowCheck6845]

theorem rawRowCheck6846 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6846 := by decide +kernel

theorem rowCheck6846 : row6846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6846 := by decide +kernel

theorem rowEval6846 (x : Key → ℝ) : Integer.Sparse.eval row6846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6846, Integer.Sparse.eval_collectBalanced, rawRowCheck6846]

theorem rawRowCheck6847 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6847 := by decide +kernel

theorem rowCheck6847 : row6847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6847 := by decide +kernel

theorem rowEval6847 (x : Key → ℝ) : Integer.Sparse.eval row6847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6847, Integer.Sparse.eval_collectBalanced, rawRowCheck6847]

theorem rawRowCheck6848 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6848 := by decide +kernel

theorem rowCheck6848 : row6848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6848 := by decide +kernel

theorem rowEval6848 (x : Key → ℝ) : Integer.Sparse.eval row6848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6848, Integer.Sparse.eval_collectBalanced, rawRowCheck6848]

theorem rawRowCheck6849 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6849 := by decide +kernel

theorem rowCheck6849 : row6849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6849 := by decide +kernel

theorem rowEval6849 (x : Key → ℝ) : Integer.Sparse.eval row6849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6849, Integer.Sparse.eval_collectBalanced, rawRowCheck6849]

theorem rawRowCheck6850 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6850 := by decide +kernel

theorem rowCheck6850 : row6850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6850 := by decide +kernel

theorem rowEval6850 (x : Key → ℝ) : Integer.Sparse.eval row6850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6850, Integer.Sparse.eval_collectBalanced, rawRowCheck6850]

theorem rawRowCheck6851 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6851 := by decide +kernel

theorem rowCheck6851 : row6851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6851 := by decide +kernel

theorem rowEval6851 (x : Key → ℝ) : Integer.Sparse.eval row6851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6851, Integer.Sparse.eval_collectBalanced, rawRowCheck6851]

theorem rawRowCheck6852 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6852 := by decide +kernel

theorem rowCheck6852 : row6852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6852 := by decide +kernel

theorem rowEval6852 (x : Key → ℝ) : Integer.Sparse.eval row6852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6852, Integer.Sparse.eval_collectBalanced, rawRowCheck6852]

theorem rawRowCheck6853 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6853 := by decide +kernel

theorem rowCheck6853 : row6853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6853 := by decide +kernel

theorem rowEval6853 (x : Key → ℝ) : Integer.Sparse.eval row6853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6853, Integer.Sparse.eval_collectBalanced, rawRowCheck6853]

theorem rawRowCheck6854 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6854 := by decide +kernel

theorem rowCheck6854 : row6854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6854 := by decide +kernel

theorem rowEval6854 (x : Key → ℝ) : Integer.Sparse.eval row6854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6854, Integer.Sparse.eval_collectBalanced, rawRowCheck6854]

theorem rawRowCheck6855 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6855 := by decide +kernel

theorem rowCheck6855 : row6855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6855 := by decide +kernel

theorem rowEval6855 (x : Key → ℝ) : Integer.Sparse.eval row6855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6855, Integer.Sparse.eval_collectBalanced, rawRowCheck6855]

theorem rawRowCheck6856 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4 = rawRow6856 := by decide +kernel

theorem rowCheck6856 : row6856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6856 := by decide +kernel

theorem rowEval6856 (x : Key → ℝ) : Integer.Sparse.eval row6856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6856, Integer.Sparse.eval_collectBalanced, rawRowCheck6856]

theorem rawRowCheck6857 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4 = rawRow6857 := by decide +kernel

theorem rowCheck6857 : row6857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6857 := by decide +kernel

theorem rowEval6857 (x : Key → ℝ) : Integer.Sparse.eval row6857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6857, Integer.Sparse.eval_collectBalanced, rawRowCheck6857]

theorem rawRowCheck6858 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4 = rawRow6858 := by decide +kernel

theorem rowCheck6858 : row6858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6858 := by decide +kernel

theorem rowEval6858 (x : Key → ℝ) : Integer.Sparse.eval row6858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6858, Integer.Sparse.eval_collectBalanced, rawRowCheck6858]

theorem rawRowCheck6859 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6859 := by decide +kernel

theorem rowCheck6859 : row6859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6859 := by decide +kernel

theorem rowEval6859 (x : Key → ℝ) : Integer.Sparse.eval row6859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6859, Integer.Sparse.eval_collectBalanced, rawRowCheck6859]

theorem rawRowCheck6860 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6860 := by decide +kernel

theorem rowCheck6860 : row6860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6860 := by decide +kernel

theorem rowEval6860 (x : Key → ℝ) : Integer.Sparse.eval row6860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6860, Integer.Sparse.eval_collectBalanced, rawRowCheck6860]

theorem rawRowCheck6861 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6861 := by decide +kernel

theorem rowCheck6861 : row6861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6861 := by decide +kernel

theorem rowEval6861 (x : Key → ℝ) : Integer.Sparse.eval row6861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6861, Integer.Sparse.eval_collectBalanced, rawRowCheck6861]

theorem rawRowCheck6862 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6862 := by decide +kernel

theorem rowCheck6862 : row6862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6862 := by decide +kernel

theorem rowEval6862 (x : Key → ℝ) : Integer.Sparse.eval row6862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6862, Integer.Sparse.eval_collectBalanced, rawRowCheck6862]

theorem rawRowCheck6863 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6863 := by decide +kernel

theorem rowCheck6863 : row6863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6863 := by decide +kernel

theorem rowEval6863 (x : Key → ℝ) : Integer.Sparse.eval row6863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6863, Integer.Sparse.eval_collectBalanced, rawRowCheck6863]

theorem rawRowCheck6864 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6864 := by decide +kernel

theorem rowCheck6864 : row6864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6864 := by decide +kernel

theorem rowEval6864 (x : Key → ℝ) : Integer.Sparse.eval row6864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6864, Integer.Sparse.eval_collectBalanced, rawRowCheck6864]

theorem rawRowCheck6865 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4 = rawRow6865 := by decide +kernel

theorem rowCheck6865 : row6865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6865 := by decide +kernel

theorem rowEval6865 (x : Key → ℝ) : Integer.Sparse.eval row6865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6865, Integer.Sparse.eval_collectBalanced, rawRowCheck6865]

theorem rawRowCheck6866 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4 = rawRow6866 := by decide +kernel

theorem rowCheck6866 : row6866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6866 := by decide +kernel

theorem rowEval6866 (x : Key → ℝ) : Integer.Sparse.eval row6866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6866, Integer.Sparse.eval_collectBalanced, rawRowCheck6866]

theorem rawRowCheck6867 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4 = rawRow6867 := by decide +kernel

theorem rowCheck6867 : row6867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6867 := by decide +kernel

theorem rowEval6867 (x : Key → ℝ) : Integer.Sparse.eval row6867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6867, Integer.Sparse.eval_collectBalanced, rawRowCheck6867]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block2.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form9.terms k).tag (GramFunctions.Block2.form9.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6838 x
  · exact rowEval6839 x
  · exact rowEval6840 x
  · exact rowEval6841 x
  · exact rowEval6842 x
  · exact rowEval6843 x
  · exact rowEval6844 x
  · exact rowEval6845 x
  · exact rowEval6846 x
  · exact rowEval6847 x
  · exact rowEval6848 x
  · exact rowEval6849 x
  · exact rowEval6850 x
  · exact rowEval6851 x
  · exact rowEval6852 x
  · exact rowEval6853 x
  · exact rowEval6854 x
  · exact rowEval6855 x
  · exact rowEval6856 x
  · exact rowEval6857 x
  · exact rowEval6858 x
  · exact rowEval6859 x
  · exact rowEval6860 x
  · exact rowEval6861 x
  · exact rowEval6862 x
  · exact rowEval6863 x
  · exact rowEval6864 x
  · exact rowEval6865 x
  · exact rowEval6866 x
  · exact rowEval6867 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block2.form9.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form9 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

theorem entryEvalRow4_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 4 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 4).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval4_0_e B hB
  · exact entryEval4_1 B hB
  · exact entryEval4_2_e B hB
  · exact entryEval4_3 B hB
  · exact entryEval4_4 B hB
  · exact (entryEval5_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_4_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_4 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow4_e_oai
