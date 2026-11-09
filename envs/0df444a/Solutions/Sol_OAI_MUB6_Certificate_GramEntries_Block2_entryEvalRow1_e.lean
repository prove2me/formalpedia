-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:51:49.412888+00:00
-- url     : https://prove2.me/submissions/fcea8df8-4c37-4d7c-a5be-54e5f9a1a42b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E053
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval1_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval1_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval2_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval5_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval6_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval7_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval8_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval9_1_e

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

theorem rawRowCheck7048 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7048 := by decide +kernel

theorem rowCheck7048 : row7048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7048 := by decide +kernel

theorem rowEval7048 (x : Key → ℝ) : Integer.Sparse.eval row7048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7048, Integer.Sparse.eval_collectBalanced, rawRowCheck7048]

theorem rawRowCheck7049 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7049 := by decide +kernel

theorem rowCheck7049 : row7049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7049 := by decide +kernel

theorem rowEval7049 (x : Key → ℝ) : Integer.Sparse.eval row7049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7049, Integer.Sparse.eval_collectBalanced, rawRowCheck7049]

theorem rawRowCheck7050 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7050 := by decide +kernel

theorem rowCheck7050 : row7050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7050 := by decide +kernel

theorem rowEval7050 (x : Key → ℝ) : Integer.Sparse.eval row7050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7050, Integer.Sparse.eval_collectBalanced, rawRowCheck7050]

theorem rawRowCheck7051 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7051 := by decide +kernel

theorem rowCheck7051 : row7051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7051 := by decide +kernel

theorem rowEval7051 (x : Key → ℝ) : Integer.Sparse.eval row7051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7051, Integer.Sparse.eval_collectBalanced, rawRowCheck7051]

theorem rawRowCheck7052 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7052 := by decide +kernel

theorem rowCheck7052 : row7052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7052 := by decide +kernel

theorem rowEval7052 (x : Key → ℝ) : Integer.Sparse.eval row7052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7052, Integer.Sparse.eval_collectBalanced, rawRowCheck7052]

theorem rawRowCheck7053 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7053 := by decide +kernel

theorem rowCheck7053 : row7053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7053 := by decide +kernel

theorem rowEval7053 (x : Key → ℝ) : Integer.Sparse.eval row7053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7053, Integer.Sparse.eval_collectBalanced, rawRowCheck7053]

theorem rawRowCheck7054 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7054 := by decide +kernel

theorem rowCheck7054 : row7054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7054 := by decide +kernel

theorem rowEval7054 (x : Key → ℝ) : Integer.Sparse.eval row7054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7054, Integer.Sparse.eval_collectBalanced, rawRowCheck7054]

theorem rawRowCheck7055 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7055 := by decide +kernel

theorem rowCheck7055 : row7055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7055 := by decide +kernel

theorem rowEval7055 (x : Key → ℝ) : Integer.Sparse.eval row7055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7055, Integer.Sparse.eval_collectBalanced, rawRowCheck7055]

theorem rawRowCheck7056 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7056 := by decide +kernel

theorem rowCheck7056 : row7056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7056 := by decide +kernel

theorem rowEval7056 (x : Key → ℝ) : Integer.Sparse.eval row7056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7056, Integer.Sparse.eval_collectBalanced, rawRowCheck7056]

theorem rawRowCheck7057 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1 = rawRow7057 := by decide +kernel

theorem rowCheck7057 : row7057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7057 := by decide +kernel

theorem rowEval7057 (x : Key → ℝ) : Integer.Sparse.eval row7057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7057, Integer.Sparse.eval_collectBalanced, rawRowCheck7057]

theorem rawRowCheck7058 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1 = rawRow7058 := by decide +kernel

theorem rowCheck7058 : row7058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7058 := by decide +kernel

theorem rowEval7058 (x : Key → ℝ) : Integer.Sparse.eval row7058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7058, Integer.Sparse.eval_collectBalanced, rawRowCheck7058]

theorem rawRowCheck7059 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1 = rawRow7059 := by decide +kernel

theorem rowCheck7059 : row7059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7059 := by decide +kernel

theorem rowEval7059 (x : Key → ℝ) : Integer.Sparse.eval row7059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7059, Integer.Sparse.eval_collectBalanced, rawRowCheck7059]

theorem rawRowCheck7060 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7060 := by decide +kernel

theorem rowCheck7060 : row7060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7060 := by decide +kernel

theorem rowEval7060 (x : Key → ℝ) : Integer.Sparse.eval row7060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7060, Integer.Sparse.eval_collectBalanced, rawRowCheck7060]

theorem rawRowCheck7061 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7061 := by decide +kernel

theorem rowCheck7061 : row7061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7061 := by decide +kernel

theorem rowEval7061 (x : Key → ℝ) : Integer.Sparse.eval row7061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7061, Integer.Sparse.eval_collectBalanced, rawRowCheck7061]

theorem rawRowCheck7062 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7062 := by decide +kernel

theorem rowCheck7062 : row7062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7062 := by decide +kernel

theorem rowEval7062 (x : Key → ℝ) : Integer.Sparse.eval row7062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7062, Integer.Sparse.eval_collectBalanced, rawRowCheck7062]

theorem rawRowCheck7063 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7063 := by decide +kernel

theorem rowCheck7063 : row7063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7063 := by decide +kernel

theorem rowEval7063 (x : Key → ℝ) : Integer.Sparse.eval row7063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7063, Integer.Sparse.eval_collectBalanced, rawRowCheck7063]

theorem rawRowCheck7064 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7064 := by decide +kernel

theorem rowCheck7064 : row7064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7064 := by decide +kernel

theorem rowEval7064 (x : Key → ℝ) : Integer.Sparse.eval row7064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7064, Integer.Sparse.eval_collectBalanced, rawRowCheck7064]

theorem rawRowCheck7065 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7065 := by decide +kernel

theorem rowCheck7065 : row7065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7065 := by decide +kernel

theorem rowEval7065 (x : Key → ℝ) : Integer.Sparse.eval row7065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7065, Integer.Sparse.eval_collectBalanced, rawRowCheck7065]

theorem rawRowCheck7066 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7066 := by decide +kernel

theorem rowCheck7066 : row7066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7066 := by decide +kernel

theorem rowEval7066 (x : Key → ℝ) : Integer.Sparse.eval row7066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7066, Integer.Sparse.eval_collectBalanced, rawRowCheck7066]

theorem rawRowCheck7067 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7067 := by decide +kernel

theorem rowCheck7067 : row7067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7067 := by decide +kernel

theorem rowEval7067 (x : Key → ℝ) : Integer.Sparse.eval row7067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7067, Integer.Sparse.eval_collectBalanced, rawRowCheck7067]

theorem rawRowCheck7068 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7068 := by decide +kernel

theorem rowCheck7068 : row7068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7068 := by decide +kernel

theorem rowEval7068 (x : Key → ℝ) : Integer.Sparse.eval row7068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7068, Integer.Sparse.eval_collectBalanced, rawRowCheck7068]

theorem rawRowCheck7069 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7069 := by decide +kernel

theorem rowCheck7069 : row7069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7069 := by decide +kernel

theorem rowEval7069 (x : Key → ℝ) : Integer.Sparse.eval row7069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7069, Integer.Sparse.eval_collectBalanced, rawRowCheck7069]

theorem rawRowCheck7070 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7070 := by decide +kernel

theorem rowCheck7070 : row7070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7070 := by decide +kernel

theorem rowEval7070 (x : Key → ℝ) : Integer.Sparse.eval row7070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7070, Integer.Sparse.eval_collectBalanced, rawRowCheck7070]

theorem rawRowCheck7071 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7071 := by decide +kernel

theorem rowCheck7071 : row7071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7071 := by decide +kernel

theorem rowEval7071 (x : Key → ℝ) : Integer.Sparse.eval row7071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7071, Integer.Sparse.eval_collectBalanced, rawRowCheck7071]

theorem rawRowCheck7072 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7072 := by decide +kernel

theorem rowCheck7072 : row7072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7072 := by decide +kernel

theorem rowEval7072 (x : Key → ℝ) : Integer.Sparse.eval row7072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7072, Integer.Sparse.eval_collectBalanced, rawRowCheck7072]

theorem rawRowCheck7073 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7073 := by decide +kernel

theorem rowCheck7073 : row7073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7073 := by decide +kernel

theorem rowEval7073 (x : Key → ℝ) : Integer.Sparse.eval row7073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7073, Integer.Sparse.eval_collectBalanced, rawRowCheck7073]

theorem rawRowCheck7074 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7074 := by decide +kernel

theorem rowCheck7074 : row7074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7074 := by decide +kernel

theorem rowEval7074 (x : Key → ℝ) : Integer.Sparse.eval row7074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7074, Integer.Sparse.eval_collectBalanced, rawRowCheck7074]

theorem rawRowCheck7075 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow7075 := by decide +kernel

theorem rowCheck7075 : row7075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7075 := by decide +kernel

theorem rowEval7075 (x : Key → ℝ) : Integer.Sparse.eval row7075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7075, Integer.Sparse.eval_collectBalanced, rawRowCheck7075]

theorem rawRowCheck7076 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow7076 := by decide +kernel

theorem rowCheck7076 : row7076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7076 := by decide +kernel

theorem rowEval7076 (x : Key → ℝ) : Integer.Sparse.eval row7076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7076, Integer.Sparse.eval_collectBalanced, rawRowCheck7076]

theorem rawRowCheck7077 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow7077 := by decide +kernel

theorem rowCheck7077 : row7077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7077 := by decide +kernel

theorem rowEval7077 (x : Key → ℝ) : Integer.Sparse.eval row7077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7077, Integer.Sparse.eval_collectBalanced, rawRowCheck7077]

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

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval7048 x
  · exact rowEval7049 x
  · exact rowEval7050 x
  · exact rowEval7051 x
  · exact rowEval7052 x
  · exact rowEval7053 x
  · exact rowEval7054 x
  · exact rowEval7055 x
  · exact rowEval7056 x
  · exact rowEval7057 x
  · exact rowEval7058 x
  · exact rowEval7059 x
  · exact rowEval7060 x
  · exact rowEval7061 x
  · exact rowEval7062 x
  · exact rowEval7063 x
  · exact rowEval7064 x
  · exact rowEval7065 x
  · exact rowEval7066 x
  · exact rowEval7067 x
  · exact rowEval7068 x
  · exact rowEval7069 x
  · exact rowEval7070 x
  · exact rowEval7071 x
  · exact rowEval7072 x
  · exact rowEval7073 x
  · exact rowEval7074 x
  · exact rowEval7075 x
  · exact rowEval7076 x
  · exact rowEval7077 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck5418 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5418 := by decide +kernel

theorem rowCheck5418 : row5418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5418 := by decide +kernel

theorem rowEval5418 (x : Key → ℝ) : Integer.Sparse.eval row5418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5418, Integer.Sparse.eval_collectBalanced, rawRowCheck5418]

theorem rawRowCheck5419 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5419 := by decide +kernel

theorem rowCheck5419 : row5419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5419 := by decide +kernel

theorem rowEval5419 (x : Key → ℝ) : Integer.Sparse.eval row5419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5419, Integer.Sparse.eval_collectBalanced, rawRowCheck5419]

theorem rawRowCheck5420 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5420 := by decide +kernel

theorem rowCheck5420 : row5420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5420 := by decide +kernel

theorem rowEval5420 (x : Key → ℝ) : Integer.Sparse.eval row5420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5420, Integer.Sparse.eval_collectBalanced, rawRowCheck5420]

theorem rawRowCheck5421 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5421 := by decide +kernel

theorem rowCheck5421 : row5421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5421 := by decide +kernel

theorem rowEval5421 (x : Key → ℝ) : Integer.Sparse.eval row5421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5421, Integer.Sparse.eval_collectBalanced, rawRowCheck5421]

theorem rawRowCheck5422 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5422 := by decide +kernel

theorem rowCheck5422 : row5422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5422 := by decide +kernel

theorem rowEval5422 (x : Key → ℝ) : Integer.Sparse.eval row5422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5422, Integer.Sparse.eval_collectBalanced, rawRowCheck5422]

theorem rawRowCheck5423 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5423 := by decide +kernel

theorem rowCheck5423 : row5423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5423 := by decide +kernel

theorem rowEval5423 (x : Key → ℝ) : Integer.Sparse.eval row5423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5423, Integer.Sparse.eval_collectBalanced, rawRowCheck5423]

theorem rawRowCheck5424 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5424 := by decide +kernel

theorem rowCheck5424 : row5424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5424 := by decide +kernel

theorem rowEval5424 (x : Key → ℝ) : Integer.Sparse.eval row5424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5424, Integer.Sparse.eval_collectBalanced, rawRowCheck5424]

theorem rawRowCheck5425 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5425 := by decide +kernel

theorem rowCheck5425 : row5425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5425 := by decide +kernel

theorem rowEval5425 (x : Key → ℝ) : Integer.Sparse.eval row5425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5425, Integer.Sparse.eval_collectBalanced, rawRowCheck5425]

theorem rawRowCheck5426 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5426 := by decide +kernel

theorem rowCheck5426 : row5426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5426 := by decide +kernel

theorem rowEval5426 (x : Key → ℝ) : Integer.Sparse.eval row5426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5426, Integer.Sparse.eval_collectBalanced, rawRowCheck5426]

theorem rawRowCheck5427 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1 = rawRow5427 := by decide +kernel

theorem rowCheck5427 : row5427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5427 := by decide +kernel

theorem rowEval5427 (x : Key → ℝ) : Integer.Sparse.eval row5427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5427, Integer.Sparse.eval_collectBalanced, rawRowCheck5427]

theorem rawRowCheck5428 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1 = rawRow5428 := by decide +kernel

theorem rowCheck5428 : row5428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5428 := by decide +kernel

theorem rowEval5428 (x : Key → ℝ) : Integer.Sparse.eval row5428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5428, Integer.Sparse.eval_collectBalanced, rawRowCheck5428]

theorem rawRowCheck5429 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1 = rawRow5429 := by decide +kernel

theorem rowCheck5429 : row5429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5429 := by decide +kernel

theorem rowEval5429 (x : Key → ℝ) : Integer.Sparse.eval row5429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5429, Integer.Sparse.eval_collectBalanced, rawRowCheck5429]

theorem rawRowCheck5430 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5430 := by decide +kernel

theorem rowCheck5430 : row5430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5430 := by decide +kernel

theorem rowEval5430 (x : Key → ℝ) : Integer.Sparse.eval row5430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5430, Integer.Sparse.eval_collectBalanced, rawRowCheck5430]

theorem rawRowCheck5431 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5431 := by decide +kernel

theorem rowCheck5431 : row5431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5431 := by decide +kernel

theorem rowEval5431 (x : Key → ℝ) : Integer.Sparse.eval row5431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5431, Integer.Sparse.eval_collectBalanced, rawRowCheck5431]

theorem rawRowCheck5432 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5432 := by decide +kernel

theorem rowCheck5432 : row5432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5432 := by decide +kernel

theorem rowEval5432 (x : Key → ℝ) : Integer.Sparse.eval row5432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5432, Integer.Sparse.eval_collectBalanced, rawRowCheck5432]

theorem rawRowCheck5433 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5433 := by decide +kernel

theorem rowCheck5433 : row5433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5433 := by decide +kernel

theorem rowEval5433 (x : Key → ℝ) : Integer.Sparse.eval row5433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5433, Integer.Sparse.eval_collectBalanced, rawRowCheck5433]

theorem rawRowCheck5434 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5434 := by decide +kernel

theorem rowCheck5434 : row5434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5434 := by decide +kernel

theorem rowEval5434 (x : Key → ℝ) : Integer.Sparse.eval row5434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5434, Integer.Sparse.eval_collectBalanced, rawRowCheck5434]

theorem rawRowCheck5435 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5435 := by decide +kernel

theorem rowCheck5435 : row5435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5435 := by decide +kernel

theorem rowEval5435 (x : Key → ℝ) : Integer.Sparse.eval row5435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5435, Integer.Sparse.eval_collectBalanced, rawRowCheck5435]

theorem rawRowCheck5436 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5436 := by decide +kernel

theorem rowCheck5436 : row5436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5436 := by decide +kernel

theorem rowEval5436 (x : Key → ℝ) : Integer.Sparse.eval row5436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5436, Integer.Sparse.eval_collectBalanced, rawRowCheck5436]

theorem rawRowCheck5437 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5437 := by decide +kernel

theorem rowCheck5437 : row5437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5437 := by decide +kernel

theorem rowEval5437 (x : Key → ℝ) : Integer.Sparse.eval row5437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5437, Integer.Sparse.eval_collectBalanced, rawRowCheck5437]

theorem rawRowCheck5438 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5438 := by decide +kernel

theorem rowCheck5438 : row5438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5438 := by decide +kernel

theorem rowEval5438 (x : Key → ℝ) : Integer.Sparse.eval row5438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5438, Integer.Sparse.eval_collectBalanced, rawRowCheck5438]

theorem rawRowCheck5439 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5439 := by decide +kernel

theorem rowCheck5439 : row5439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5439 := by decide +kernel

theorem rowEval5439 (x : Key → ℝ) : Integer.Sparse.eval row5439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5439, Integer.Sparse.eval_collectBalanced, rawRowCheck5439]

theorem rawRowCheck5440 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5440 := by decide +kernel

theorem rowCheck5440 : row5440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5440 := by decide +kernel

theorem rowEval5440 (x : Key → ℝ) : Integer.Sparse.eval row5440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5440, Integer.Sparse.eval_collectBalanced, rawRowCheck5440]

theorem rawRowCheck5441 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5441 := by decide +kernel

theorem rowCheck5441 : row5441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5441 := by decide +kernel

theorem rowEval5441 (x : Key → ℝ) : Integer.Sparse.eval row5441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5441, Integer.Sparse.eval_collectBalanced, rawRowCheck5441]

theorem rawRowCheck5442 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5442 := by decide +kernel

theorem rowCheck5442 : row5442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5442 := by decide +kernel

theorem rowEval5442 (x : Key → ℝ) : Integer.Sparse.eval row5442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5442, Integer.Sparse.eval_collectBalanced, rawRowCheck5442]

theorem rawRowCheck5443 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5443 := by decide +kernel

theorem rowCheck5443 : row5443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5443 := by decide +kernel

theorem rowEval5443 (x : Key → ℝ) : Integer.Sparse.eval row5443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5443, Integer.Sparse.eval_collectBalanced, rawRowCheck5443]

theorem rawRowCheck5444 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5444 := by decide +kernel

theorem rowCheck5444 : row5444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5444 := by decide +kernel

theorem rowEval5444 (x : Key → ℝ) : Integer.Sparse.eval row5444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5444, Integer.Sparse.eval_collectBalanced, rawRowCheck5444]

theorem rawRowCheck5445 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1 = rawRow5445 := by decide +kernel

theorem rowCheck5445 : row5445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5445 := by decide +kernel

theorem rowEval5445 (x : Key → ℝ) : Integer.Sparse.eval row5445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5445, Integer.Sparse.eval_collectBalanced, rawRowCheck5445]

theorem rawRowCheck5446 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1 = rawRow5446 := by decide +kernel

theorem rowCheck5446 : row5446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5446 := by decide +kernel

theorem rowEval5446 (x : Key → ℝ) : Integer.Sparse.eval row5446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5446, Integer.Sparse.eval_collectBalanced, rawRowCheck5446]

theorem rawRowCheck5447 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1 = rawRow5447 := by decide +kernel

theorem rowCheck5447 : row5447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5447 := by decide +kernel

theorem rowEval5447 (x : Key → ℝ) : Integer.Sparse.eval row5447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5447, Integer.Sparse.eval_collectBalanced, rawRowCheck5447]

end MUB6.Certificate.GramRows

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block2.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form3.terms k).tag (GramFunctions.Block2.form3.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval5418 x
  · exact rowEval5419 x
  · exact rowEval5420 x
  · exact rowEval5421 x
  · exact rowEval5422 x
  · exact rowEval5423 x
  · exact rowEval5424 x
  · exact rowEval5425 x
  · exact rowEval5426 x
  · exact rowEval5427 x
  · exact rowEval5428 x
  · exact rowEval5429 x
  · exact rowEval5430 x
  · exact rowEval5431 x
  · exact rowEval5432 x
  · exact rowEval5433 x
  · exact rowEval5434 x
  · exact rowEval5435 x
  · exact rowEval5436 x
  · exact rowEval5437 x
  · exact rowEval5438 x
  · exact rowEval5439 x
  · exact rowEval5440 x
  · exact rowEval5441 x
  · exact rowEval5442 x
  · exact rowEval5443 x
  · exact rowEval5444 x
  · exact rowEval5445 x
  · exact rowEval5446 x
  · exact rowEval5447 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block2.form3.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form3 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

end MUB6.Certificate.GramEntries.Block2

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

theorem entryEvalRow1_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 1 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 1).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval1_0_e B hB
  · exact entryEval1_1_e B hB
  · exact (entryEval2_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval3_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval4_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval5_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval6_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_1_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_1 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow1_e_oai
