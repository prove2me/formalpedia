-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:44:23.777204+00:00
-- url     : https://prove2.me/submissions/c2dd3dcc-1765-4023-a976-388b5248081d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E047
import Definitions.Def_OAIQ106E048
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval10_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval13_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval14_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval15_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval16_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval6_0_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13187 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0 = rawRow13187 := by decide +kernel

theorem rowCheck13187 : row13187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13187 := by decide +kernel

theorem rowEval13187 (x : Key → ℝ) : Integer.Sparse.eval row13187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13187, Integer.Sparse.eval_collectBalanced, rawRowCheck13187]

theorem rawRowCheck13188 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0 = rawRow13188 := by decide +kernel

theorem rowCheck13188 : row13188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13188 := by decide +kernel

theorem rowEval13188 (x : Key → ℝ) : Integer.Sparse.eval row13188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13188, Integer.Sparse.eval_collectBalanced, rawRowCheck13188]

theorem rawRowCheck13189 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0 = rawRow13189 := by decide +kernel

theorem rowCheck13189 : row13189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13189 := by decide +kernel

theorem rowEval13189 (x : Key → ℝ) : Integer.Sparse.eval row13189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13189, Integer.Sparse.eval_collectBalanced, rawRowCheck13189]

theorem rawRowCheck13190 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13190 := by decide +kernel

theorem rowCheck13190 : row13190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13190 := by decide +kernel

theorem rowEval13190 (x : Key → ℝ) : Integer.Sparse.eval row13190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13190, Integer.Sparse.eval_collectBalanced, rawRowCheck13190]

theorem rawRowCheck13191 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13191 := by decide +kernel

theorem rowCheck13191 : row13191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13191 := by decide +kernel

theorem rowEval13191 (x : Key → ℝ) : Integer.Sparse.eval row13191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13191, Integer.Sparse.eval_collectBalanced, rawRowCheck13191]

theorem rawRowCheck13192 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13192 := by decide +kernel

theorem rowCheck13192 : row13192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13192 := by decide +kernel

theorem rowEval13192 (x : Key → ℝ) : Integer.Sparse.eval row13192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13192, Integer.Sparse.eval_collectBalanced, rawRowCheck13192]

theorem rawRowCheck13193 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13193 := by decide +kernel

theorem rowCheck13193 : row13193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13193 := by decide +kernel

theorem rowEval13193 (x : Key → ℝ) : Integer.Sparse.eval row13193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13193, Integer.Sparse.eval_collectBalanced, rawRowCheck13193]

theorem rawRowCheck13194 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13194 := by decide +kernel

theorem rowCheck13194 : row13194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13194 := by decide +kernel

theorem rowEval13194 (x : Key → ℝ) : Integer.Sparse.eval row13194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13194, Integer.Sparse.eval_collectBalanced, rawRowCheck13194]

theorem rawRowCheck13195 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13195 := by decide +kernel

theorem rowCheck13195 : row13195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13195 := by decide +kernel

theorem rowEval13195 (x : Key → ℝ) : Integer.Sparse.eval row13195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13195, Integer.Sparse.eval_collectBalanced, rawRowCheck13195]

theorem rawRowCheck13196 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13196 := by decide +kernel

theorem rowCheck13196 : row13196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13196 := by decide +kernel

theorem rowEval13196 (x : Key → ℝ) : Integer.Sparse.eval row13196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13196, Integer.Sparse.eval_collectBalanced, rawRowCheck13196]

theorem rawRowCheck13197 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13197 := by decide +kernel

theorem rowCheck13197 : row13197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13197 := by decide +kernel

theorem rowEval13197 (x : Key → ℝ) : Integer.Sparse.eval row13197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13197, Integer.Sparse.eval_collectBalanced, rawRowCheck13197]

theorem rawRowCheck13198 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13198 := by decide +kernel

theorem rowCheck13198 : row13198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13198 := by decide +kernel

theorem rowEval13198 (x : Key → ℝ) : Integer.Sparse.eval row13198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13198, Integer.Sparse.eval_collectBalanced, rawRowCheck13198]

theorem rawRowCheck13199 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13199 := by decide +kernel

theorem rowCheck13199 : row13199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13199 := by decide +kernel

theorem rowEval13199 (x : Key → ℝ) : Integer.Sparse.eval row13199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13199, Integer.Sparse.eval_collectBalanced, rawRowCheck13199]

theorem rawRowCheck13200 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13200 := by decide +kernel

theorem rowCheck13200 : row13200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13200 := by decide +kernel

theorem rowEval13200 (x : Key → ℝ) : Integer.Sparse.eval row13200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13200, Integer.Sparse.eval_collectBalanced, rawRowCheck13200]

theorem rawRowCheck13201 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13201 := by decide +kernel

theorem rowCheck13201 : row13201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13201 := by decide +kernel

theorem rowEval13201 (x : Key → ℝ) : Integer.Sparse.eval row13201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13201, Integer.Sparse.eval_collectBalanced, rawRowCheck13201]

theorem rawRowCheck13202 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13202 := by decide +kernel

theorem rowCheck13202 : row13202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13202 := by decide +kernel

theorem rowEval13202 (x : Key → ℝ) : Integer.Sparse.eval row13202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13202, Integer.Sparse.eval_collectBalanced, rawRowCheck13202]

theorem rawRowCheck13203 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13203 := by decide +kernel

theorem rowCheck13203 : row13203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13203 := by decide +kernel

theorem rowEval13203 (x : Key → ℝ) : Integer.Sparse.eval row13203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13203, Integer.Sparse.eval_collectBalanced, rawRowCheck13203]

theorem rawRowCheck13204 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13204 := by decide +kernel

theorem rowCheck13204 : row13204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13204 := by decide +kernel

theorem rowEval13204 (x : Key → ℝ) : Integer.Sparse.eval row13204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13204, Integer.Sparse.eval_collectBalanced, rawRowCheck13204]

theorem rawRowCheck13205 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13205 := by decide +kernel

theorem rowCheck13205 : row13205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13205 := by decide +kernel

theorem rowEval13205 (x : Key → ℝ) : Integer.Sparse.eval row13205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13205, Integer.Sparse.eval_collectBalanced, rawRowCheck13205]

theorem rawRowCheck13206 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13206 := by decide +kernel

theorem rowCheck13206 : row13206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13206 := by decide +kernel

theorem rowEval13206 (x : Key → ℝ) : Integer.Sparse.eval row13206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13206, Integer.Sparse.eval_collectBalanced, rawRowCheck13206]

theorem rawRowCheck13207 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13207 := by decide +kernel

theorem rowCheck13207 : row13207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13207 := by decide +kernel

theorem rowEval13207 (x : Key → ℝ) : Integer.Sparse.eval row13207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13207, Integer.Sparse.eval_collectBalanced, rawRowCheck13207]

theorem rawRowCheck13208 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13208 := by decide +kernel

theorem rowCheck13208 : row13208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13208 := by decide +kernel

theorem rowEval13208 (x : Key → ℝ) : Integer.Sparse.eval row13208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13208, Integer.Sparse.eval_collectBalanced, rawRowCheck13208]

theorem rawRowCheck13209 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13209 := by decide +kernel

theorem rowCheck13209 : row13209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13209 := by decide +kernel

theorem rowEval13209 (x : Key → ℝ) : Integer.Sparse.eval row13209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13209, Integer.Sparse.eval_collectBalanced, rawRowCheck13209]

theorem rawRowCheck13210 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13210 := by decide +kernel

theorem rowCheck13210 : row13210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13210 := by decide +kernel

theorem rowEval13210 (x : Key → ℝ) : Integer.Sparse.eval row13210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13210, Integer.Sparse.eval_collectBalanced, rawRowCheck13210]

theorem rawRowCheck13211 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13211 := by decide +kernel

theorem rowCheck13211 : row13211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13211 := by decide +kernel

theorem rowEval13211 (x : Key → ℝ) : Integer.Sparse.eval row13211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13211, Integer.Sparse.eval_collectBalanced, rawRowCheck13211]

theorem rawRowCheck13212 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0 = rawRow13212 := by decide +kernel

theorem rowCheck13212 : row13212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13212 := by decide +kernel

theorem rowEval13212 (x : Key → ℝ) : Integer.Sparse.eval row13212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13212, Integer.Sparse.eval_collectBalanced, rawRowCheck13212]

theorem rawRowCheck13213 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0 = rawRow13213 := by decide +kernel

theorem rowCheck13213 : row13213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13213 := by decide +kernel

theorem rowEval13213 (x : Key → ℝ) : Integer.Sparse.eval row13213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13213, Integer.Sparse.eval_collectBalanced, rawRowCheck13213]

theorem rawRowCheck13214 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0 = rawRow13214 := by decide +kernel

theorem rowCheck13214 : row13214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13214 := by decide +kernel

theorem rowEval13214 (x : Key → ℝ) : Integer.Sparse.eval row13214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13214, Integer.Sparse.eval_collectBalanced, rawRowCheck13214]

theorem rawRowCheck13215 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0 = rawRow13215 := by decide +kernel

theorem rowCheck13215 : row13215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13215 := by decide +kernel

theorem rowEval13215 (x : Key → ℝ) : Integer.Sparse.eval row13215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13215, Integer.Sparse.eval_collectBalanced, rawRowCheck13215]

theorem rawRowCheck13216 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0 = rawRow13216 := by decide +kernel

theorem rowCheck13216 : row13216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13216 := by decide +kernel

theorem rowEval13216 (x : Key → ℝ) : Integer.Sparse.eval row13216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13216, Integer.Sparse.eval_collectBalanced, rawRowCheck13216]

theorem rawRowCheck13217 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0 = rawRow13217 := by decide +kernel

theorem rowCheck13217 : row13217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13217 := by decide +kernel

theorem rowEval13217 (x : Key → ℝ) : Integer.Sparse.eval row13217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13217, Integer.Sparse.eval_collectBalanced, rawRowCheck13217]

theorem rawRowCheck13218 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13218 := by decide +kernel

theorem rowCheck13218 : row13218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13218 := by decide +kernel

theorem rowEval13218 (x : Key → ℝ) : Integer.Sparse.eval row13218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13218, Integer.Sparse.eval_collectBalanced, rawRowCheck13218]

theorem rawRowCheck13219 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13219 := by decide +kernel

theorem rowCheck13219 : row13219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13219 := by decide +kernel

theorem rowEval13219 (x : Key → ℝ) : Integer.Sparse.eval row13219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13219, Integer.Sparse.eval_collectBalanced, rawRowCheck13219]

theorem rawRowCheck13220 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13220 := by decide +kernel

theorem rowCheck13220 : row13220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13220 := by decide +kernel

theorem rowEval13220 (x : Key → ℝ) : Integer.Sparse.eval row13220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13220, Integer.Sparse.eval_collectBalanced, rawRowCheck13220]

theorem rawRowCheck13221 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13221 := by decide +kernel

theorem rowCheck13221 : row13221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13221 := by decide +kernel

theorem rowEval13221 (x : Key → ℝ) : Integer.Sparse.eval row13221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13221, Integer.Sparse.eval_collectBalanced, rawRowCheck13221]

theorem rawRowCheck13222 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13222 := by decide +kernel

theorem rowCheck13222 : row13222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13222 := by decide +kernel

theorem rowEval13222 (x : Key → ℝ) : Integer.Sparse.eval row13222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13222, Integer.Sparse.eval_collectBalanced, rawRowCheck13222]

theorem rawRowCheck13223 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13223 := by decide +kernel

theorem rowCheck13223 : row13223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13223 := by decide +kernel

theorem rowEval13223 (x : Key → ℝ) : Integer.Sparse.eval row13223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13223, Integer.Sparse.eval_collectBalanced, rawRowCheck13223]

theorem rawRowCheck13224 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13224 := by decide +kernel

theorem rowCheck13224 : row13224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13224 := by decide +kernel

theorem rowEval13224 (x : Key → ℝ) : Integer.Sparse.eval row13224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13224, Integer.Sparse.eval_collectBalanced, rawRowCheck13224]

theorem rawRowCheck13245 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13245 := by decide +kernel

theorem rowCheck13245 : row13245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13245 := by decide +kernel

theorem rowEval13245 (x : Key → ℝ) : Integer.Sparse.eval row13245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13245, Integer.Sparse.eval_collectBalanced, rawRowCheck13245]

theorem rawRowCheck13246 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13246 := by decide +kernel

theorem rowCheck13246 : row13246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13246 := by decide +kernel

theorem rowEval13246 (x : Key → ℝ) : Integer.Sparse.eval row13246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13246, Integer.Sparse.eval_collectBalanced, rawRowCheck13246]

theorem rawRowCheck13247 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13247 := by decide +kernel

theorem rowCheck13247 : row13247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13247 := by decide +kernel

theorem rowEval13247 (x : Key → ℝ) : Integer.Sparse.eval row13247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13247, Integer.Sparse.eval_collectBalanced, rawRowCheck13247]

theorem rawRowCheck13248 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13248 := by decide +kernel

theorem rowCheck13248 : row13248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13248 := by decide +kernel

theorem rowEval13248 (x : Key → ℝ) : Integer.Sparse.eval row13248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13248, Integer.Sparse.eval_collectBalanced, rawRowCheck13248]

theorem rawRowCheck13249 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13249 := by decide +kernel

theorem rowCheck13249 : row13249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13249 := by decide +kernel

theorem rowEval13249 (x : Key → ℝ) : Integer.Sparse.eval row13249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13249, Integer.Sparse.eval_collectBalanced, rawRowCheck13249]

theorem rawRowCheck13250 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13250 := by decide +kernel

theorem rowCheck13250 : row13250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13250 := by decide +kernel

theorem rowEval13250 (x : Key → ℝ) : Integer.Sparse.eval row13250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13250, Integer.Sparse.eval_collectBalanced, rawRowCheck13250]

theorem rawRowCheck13251 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13251 := by decide +kernel

theorem rowCheck13251 : row13251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13251 := by decide +kernel

theorem rowEval13251 (x : Key → ℝ) : Integer.Sparse.eval row13251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13251, Integer.Sparse.eval_collectBalanced, rawRowCheck13251]

theorem rawRowCheck13252 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0 = rawRow13252 := by decide +kernel

theorem rowCheck13252 : row13252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13252 := by decide +kernel

theorem rowEval13252 (x : Key → ℝ) : Integer.Sparse.eval row13252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13252, Integer.Sparse.eval_collectBalanced, rawRowCheck13252]

theorem rawRowCheck13253 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0 = rawRow13253 := by decide +kernel

theorem rowCheck13253 : row13253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13253 := by decide +kernel

theorem rowEval13253 (x : Key → ℝ) : Integer.Sparse.eval row13253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13253, Integer.Sparse.eval_collectBalanced, rawRowCheck13253]

theorem rawRowCheck13254 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0 = rawRow13254 := by decide +kernel

theorem rowCheck13254 : row13254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13254 := by decide +kernel

theorem rowEval13254 (x : Key → ℝ) : Integer.Sparse.eval row13254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13254, Integer.Sparse.eval_collectBalanced, rawRowCheck13254]

theorem rawRowCheck13255 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0 = rawRow13255 := by decide +kernel

theorem rowCheck13255 : row13255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13255 := by decide +kernel

theorem rowEval13255 (x : Key → ℝ) : Integer.Sparse.eval row13255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13255, Integer.Sparse.eval_collectBalanced, rawRowCheck13255]

theorem rawRowCheck13256 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0 = rawRow13256 := by decide +kernel

theorem rowCheck13256 : row13256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13256 := by decide +kernel

theorem rowEval13256 (x : Key → ℝ) : Integer.Sparse.eval row13256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13256, Integer.Sparse.eval_collectBalanced, rawRowCheck13256]

theorem rawRowCheck13257 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0 = rawRow13257 := by decide +kernel

theorem rowCheck13257 : row13257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13257 := by decide +kernel

theorem rowEval13257 (x : Key → ℝ) : Integer.Sparse.eval row13257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13257, Integer.Sparse.eval_collectBalanced, rawRowCheck13257]

theorem rawRowCheck13258 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13258 := by decide +kernel

theorem rowCheck13258 : row13258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13258 := by decide +kernel

theorem rowEval13258 (x : Key → ℝ) : Integer.Sparse.eval row13258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13258, Integer.Sparse.eval_collectBalanced, rawRowCheck13258]

theorem rawRowCheck13259 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13259 := by decide +kernel

theorem rowCheck13259 : row13259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13259 := by decide +kernel

theorem rowEval13259 (x : Key → ℝ) : Integer.Sparse.eval row13259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13259, Integer.Sparse.eval_collectBalanced, rawRowCheck13259]

theorem rawRowCheck13260 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13260 := by decide +kernel

theorem rowCheck13260 : row13260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13260 := by decide +kernel

theorem rowEval13260 (x : Key → ℝ) : Integer.Sparse.eval row13260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13260, Integer.Sparse.eval_collectBalanced, rawRowCheck13260]

theorem rawRowCheck13261 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13261 := by decide +kernel

theorem rowCheck13261 : row13261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13261 := by decide +kernel

theorem rowEval13261 (x : Key → ℝ) : Integer.Sparse.eval row13261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13261, Integer.Sparse.eval_collectBalanced, rawRowCheck13261]

theorem rawRowCheck13262 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13262 := by decide +kernel

theorem rowCheck13262 : row13262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13262 := by decide +kernel

theorem rowEval13262 (x : Key → ℝ) : Integer.Sparse.eval row13262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13262, Integer.Sparse.eval_collectBalanced, rawRowCheck13262]

theorem rawRowCheck13263 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13263 := by decide +kernel

theorem rowCheck13263 : row13263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13263 := by decide +kernel

theorem rowEval13263 (x : Key → ℝ) : Integer.Sparse.eval row13263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13263, Integer.Sparse.eval_collectBalanced, rawRowCheck13263]

theorem rawRowCheck13264 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13264 := by decide +kernel

theorem rowCheck13264 : row13264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13264 := by decide +kernel

theorem rowEval13264 (x : Key → ℝ) : Integer.Sparse.eval row13264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13264, Integer.Sparse.eval_collectBalanced, rawRowCheck13264]

theorem rawRowCheck13305 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13305 := by decide +kernel

theorem rowCheck13305 : row13305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13305 := by decide +kernel

theorem rowEval13305 (x : Key → ℝ) : Integer.Sparse.eval row13305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13305, Integer.Sparse.eval_collectBalanced, rawRowCheck13305]

theorem rawRowCheck13306 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13306 := by decide +kernel

theorem rowCheck13306 : row13306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13306 := by decide +kernel

theorem rowEval13306 (x : Key → ℝ) : Integer.Sparse.eval row13306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13306, Integer.Sparse.eval_collectBalanced, rawRowCheck13306]

theorem rawRowCheck13307 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13307 := by decide +kernel

theorem rowCheck13307 : row13307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13307 := by decide +kernel

theorem rowEval13307 (x : Key → ℝ) : Integer.Sparse.eval row13307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13307, Integer.Sparse.eval_collectBalanced, rawRowCheck13307]

theorem rawRowCheck13308 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13308 := by decide +kernel

theorem rowCheck13308 : row13308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13308 := by decide +kernel

theorem rowEval13308 (x : Key → ℝ) : Integer.Sparse.eval row13308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13308, Integer.Sparse.eval_collectBalanced, rawRowCheck13308]

theorem rawRowCheck13309 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13309 := by decide +kernel

theorem rowCheck13309 : row13309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13309 := by decide +kernel

theorem rowEval13309 (x : Key → ℝ) : Integer.Sparse.eval row13309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13309, Integer.Sparse.eval_collectBalanced, rawRowCheck13309]

theorem rawRowCheck13310 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13310 := by decide +kernel

theorem rowCheck13310 : row13310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13310 := by decide +kernel

theorem rowEval13310 (x : Key → ℝ) : Integer.Sparse.eval row13310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13310, Integer.Sparse.eval_collectBalanced, rawRowCheck13310]

theorem rawRowCheck13311 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13311 := by decide +kernel

theorem rowCheck13311 : row13311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13311 := by decide +kernel

theorem rowEval13311 (x : Key → ℝ) : Integer.Sparse.eval row13311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13311, Integer.Sparse.eval_collectBalanced, rawRowCheck13311]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck0_0 : entry0_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form0.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form0.terms k).coefficient) (rows0_0 k)) := by decide +kernel

theorem rowsSound0_0 (k : Fin GramFunctions.Block4.form0.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows0_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form0.terms k).tag (GramFunctions.Block4.form0.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13187 x
  · exact rowEval13188 x
  · exact rowEval13189 x
  · exact rowEval13190 x
  · exact rowEval13191 x
  · exact rowEval13192 x
  · exact rowEval13193 x
  · exact rowEval13194 x
  · exact rowEval13195 x
  · exact rowEval13196 x
  · exact rowEval13197 x
  · exact rowEval13198 x
  · exact rowEval13199 x
  · exact rowEval13200 x
  · exact rowEval13201 x
  · exact rowEval13202 x
  · exact rowEval13203 x
  · exact rowEval13204 x

theorem entryEval0_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry0_0 (GramNormalization.eval B) = GramFunctions.Block4.form0.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck0_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form0 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound0_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck1_0 : entry1_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form1.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form1.terms k).coefficient) (rows1_0 k)) := by decide +kernel

theorem rowsSound1_0 (k : Fin GramFunctions.Block4.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form1.terms k).tag (GramFunctions.Block4.form1.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13205 x
  · exact rowEval13206 x
  · exact rowEval13207 x
  · exact rowEval13208 x
  · exact rowEval13209 x
  · exact rowEval13210 x
  · exact rowEval13211 x
  · exact rowEval13212 x
  · exact rowEval13213 x
  · exact rowEval13214 x
  · exact rowEval13215 x
  · exact rowEval13216 x
  · exact rowEval13217 x
  · exact rowEval13218 x
  · exact rowEval13219 x
  · exact rowEval13220 x
  · exact rowEval13221 x
  · exact rowEval13222 x
  · exact rowEval13223 x
  · exact rowEval13224 x

theorem entryEval1_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry1_0 (GramNormalization.eval B) = GramFunctions.Block4.form1.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck1_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form1 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound1_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14105 : GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow14105 := by decide +kernel

theorem rowCheck14105 : row14105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14105 := by decide +kernel

theorem rowEval14105 (x : Key → ℝ) : Integer.Sparse.eval row14105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14105, Integer.Sparse.eval_collectBalanced, rawRowCheck14105]

theorem rawRowCheck14106 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow14106 := by decide +kernel

theorem rowCheck14106 : row14106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14106 := by decide +kernel

theorem rowEval14106 (x : Key → ℝ) : Integer.Sparse.eval row14106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14106, Integer.Sparse.eval_collectBalanced, rawRowCheck14106]

theorem rawRowCheck14107 : GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow14107 := by decide +kernel

theorem rowCheck14107 : row14107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14107 := by decide +kernel

theorem rowEval14107 (x : Key → ℝ) : Integer.Sparse.eval row14107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14107, Integer.Sparse.eval_collectBalanced, rawRowCheck14107]

theorem rawRowCheck14108 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14108 := by decide +kernel

theorem rowCheck14108 : row14108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14108 := by decide +kernel

theorem rowEval14108 (x : Key → ℝ) : Integer.Sparse.eval row14108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14108, Integer.Sparse.eval_collectBalanced, rawRowCheck14108]

theorem rawRowCheck14109 : GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14109 := by decide +kernel

theorem rowCheck14109 : row14109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14109 := by decide +kernel

theorem rowEval14109 (x : Key → ℝ) : Integer.Sparse.eval row14109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14109, Integer.Sparse.eval_collectBalanced, rawRowCheck14109]

theorem rawRowCheck14110 : GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14110 := by decide +kernel

theorem rowCheck14110 : row14110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14110 := by decide +kernel

theorem rowEval14110 (x : Key → ℝ) : Integer.Sparse.eval row14110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14110, Integer.Sparse.eval_collectBalanced, rawRowCheck14110]

theorem rawRowCheck14111 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow14111 := by decide +kernel

theorem rowCheck14111 : row14111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14111 := by decide +kernel

theorem rowEval14111 (x : Key → ℝ) : Integer.Sparse.eval row14111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14111, Integer.Sparse.eval_collectBalanced, rawRowCheck14111]

theorem rawRowCheck14112 : GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow14112 := by decide +kernel

theorem rowCheck14112 : row14112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14112 := by decide +kernel

theorem rowEval14112 (x : Key → ℝ) : Integer.Sparse.eval row14112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14112, Integer.Sparse.eval_collectBalanced, rawRowCheck14112]

theorem rawRowCheck14113 : GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow14113 := by decide +kernel

theorem rowCheck14113 : row14113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14113 := by decide +kernel

theorem rowEval14113 (x : Key → ℝ) : Integer.Sparse.eval row14113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14113, Integer.Sparse.eval_collectBalanced, rawRowCheck14113]

theorem rawRowCheck14114 : GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow14114 := by decide +kernel

theorem rowCheck14114 : row14114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14114 := by decide +kernel

theorem rowEval14114 (x : Key → ℝ) : Integer.Sparse.eval row14114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14114, Integer.Sparse.eval_collectBalanced, rawRowCheck14114]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14601 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14601 := by decide +kernel

theorem rowCheck14601 : row14601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14601 := by decide +kernel

theorem rowEval14601 (x : Key → ℝ) : Integer.Sparse.eval row14601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14601, Integer.Sparse.eval_collectBalanced, rawRowCheck14601]

theorem rawRowCheck14602 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14602 := by decide +kernel

theorem rowCheck14602 : row14602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14602 := by decide +kernel

theorem rowEval14602 (x : Key → ℝ) : Integer.Sparse.eval row14602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14602, Integer.Sparse.eval_collectBalanced, rawRowCheck14602]

theorem rawRowCheck14603 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14603 := by decide +kernel

theorem rowCheck14603 : row14603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14603 := by decide +kernel

theorem rowEval14603 (x : Key → ℝ) : Integer.Sparse.eval row14603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14603, Integer.Sparse.eval_collectBalanced, rawRowCheck14603]

theorem rawRowCheck14604 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14604 := by decide +kernel

theorem rowCheck14604 : row14604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14604 := by decide +kernel

theorem rowEval14604 (x : Key → ℝ) : Integer.Sparse.eval row14604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14604, Integer.Sparse.eval_collectBalanced, rawRowCheck14604]

theorem rawRowCheck14605 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0 = rawRow14605 := by decide +kernel

theorem rowCheck14605 : row14605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14605 := by decide +kernel

theorem rowEval14605 (x : Key → ℝ) : Integer.Sparse.eval row14605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14605, Integer.Sparse.eval_collectBalanced, rawRowCheck14605]

theorem rawRowCheck14606 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0 = rawRow14606 := by decide +kernel

theorem rowCheck14606 : row14606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14606 := by decide +kernel

theorem rowEval14606 (x : Key → ℝ) : Integer.Sparse.eval row14606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14606, Integer.Sparse.eval_collectBalanced, rawRowCheck14606]

theorem rawRowCheck14607 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0 = rawRow14607 := by decide +kernel

theorem rowCheck14607 : row14607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14607 := by decide +kernel

theorem rowEval14607 (x : Key → ℝ) : Integer.Sparse.eval row14607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14607, Integer.Sparse.eval_collectBalanced, rawRowCheck14607]

theorem rawRowCheck14608 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0 = rawRow14608 := by decide +kernel

theorem rowCheck14608 : row14608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14608 := by decide +kernel

theorem rowEval14608 (x : Key → ℝ) : Integer.Sparse.eval row14608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14608, Integer.Sparse.eval_collectBalanced, rawRowCheck14608]

theorem rawRowCheck14609 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0 = rawRow14609 := by decide +kernel

theorem rowCheck14609 : row14609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14609 := by decide +kernel

theorem rowEval14609 (x : Key → ℝ) : Integer.Sparse.eval row14609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14609, Integer.Sparse.eval_collectBalanced, rawRowCheck14609]

theorem rawRowCheck14610 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0 = rawRow14610 := by decide +kernel

theorem rowCheck14610 : row14610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14610 := by decide +kernel

theorem rowEval14610 (x : Key → ℝ) : Integer.Sparse.eval row14610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14610, Integer.Sparse.eval_collectBalanced, rawRowCheck14610]

theorem rawRowCheck14611 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0 = rawRow14611 := by decide +kernel

theorem rowCheck14611 : row14611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14611 := by decide +kernel

theorem rowEval14611 (x : Key → ℝ) : Integer.Sparse.eval row14611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14611, Integer.Sparse.eval_collectBalanced, rawRowCheck14611]

theorem rawRowCheck14612 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0 = rawRow14612 := by decide +kernel

theorem rowCheck14612 : row14612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14612 := by decide +kernel

theorem rowEval14612 (x : Key → ℝ) : Integer.Sparse.eval row14612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14612, Integer.Sparse.eval_collectBalanced, rawRowCheck14612]

theorem rawRowCheck14613 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0 = rawRow14613 := by decide +kernel

theorem rowCheck14613 : row14613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14613 := by decide +kernel

theorem rowEval14613 (x : Key → ℝ) : Integer.Sparse.eval row14613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14613, Integer.Sparse.eval_collectBalanced, rawRowCheck14613]

theorem rawRowCheck14614 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14614 := by decide +kernel

theorem rowCheck14614 : row14614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14614 := by decide +kernel

theorem rowEval14614 (x : Key → ℝ) : Integer.Sparse.eval row14614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14614, Integer.Sparse.eval_collectBalanced, rawRowCheck14614]

theorem rawRowCheck14615 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14615 := by decide +kernel

theorem rowCheck14615 : row14615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14615 := by decide +kernel

theorem rowEval14615 (x : Key → ℝ) : Integer.Sparse.eval row14615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14615, Integer.Sparse.eval_collectBalanced, rawRowCheck14615]

theorem rawRowCheck14616 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14616 := by decide +kernel

theorem rowCheck14616 : row14616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14616 := by decide +kernel

theorem rowEval14616 (x : Key → ℝ) : Integer.Sparse.eval row14616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14616, Integer.Sparse.eval_collectBalanced, rawRowCheck14616]

theorem rawRowCheck14617 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow14617 := by decide +kernel

theorem rowCheck14617 : row14617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14617 := by decide +kernel

theorem rowEval14617 (x : Key → ℝ) : Integer.Sparse.eval row14617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14617, Integer.Sparse.eval_collectBalanced, rawRowCheck14617]

theorem rawRowCheck14618 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0 = rawRow14618 := by decide +kernel

theorem rowCheck14618 : row14618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14618 := by decide +kernel

theorem rowEval14618 (x : Key → ℝ) : Integer.Sparse.eval row14618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14618, Integer.Sparse.eval_collectBalanced, rawRowCheck14618]

theorem rawRowCheck14619 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0 = rawRow14619 := by decide +kernel

theorem rowCheck14619 : row14619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14619 := by decide +kernel

theorem rowEval14619 (x : Key → ℝ) : Integer.Sparse.eval row14619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14619, Integer.Sparse.eval_collectBalanced, rawRowCheck14619]

theorem rawRowCheck14620 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0 = rawRow14620 := by decide +kernel

theorem rowCheck14620 : row14620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14620 := by decide +kernel

theorem rowEval14620 (x : Key → ℝ) : Integer.Sparse.eval row14620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck14620, Integer.Sparse.eval_collectBalanced, rawRowCheck14620]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14841 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14841 := by decide +kernel

theorem rowCheck14841 : row14841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14841 := by decide +kernel

theorem rowEval14841 (x : Key → ℝ) : Integer.Sparse.eval row14841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14841, Integer.Sparse.eval_collectBalanced, rawRowCheck14841]

theorem rawRowCheck14842 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14842 := by decide +kernel

theorem rowCheck14842 : row14842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14842 := by decide +kernel

theorem rowEval14842 (x : Key → ℝ) : Integer.Sparse.eval row14842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14842, Integer.Sparse.eval_collectBalanced, rawRowCheck14842]

theorem rawRowCheck14843 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14843 := by decide +kernel

theorem rowCheck14843 : row14843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14843 := by decide +kernel

theorem rowEval14843 (x : Key → ℝ) : Integer.Sparse.eval row14843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14843, Integer.Sparse.eval_collectBalanced, rawRowCheck14843]

theorem rawRowCheck14844 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14844 := by decide +kernel

theorem rowCheck14844 : row14844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14844 := by decide +kernel

theorem rowEval14844 (x : Key → ℝ) : Integer.Sparse.eval row14844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14844, Integer.Sparse.eval_collectBalanced, rawRowCheck14844]

theorem rawRowCheck14845 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14845 := by decide +kernel

theorem rowCheck14845 : row14845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14845 := by decide +kernel

theorem rowEval14845 (x : Key → ℝ) : Integer.Sparse.eval row14845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14845, Integer.Sparse.eval_collectBalanced, rawRowCheck14845]

theorem rawRowCheck14846 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14846 := by decide +kernel

theorem rowCheck14846 : row14846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14846 := by decide +kernel

theorem rowEval14846 (x : Key → ℝ) : Integer.Sparse.eval row14846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14846, Integer.Sparse.eval_collectBalanced, rawRowCheck14846]

theorem rawRowCheck14847 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0 = rawRow14847 := by decide +kernel

theorem rowCheck14847 : row14847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14847 := by decide +kernel

theorem rowEval14847 (x : Key → ℝ) : Integer.Sparse.eval row14847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14847, Integer.Sparse.eval_collectBalanced, rawRowCheck14847]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block4.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form11.terms k).tag (GramFunctions.Block4.form11.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14601 x
  · exact rowEval14602 x
  · exact rowEval14603 x
  · exact rowEval14604 x
  · exact rowEval14605 x
  · exact rowEval14606 x
  · exact rowEval14607 x
  · exact rowEval14608 x
  · exact rowEval14609 x
  · exact rowEval14610 x
  · exact rowEval14611 x
  · exact rowEval14612 x
  · exact rowEval14613 x
  · exact rowEval14614 x
  · exact rowEval14615 x
  · exact rowEval14616 x
  · exact rowEval14617 x
  · exact rowEval14618 x
  · exact rowEval14619 x
  · exact rowEval14620 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block4.form11.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form11 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck14848 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0 = rawRow14848 := by decide +kernel

theorem rowCheck14848 : row14848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14848 := by decide +kernel

theorem rowEval14848 (x : Key → ℝ) : Integer.Sparse.eval row14848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14848, Integer.Sparse.eval_collectBalanced, rawRowCheck14848]

theorem rawRowCheck14849 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0 = rawRow14849 := by decide +kernel

theorem rowCheck14849 : row14849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14849 := by decide +kernel

theorem rowEval14849 (x : Key → ℝ) : Integer.Sparse.eval row14849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14849, Integer.Sparse.eval_collectBalanced, rawRowCheck14849]

theorem rawRowCheck14850 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow14850 := by decide +kernel

theorem rowCheck14850 : row14850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14850 := by decide +kernel

theorem rowEval14850 (x : Key → ℝ) : Integer.Sparse.eval row14850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck14850, Integer.Sparse.eval_collectBalanced, rawRowCheck14850]

theorem rawRowCheck14851 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow14851 := by decide +kernel

theorem rowCheck14851 : row14851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14851 := by decide +kernel

theorem rowEval14851 (x : Key → ℝ) : Integer.Sparse.eval row14851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14851, Integer.Sparse.eval_collectBalanced, rawRowCheck14851]

theorem rawRowCheck14852 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow14852 := by decide +kernel

theorem rowCheck14852 : row14852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14852 := by decide +kernel

theorem rowEval14852 (x : Key → ℝ) : Integer.Sparse.eval row14852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck14852, Integer.Sparse.eval_collectBalanced, rawRowCheck14852]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block4.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form12.terms k).tag (GramFunctions.Block4.form12.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14841 x
  · exact rowEval14842 x
  · exact rowEval14843 x
  · exact rowEval14844 x
  · exact rowEval14845 x
  · exact rowEval14846 x
  · exact rowEval14847 x
  · exact rowEval14848 x
  · exact rowEval14849 x
  · exact rowEval13190 x
  · exact rowEval13191 x
  · exact rowEval13192 x
  · exact rowEval13193 x
  · exact rowEval13194 x
  · exact rowEval13195 x
  · exact rowEval14850 x
  · exact rowEval14851 x
  · exact rowEval14852 x
  · exact rowEval13196 x
  · exact rowEval13197 x
  · exact rowEval13198 x
  · exact rowEval13199 x
  · exact rowEval13200 x
  · exact rowEval13201 x
  · exact rowEval13202 x
  · exact rowEval13203 x
  · exact rowEval13204 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block4.form12.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form12 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13845 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13845 := by decide +kernel

theorem rowCheck13845 : row13845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13845 := by decide +kernel

theorem rowEval13845 (x : Key → ℝ) : Integer.Sparse.eval row13845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13845, Integer.Sparse.eval_collectBalanced, rawRowCheck13845]

theorem rawRowCheck13846 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13846 := by decide +kernel

theorem rowCheck13846 : row13846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13846 := by decide +kernel

theorem rowEval13846 (x : Key → ℝ) : Integer.Sparse.eval row13846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13846, Integer.Sparse.eval_collectBalanced, rawRowCheck13846]

theorem rawRowCheck13847 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13847 := by decide +kernel

theorem rowCheck13847 : row13847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13847 := by decide +kernel

theorem rowEval13847 (x : Key → ℝ) : Integer.Sparse.eval row13847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13847, Integer.Sparse.eval_collectBalanced, rawRowCheck13847]

theorem rawRowCheck13848 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13848 := by decide +kernel

theorem rowCheck13848 : row13848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13848 := by decide +kernel

theorem rowEval13848 (x : Key → ℝ) : Integer.Sparse.eval row13848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13848, Integer.Sparse.eval_collectBalanced, rawRowCheck13848]

theorem rawRowCheck13849 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13849 := by decide +kernel

theorem rowCheck13849 : row13849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13849 := by decide +kernel

theorem rowEval13849 (x : Key → ℝ) : Integer.Sparse.eval row13849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13849, Integer.Sparse.eval_collectBalanced, rawRowCheck13849]

theorem rawRowCheck13850 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13850 := by decide +kernel

theorem rowCheck13850 : row13850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13850 := by decide +kernel

theorem rowEval13850 (x : Key → ℝ) : Integer.Sparse.eval row13850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13850, Integer.Sparse.eval_collectBalanced, rawRowCheck13850]

theorem rawRowCheck13851 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow13851 := by decide +kernel

theorem rowCheck13851 : row13851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13851 := by decide +kernel

theorem rowEval13851 (x : Key → ℝ) : Integer.Sparse.eval row13851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13851, Integer.Sparse.eval_collectBalanced, rawRowCheck13851]

theorem rawRowCheck13852 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow13852 := by decide +kernel

theorem rowCheck13852 : row13852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13852 := by decide +kernel

theorem rowEval13852 (x : Key → ℝ) : Integer.Sparse.eval row13852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13852, Integer.Sparse.eval_collectBalanced, rawRowCheck13852]

theorem rawRowCheck13853 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow13853 := by decide +kernel

theorem rowCheck13853 : row13853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13853 := by decide +kernel

theorem rowEval13853 (x : Key → ℝ) : Integer.Sparse.eval row13853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13853, Integer.Sparse.eval_collectBalanced, rawRowCheck13853]

theorem rawRowCheck13854 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow13854 := by decide +kernel

theorem rowCheck13854 : row13854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13854 := by decide +kernel

theorem rowEval13854 (x : Key → ℝ) : Integer.Sparse.eval row13854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13854, Integer.Sparse.eval_collectBalanced, rawRowCheck13854]

theorem rawRowCheck13925 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13925 := by decide +kernel

theorem rowCheck13925 : row13925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13925 := by decide +kernel

theorem rowEval13925 (x : Key → ℝ) : Integer.Sparse.eval row13925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13925, Integer.Sparse.eval_collectBalanced, rawRowCheck13925]

theorem rawRowCheck13926 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13926 := by decide +kernel

theorem rowCheck13926 : row13926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13926 := by decide +kernel

theorem rowEval13926 (x : Key → ℝ) : Integer.Sparse.eval row13926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13926, Integer.Sparse.eval_collectBalanced, rawRowCheck13926]

theorem rawRowCheck13927 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13927 := by decide +kernel

theorem rowCheck13927 : row13927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13927 := by decide +kernel

theorem rowEval13927 (x : Key → ℝ) : Integer.Sparse.eval row13927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13927, Integer.Sparse.eval_collectBalanced, rawRowCheck13927]

theorem rawRowCheck13928 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13928 := by decide +kernel

theorem rowCheck13928 : row13928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13928 := by decide +kernel

theorem rowEval13928 (x : Key → ℝ) : Integer.Sparse.eval row13928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13928, Integer.Sparse.eval_collectBalanced, rawRowCheck13928]

theorem rawRowCheck13929 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13929 := by decide +kernel

theorem rowCheck13929 : row13929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13929 := by decide +kernel

theorem rowEval13929 (x : Key → ℝ) : Integer.Sparse.eval row13929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13929, Integer.Sparse.eval_collectBalanced, rawRowCheck13929]

theorem rawRowCheck13930 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13930 := by decide +kernel

theorem rowCheck13930 : row13930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13930 := by decide +kernel

theorem rowEval13930 (x : Key → ℝ) : Integer.Sparse.eval row13930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13930, Integer.Sparse.eval_collectBalanced, rawRowCheck13930]

theorem rawRowCheck13931 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13931 := by decide +kernel

theorem rowCheck13931 : row13931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13931 := by decide +kernel

theorem rowEval13931 (x : Key → ℝ) : Integer.Sparse.eval row13931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13931, Integer.Sparse.eval_collectBalanced, rawRowCheck13931]

theorem rawRowCheck13932 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13932 := by decide +kernel

theorem rowCheck13932 : row13932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13932 := by decide +kernel

theorem rowEval13932 (x : Key → ℝ) : Integer.Sparse.eval row13932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13932, Integer.Sparse.eval_collectBalanced, rawRowCheck13932]

theorem rawRowCheck13933 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13933 := by decide +kernel

theorem rowCheck13933 : row13933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13933 := by decide +kernel

theorem rowEval13933 (x : Key → ℝ) : Integer.Sparse.eval row13933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13933, Integer.Sparse.eval_collectBalanced, rawRowCheck13933]

theorem rawRowCheck13934 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13934 := by decide +kernel

theorem rowCheck13934 : row13934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13934 := by decide +kernel

theorem rowEval13934 (x : Key → ℝ) : Integer.Sparse.eval row13934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13934, Integer.Sparse.eval_collectBalanced, rawRowCheck13934]

theorem rawRowCheck13935 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13935 := by decide +kernel

theorem rowCheck13935 : row13935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13935 := by decide +kernel

theorem rowEval13935 (x : Key → ℝ) : Integer.Sparse.eval row13935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13935, Integer.Sparse.eval_collectBalanced, rawRowCheck13935]

theorem rawRowCheck13936 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13936 := by decide +kernel

theorem rowCheck13936 : row13936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13936 := by decide +kernel

theorem rowEval13936 (x : Key → ℝ) : Integer.Sparse.eval row13936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13936, Integer.Sparse.eval_collectBalanced, rawRowCheck13936]

theorem rawRowCheck13937 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13937 := by decide +kernel

theorem rowCheck13937 : row13937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13937 := by decide +kernel

theorem rowEval13937 (x : Key → ℝ) : Integer.Sparse.eval row13937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13937, Integer.Sparse.eval_collectBalanced, rawRowCheck13937]

theorem rawRowCheck13938 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13938 := by decide +kernel

theorem rowCheck13938 : row13938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13938 := by decide +kernel

theorem rowEval13938 (x : Key → ℝ) : Integer.Sparse.eval row13938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13938, Integer.Sparse.eval_collectBalanced, rawRowCheck13938]

theorem rawRowCheck13939 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13939 := by decide +kernel

theorem rowCheck13939 : row13939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13939 := by decide +kernel

theorem rowEval13939 (x : Key → ℝ) : Integer.Sparse.eval row13939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13939, Integer.Sparse.eval_collectBalanced, rawRowCheck13939]

theorem rawRowCheck13940 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13940 := by decide +kernel

theorem rowCheck13940 : row13940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13940 := by decide +kernel

theorem rowEval13940 (x : Key → ℝ) : Integer.Sparse.eval row13940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13940, Integer.Sparse.eval_collectBalanced, rawRowCheck13940]

theorem rawRowCheck13941 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13941 := by decide +kernel

theorem rowCheck13941 : row13941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13941 := by decide +kernel

theorem rowEval13941 (x : Key → ℝ) : Integer.Sparse.eval row13941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13941, Integer.Sparse.eval_collectBalanced, rawRowCheck13941]

theorem rawRowCheck13942 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13942 := by decide +kernel

theorem rowCheck13942 : row13942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13942 := by decide +kernel

theorem rowEval13942 (x : Key → ℝ) : Integer.Sparse.eval row13942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13942, Integer.Sparse.eval_collectBalanced, rawRowCheck13942]

theorem rawRowCheck13943 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13943 := by decide +kernel

theorem rowCheck13943 : row13943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13943 := by decide +kernel

theorem rowEval13943 (x : Key → ℝ) : Integer.Sparse.eval row13943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13943, Integer.Sparse.eval_collectBalanced, rawRowCheck13943]

theorem rawRowCheck13944 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13944 := by decide +kernel

theorem rowCheck13944 : row13944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13944 := by decide +kernel

theorem rowEval13944 (x : Key → ℝ) : Integer.Sparse.eval row13944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13944, Integer.Sparse.eval_collectBalanced, rawRowCheck13944]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck16707 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form0 = rawRow16707 := by decide +kernel

theorem rowCheck16707 : row16707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16707 := by decide +kernel

theorem rowEval16707 (x : Key → ℝ) : Integer.Sparse.eval row16707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16707, Integer.Sparse.eval_collectBalanced, rawRowCheck16707]

theorem rawRowCheck16708 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form0 = rawRow16708 := by decide +kernel

theorem rowCheck16708 : row16708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16708 := by decide +kernel

theorem rowEval16708 (x : Key → ℝ) : Integer.Sparse.eval row16708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16708, Integer.Sparse.eval_collectBalanced, rawRowCheck16708]

theorem rawRowCheck16709 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form0 = rawRow16709 := by decide +kernel

theorem rowCheck16709 : row16709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16709 := by decide +kernel

theorem rowEval16709 (x : Key → ℝ) : Integer.Sparse.eval row16709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16709, Integer.Sparse.eval_collectBalanced, rawRowCheck16709]

theorem rawRowCheck16710 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form0 = rawRow16710 := by decide +kernel

theorem rowCheck16710 : row16710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16710 := by decide +kernel

theorem rowEval16710 (x : Key → ℝ) : Integer.Sparse.eval row16710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16710, Integer.Sparse.eval_collectBalanced, rawRowCheck16710]

theorem rawRowCheck16711 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form0 = rawRow16711 := by decide +kernel

theorem rowCheck16711 : row16711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16711 := by decide +kernel

theorem rowEval16711 (x : Key → ℝ) : Integer.Sparse.eval row16711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16711, Integer.Sparse.eval_collectBalanced, rawRowCheck16711]

theorem rawRowCheck16712 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form0 = rawRow16712 := by decide +kernel

theorem rowCheck16712 : row16712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16712 := by decide +kernel

theorem rowEval16712 (x : Key → ℝ) : Integer.Sparse.eval row16712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16712, Integer.Sparse.eval_collectBalanced, rawRowCheck16712]

theorem rawRowCheck16713 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form0 = rawRow16713 := by decide +kernel

theorem rowCheck16713 : row16713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16713 := by decide +kernel

theorem rowEval16713 (x : Key → ℝ) : Integer.Sparse.eval row16713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16713, Integer.Sparse.eval_collectBalanced, rawRowCheck16713]

theorem rawRowCheck16714 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form0 = rawRow16714 := by decide +kernel

theorem rowCheck16714 : row16714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16714 := by decide +kernel

theorem rowEval16714 (x : Key → ℝ) : Integer.Sparse.eval row16714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16714, Integer.Sparse.eval_collectBalanced, rawRowCheck16714]

theorem rawRowCheck16715 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form0 = rawRow16715 := by decide +kernel

theorem rowCheck16715 : row16715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16715 := by decide +kernel

theorem rowEval16715 (x : Key → ℝ) : Integer.Sparse.eval row16715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16715, Integer.Sparse.eval_collectBalanced, rawRowCheck16715]

theorem rawRowCheck16716 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form0 = rawRow16716 := by decide +kernel

theorem rowCheck16716 : row16716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16716 := by decide +kernel

theorem rowEval16716 (x : Key → ℝ) : Integer.Sparse.eval row16716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16716, Integer.Sparse.eval_collectBalanced, rawRowCheck16716]

theorem rawRowCheck16717 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form0 = rawRow16717 := by decide +kernel

theorem rowCheck16717 : row16717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16717 := by decide +kernel

theorem rowEval16717 (x : Key → ℝ) : Integer.Sparse.eval row16717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16717, Integer.Sparse.eval_collectBalanced, rawRowCheck16717]

theorem rawRowCheck16718 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form0 = rawRow16718 := by decide +kernel

theorem rowCheck16718 : row16718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16718 := by decide +kernel

theorem rowEval16718 (x : Key → ℝ) : Integer.Sparse.eval row16718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16718, Integer.Sparse.eval_collectBalanced, rawRowCheck16718]

theorem rawRowCheck16719 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form0 = rawRow16719 := by decide +kernel

theorem rowCheck16719 : row16719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16719 := by decide +kernel

theorem rowEval16719 (x : Key → ℝ) : Integer.Sparse.eval row16719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16719, Integer.Sparse.eval_collectBalanced, rawRowCheck16719]

theorem rawRowCheck16720 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form0 = rawRow16720 := by decide +kernel

theorem rowCheck16720 : row16720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16720 := by decide +kernel

theorem rowEval16720 (x : Key → ℝ) : Integer.Sparse.eval row16720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16720, Integer.Sparse.eval_collectBalanced, rawRowCheck16720]

theorem rawRowCheck16721 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form0 = rawRow16721 := by decide +kernel

theorem rowCheck16721 : row16721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16721 := by decide +kernel

theorem rowEval16721 (x : Key → ℝ) : Integer.Sparse.eval row16721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16721, Integer.Sparse.eval_collectBalanced, rawRowCheck16721]

theorem rawRowCheck16722 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form0 = rawRow16722 := by decide +kernel

theorem rowCheck16722 : row16722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16722 := by decide +kernel

theorem rowEval16722 (x : Key → ℝ) : Integer.Sparse.eval row16722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16722, Integer.Sparse.eval_collectBalanced, rawRowCheck16722]

theorem rawRowCheck16723 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form0 = rawRow16723 := by decide +kernel

theorem rowCheck16723 : row16723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16723 := by decide +kernel

theorem rowEval16723 (x : Key → ℝ) : Integer.Sparse.eval row16723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16723, Integer.Sparse.eval_collectBalanced, rawRowCheck16723]

theorem rawRowCheck16724 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form0 = rawRow16724 := by decide +kernel

theorem rowCheck16724 : row16724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16724 := by decide +kernel

theorem rowEval16724 (x : Key → ℝ) : Integer.Sparse.eval row16724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16724, Integer.Sparse.eval_collectBalanced, rawRowCheck16724]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17031 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form0 = rawRow17031 := by decide +kernel

theorem rowCheck17031 : row17031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17031 := by decide +kernel

theorem rowEval17031 (x : Key → ℝ) : Integer.Sparse.eval row17031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17031, Integer.Sparse.eval_collectBalanced, rawRowCheck17031]

theorem rawRowCheck17032 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form0 = rawRow17032 := by decide +kernel

theorem rowCheck17032 : row17032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17032 := by decide +kernel

theorem rowEval17032 (x : Key → ℝ) : Integer.Sparse.eval row17032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17032, Integer.Sparse.eval_collectBalanced, rawRowCheck17032]

theorem rawRowCheck17033 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form0 = rawRow17033 := by decide +kernel

theorem rowCheck17033 : row17033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17033 := by decide +kernel

theorem rowEval17033 (x : Key → ℝ) : Integer.Sparse.eval row17033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17033, Integer.Sparse.eval_collectBalanced, rawRowCheck17033]

theorem rawRowCheck17034 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form0 = rawRow17034 := by decide +kernel

theorem rowCheck17034 : row17034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17034 := by decide +kernel

theorem rowEval17034 (x : Key → ℝ) : Integer.Sparse.eval row17034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17034, Integer.Sparse.eval_collectBalanced, rawRowCheck17034]

theorem rawRowCheck17035 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form0 = rawRow17035 := by decide +kernel

theorem rowCheck17035 : row17035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17035 := by decide +kernel

theorem rowEval17035 (x : Key → ℝ) : Integer.Sparse.eval row17035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17035, Integer.Sparse.eval_collectBalanced, rawRowCheck17035]

theorem rawRowCheck17036 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form0 = rawRow17036 := by decide +kernel

theorem rowCheck17036 : row17036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17036 := by decide +kernel

theorem rowEval17036 (x : Key → ℝ) : Integer.Sparse.eval row17036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17036, Integer.Sparse.eval_collectBalanced, rawRowCheck17036]

theorem rawRowCheck17037 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form0 = rawRow17037 := by decide +kernel

theorem rowCheck17037 : row17037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17037 := by decide +kernel

theorem rowEval17037 (x : Key → ℝ) : Integer.Sparse.eval row17037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17037, Integer.Sparse.eval_collectBalanced, rawRowCheck17037]

theorem rawRowCheck17038 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form0 = rawRow17038 := by decide +kernel

theorem rowCheck17038 : row17038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17038 := by decide +kernel

theorem rowEval17038 (x : Key → ℝ) : Integer.Sparse.eval row17038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17038, Integer.Sparse.eval_collectBalanced, rawRowCheck17038]

theorem rawRowCheck17039 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form0 = rawRow17039 := by decide +kernel

theorem rowCheck17039 : row17039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17039 := by decide +kernel

theorem rowEval17039 (x : Key → ℝ) : Integer.Sparse.eval row17039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17039, Integer.Sparse.eval_collectBalanced, rawRowCheck17039]

theorem rawRowCheck17040 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17040 := by decide +kernel

theorem rowCheck17040 : row17040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17040 := by decide +kernel

theorem rowEval17040 (x : Key → ℝ) : Integer.Sparse.eval row17040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17040, Integer.Sparse.eval_collectBalanced, rawRowCheck17040]

theorem rawRowCheck17041 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17041 := by decide +kernel

theorem rowCheck17041 : row17041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17041 := by decide +kernel

theorem rowEval17041 (x : Key → ℝ) : Integer.Sparse.eval row17041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17041, Integer.Sparse.eval_collectBalanced, rawRowCheck17041]

theorem rawRowCheck17042 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form0 = rawRow17042 := by decide +kernel

theorem rowCheck17042 : row17042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17042 := by decide +kernel

theorem rowEval17042 (x : Key → ℝ) : Integer.Sparse.eval row17042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17042, Integer.Sparse.eval_collectBalanced, rawRowCheck17042]

theorem rawRowCheck17043 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form0 = rawRow17043 := by decide +kernel

theorem rowCheck17043 : row17043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17043 := by decide +kernel

theorem rowEval17043 (x : Key → ℝ) : Integer.Sparse.eval row17043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17043, Integer.Sparse.eval_collectBalanced, rawRowCheck17043]

theorem rawRowCheck17044 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form0 = rawRow17044 := by decide +kernel

theorem rowCheck17044 : row17044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17044 := by decide +kernel

theorem rowEval17044 (x : Key → ℝ) : Integer.Sparse.eval row17044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17044, Integer.Sparse.eval_collectBalanced, rawRowCheck17044]

theorem rawRowCheck17045 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form0 = rawRow17045 := by decide +kernel

theorem rowCheck17045 : row17045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17045 := by decide +kernel

theorem rowEval17045 (x : Key → ℝ) : Integer.Sparse.eval row17045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17045, Integer.Sparse.eval_collectBalanced, rawRowCheck17045]

theorem rawRowCheck17046 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form0 = rawRow17046 := by decide +kernel

theorem rowCheck17046 : row17046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17046 := by decide +kernel

theorem rowEval17046 (x : Key → ℝ) : Integer.Sparse.eval row17046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17046, Integer.Sparse.eval_collectBalanced, rawRowCheck17046]

theorem rawRowCheck17047 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17047 := by decide +kernel

theorem rowCheck17047 : row17047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17047 := by decide +kernel

theorem rowEval17047 (x : Key → ℝ) : Integer.Sparse.eval row17047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17047, Integer.Sparse.eval_collectBalanced, rawRowCheck17047]

theorem rawRowCheck17048 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17048 := by decide +kernel

theorem rowCheck17048 : row17048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17048 := by decide +kernel

theorem rowEval17048 (x : Key → ℝ) : Integer.Sparse.eval row17048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17048, Integer.Sparse.eval_collectBalanced, rawRowCheck17048]

theorem rawRowCheck17049 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow17049 := by decide +kernel

theorem rowCheck17049 : row17049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17049 := by decide +kernel

theorem rowEval17049 (x : Key → ℝ) : Integer.Sparse.eval row17049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17049, Integer.Sparse.eval_collectBalanced, rawRowCheck17049]

theorem rawRowCheck17050 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow17050 := by decide +kernel

theorem rowCheck17050 : row17050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17050 := by decide +kernel

theorem rowEval17050 (x : Key → ℝ) : Integer.Sparse.eval row17050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17050, Integer.Sparse.eval_collectBalanced, rawRowCheck17050]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck17_0 : entry17_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form17.terms k).coefficient) (rows17_0 k)) := by decide +kernel

theorem rowsSound17_0 (k : Fin GramFunctions.Block4.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form17.terms k).tag (GramFunctions.Block4.form17.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval16707 x
  · exact rowEval16708 x
  · exact rowEval16709 x
  · exact rowEval16710 x
  · exact rowEval16711 x
  · exact rowEval16712 x
  · exact rowEval16713 x
  · exact rowEval16714 x
  · exact rowEval16715 x
  · exact rowEval16716 x
  · exact rowEval16717 x
  · exact rowEval16718 x
  · exact rowEval16719 x
  · exact rowEval16720 x
  · exact rowEval16721 x
  · exact rowEval16722 x
  · exact rowEval16723 x
  · exact rowEval16724 x

theorem entryEval17_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_0 (GramNormalization.eval B) = GramFunctions.Block4.form17.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck17_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form17 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17411 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow17411 := by decide +kernel

theorem rowCheck17411 : row17411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17411 := by decide +kernel

theorem rowEval17411 (x : Key → ℝ) : Integer.Sparse.eval row17411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17411, Integer.Sparse.eval_collectBalanced, rawRowCheck17411]

theorem rawRowCheck17412 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow17412 := by decide +kernel

theorem rowCheck17412 : row17412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17412 := by decide +kernel

theorem rowEval17412 (x : Key → ℝ) : Integer.Sparse.eval row17412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17412, Integer.Sparse.eval_collectBalanced, rawRowCheck17412]

theorem rawRowCheck17413 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow17413 := by decide +kernel

theorem rowCheck17413 : row17413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17413 := by decide +kernel

theorem rowEval17413 (x : Key → ℝ) : Integer.Sparse.eval row17413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17413, Integer.Sparse.eval_collectBalanced, rawRowCheck17413]

theorem rawRowCheck17414 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17414 := by decide +kernel

theorem rowCheck17414 : row17414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17414 := by decide +kernel

theorem rowEval17414 (x : Key → ℝ) : Integer.Sparse.eval row17414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17414, Integer.Sparse.eval_collectBalanced, rawRowCheck17414]

theorem rawRowCheck17415 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17415 := by decide +kernel

theorem rowCheck17415 : row17415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17415 := by decide +kernel

theorem rowEval17415 (x : Key → ℝ) : Integer.Sparse.eval row17415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17415, Integer.Sparse.eval_collectBalanced, rawRowCheck17415]

theorem rawRowCheck17416 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17416 := by decide +kernel

theorem rowCheck17416 : row17416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17416 := by decide +kernel

theorem rowEval17416 (x : Key → ℝ) : Integer.Sparse.eval row17416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17416, Integer.Sparse.eval_collectBalanced, rawRowCheck17416]

theorem rawRowCheck17417 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17417 := by decide +kernel

theorem rowCheck17417 : row17417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17417 := by decide +kernel

theorem rowEval17417 (x : Key → ℝ) : Integer.Sparse.eval row17417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17417, Integer.Sparse.eval_collectBalanced, rawRowCheck17417]

theorem rawRowCheck17418 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17418 := by decide +kernel

theorem rowCheck17418 : row17418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17418 := by decide +kernel

theorem rowEval17418 (x : Key → ℝ) : Integer.Sparse.eval row17418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17418, Integer.Sparse.eval_collectBalanced, rawRowCheck17418]

theorem rawRowCheck17419 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17419 := by decide +kernel

theorem rowCheck17419 : row17419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17419 := by decide +kernel

theorem rowEval17419 (x : Key → ℝ) : Integer.Sparse.eval row17419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17419, Integer.Sparse.eval_collectBalanced, rawRowCheck17419]

theorem rawRowCheck17420 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow17420 := by decide +kernel

theorem rowCheck17420 : row17420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17420 := by decide +kernel

theorem rowEval17420 (x : Key → ℝ) : Integer.Sparse.eval row17420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17420, Integer.Sparse.eval_collectBalanced, rawRowCheck17420]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck18_0 : entry18_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_0 k)) := by decide +kernel

theorem rowsSound18_0 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17031 x
  · exact rowEval17032 x
  · exact rowEval17033 x
  · exact rowEval17034 x
  · exact rowEval17035 x
  · exact rowEval17036 x
  · exact rowEval17037 x
  · exact rowEval17038 x
  · exact rowEval17039 x
  · exact rowEval17040 x
  · exact rowEval17041 x
  · exact rowEval17042 x
  · exact rowEval17043 x
  · exact rowEval17044 x
  · exact rowEval17045 x
  · exact rowEval17046 x
  · exact rowEval17047 x
  · exact rowEval17048 x
  · exact rowEval17049 x
  · exact rowEval17050 x

theorem entryEval18_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_0 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck18_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17611 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17611 := by decide +kernel

theorem rowCheck17611 : row17611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17611 := by decide +kernel

theorem rowEval17611 (x : Key → ℝ) : Integer.Sparse.eval row17611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17611, Integer.Sparse.eval_collectBalanced, rawRowCheck17611]

theorem rawRowCheck17612 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17612 := by decide +kernel

theorem rowCheck17612 : row17612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17612 := by decide +kernel

theorem rowEval17612 (x : Key → ℝ) : Integer.Sparse.eval row17612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17612, Integer.Sparse.eval_collectBalanced, rawRowCheck17612]

theorem rawRowCheck17613 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17613 := by decide +kernel

theorem rowCheck17613 : row17613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17613 := by decide +kernel

theorem rowEval17613 (x : Key → ℝ) : Integer.Sparse.eval row17613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17613, Integer.Sparse.eval_collectBalanced, rawRowCheck17613]

theorem rawRowCheck17614 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17614 := by decide +kernel

theorem rowCheck17614 : row17614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17614 := by decide +kernel

theorem rowEval17614 (x : Key → ℝ) : Integer.Sparse.eval row17614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17614, Integer.Sparse.eval_collectBalanced, rawRowCheck17614]

theorem rawRowCheck17615 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17615 := by decide +kernel

theorem rowCheck17615 : row17615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17615 := by decide +kernel

theorem rowEval17615 (x : Key → ℝ) : Integer.Sparse.eval row17615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17615, Integer.Sparse.eval_collectBalanced, rawRowCheck17615]

theorem rawRowCheck17616 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17616 := by decide +kernel

theorem rowCheck17616 : row17616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17616 := by decide +kernel

theorem rowEval17616 (x : Key → ℝ) : Integer.Sparse.eval row17616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17616, Integer.Sparse.eval_collectBalanced, rawRowCheck17616]

theorem rawRowCheck17617 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17617 := by decide +kernel

theorem rowCheck17617 : row17617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17617 := by decide +kernel

theorem rowEval17617 (x : Key → ℝ) : Integer.Sparse.eval row17617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17617, Integer.Sparse.eval_collectBalanced, rawRowCheck17617]

theorem rawRowCheck17618 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17618 := by decide +kernel

theorem rowCheck17618 : row17618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17618 := by decide +kernel

theorem rowEval17618 (x : Key → ℝ) : Integer.Sparse.eval row17618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17618, Integer.Sparse.eval_collectBalanced, rawRowCheck17618]

theorem rawRowCheck17619 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17619 := by decide +kernel

theorem rowCheck17619 : row17619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17619 := by decide +kernel

theorem rowEval17619 (x : Key → ℝ) : Integer.Sparse.eval row17619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17619, Integer.Sparse.eval_collectBalanced, rawRowCheck17619]

theorem rawRowCheck17620 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17620 := by decide +kernel

theorem rowCheck17620 : row17620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17620 := by decide +kernel

theorem rowEval17620 (x : Key → ℝ) : Integer.Sparse.eval row17620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17620, Integer.Sparse.eval_collectBalanced, rawRowCheck17620]

theorem rawRowCheck17621 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17621 := by decide +kernel

theorem rowCheck17621 : row17621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17621 := by decide +kernel

theorem rowEval17621 (x : Key → ℝ) : Integer.Sparse.eval row17621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17621, Integer.Sparse.eval_collectBalanced, rawRowCheck17621]

theorem rawRowCheck17622 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17622 := by decide +kernel

theorem rowCheck17622 : row17622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17622 := by decide +kernel

theorem rowEval17622 (x : Key → ℝ) : Integer.Sparse.eval row17622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17622, Integer.Sparse.eval_collectBalanced, rawRowCheck17622]

theorem rawRowCheck17623 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17623 := by decide +kernel

theorem rowCheck17623 : row17623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17623 := by decide +kernel

theorem rowEval17623 (x : Key → ℝ) : Integer.Sparse.eval row17623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17623, Integer.Sparse.eval_collectBalanced, rawRowCheck17623]

theorem rawRowCheck17624 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17624 := by decide +kernel

theorem rowCheck17624 : row17624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17624 := by decide +kernel

theorem rowEval17624 (x : Key → ℝ) : Integer.Sparse.eval row17624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17624, Integer.Sparse.eval_collectBalanced, rawRowCheck17624]

theorem rawRowCheck17625 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17625 := by decide +kernel

theorem rowCheck17625 : row17625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17625 := by decide +kernel

theorem rowEval17625 (x : Key → ℝ) : Integer.Sparse.eval row17625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17625, Integer.Sparse.eval_collectBalanced, rawRowCheck17625]

theorem rawRowCheck17626 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form0 = rawRow17626 := by decide +kernel

theorem rowCheck17626 : row17626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17626 := by decide +kernel

theorem rowEval17626 (x : Key → ℝ) : Integer.Sparse.eval row17626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17626, Integer.Sparse.eval_collectBalanced, rawRowCheck17626]

theorem rawRowCheck17627 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form0 = rawRow17627 := by decide +kernel

theorem rowCheck17627 : row17627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17627 := by decide +kernel

theorem rowEval17627 (x : Key → ℝ) : Integer.Sparse.eval row17627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17627, Integer.Sparse.eval_collectBalanced, rawRowCheck17627]

theorem rawRowCheck17628 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form0 = rawRow17628 := by decide +kernel

theorem rowCheck17628 : row17628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17628 := by decide +kernel

theorem rowEval17628 (x : Key → ℝ) : Integer.Sparse.eval row17628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17628, Integer.Sparse.eval_collectBalanced, rawRowCheck17628]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block4.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form19.terms k).tag (GramFunctions.Block4.form19.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17411 x
  · exact rowEval17412 x
  · exact rowEval17413 x
  · exact rowEval17414 x
  · exact rowEval17415 x
  · exact rowEval17416 x
  · exact rowEval17417 x
  · exact rowEval17418 x
  · exact rowEval17419 x
  · exact rowEval17420 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block4.form19.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form19 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block4.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form2.terms k).tag (GramFunctions.Block4.form2.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13245 x
  · exact rowEval13246 x
  · exact rowEval13247 x
  · exact rowEval13248 x
  · exact rowEval13249 x
  · exact rowEval13250 x
  · exact rowEval13251 x
  · exact rowEval13252 x
  · exact rowEval13253 x
  · exact rowEval13254 x
  · exact rowEval13255 x
  · exact rowEval13256 x
  · exact rowEval13257 x
  · exact rowEval13258 x
  · exact rowEval13259 x
  · exact rowEval13260 x
  · exact rowEval13261 x
  · exact rowEval13262 x
  · exact rowEval13263 x
  · exact rowEval13264 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block4.form2.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form2 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17989 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0 = rawRow17989 := by decide +kernel

theorem rowCheck17989 : row17989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17989 := by decide +kernel

theorem rowEval17989 (x : Key → ℝ) : Integer.Sparse.eval row17989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17989, Integer.Sparse.eval_collectBalanced, rawRowCheck17989]

theorem rawRowCheck17990 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0 = rawRow17990 := by decide +kernel

theorem rowCheck17990 : row17990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17990 := by decide +kernel

theorem rowEval17990 (x : Key → ℝ) : Integer.Sparse.eval row17990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17990, Integer.Sparse.eval_collectBalanced, rawRowCheck17990]

theorem rawRowCheck17991 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0 = rawRow17991 := by decide +kernel

theorem rowCheck17991 : row17991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17991 := by decide +kernel

theorem rowEval17991 (x : Key → ℝ) : Integer.Sparse.eval row17991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17991, Integer.Sparse.eval_collectBalanced, rawRowCheck17991]

theorem rawRowCheck17992 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0 = rawRow17992 := by decide +kernel

theorem rowCheck17992 : row17992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17992 := by decide +kernel

theorem rowEval17992 (x : Key → ℝ) : Integer.Sparse.eval row17992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17992, Integer.Sparse.eval_collectBalanced, rawRowCheck17992]

theorem rawRowCheck17993 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0 = rawRow17993 := by decide +kernel

theorem rowCheck17993 : row17993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17993 := by decide +kernel

theorem rowEval17993 (x : Key → ℝ) : Integer.Sparse.eval row17993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17993, Integer.Sparse.eval_collectBalanced, rawRowCheck17993]

theorem rawRowCheck17994 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0 = rawRow17994 := by decide +kernel

theorem rowCheck17994 : row17994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17994 := by decide +kernel

theorem rowEval17994 (x : Key → ℝ) : Integer.Sparse.eval row17994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17994, Integer.Sparse.eval_collectBalanced, rawRowCheck17994]

theorem rawRowCheck17995 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0 = rawRow17995 := by decide +kernel

theorem rowCheck17995 : row17995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17995 := by decide +kernel

theorem rowEval17995 (x : Key → ℝ) : Integer.Sparse.eval row17995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17995, Integer.Sparse.eval_collectBalanced, rawRowCheck17995]

theorem rawRowCheck17996 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0 = rawRow17996 := by decide +kernel

theorem rowCheck17996 : row17996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17996 := by decide +kernel

theorem rowEval17996 (x : Key → ℝ) : Integer.Sparse.eval row17996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17996, Integer.Sparse.eval_collectBalanced, rawRowCheck17996]

theorem rawRowCheck17997 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0 = rawRow17997 := by decide +kernel

theorem rowCheck17997 : row17997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17997 := by decide +kernel

theorem rowEval17997 (x : Key → ℝ) : Integer.Sparse.eval row17997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17997, Integer.Sparse.eval_collectBalanced, rawRowCheck17997]

theorem rawRowCheck17998 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17998 := by decide +kernel

theorem rowCheck17998 : row17998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17998 := by decide +kernel

theorem rowEval17998 (x : Key → ℝ) : Integer.Sparse.eval row17998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17998, Integer.Sparse.eval_collectBalanced, rawRowCheck17998]

theorem rawRowCheck17999 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17999 := by decide +kernel

theorem rowCheck17999 : row17999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17999 := by decide +kernel

theorem rowEval17999 (x : Key → ℝ) : Integer.Sparse.eval row17999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17999, Integer.Sparse.eval_collectBalanced, rawRowCheck17999]

theorem rawRowCheck18000 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18000 := by decide +kernel

theorem rowCheck18000 : row18000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18000 := by decide +kernel

theorem rowEval18000 (x : Key → ℝ) : Integer.Sparse.eval row18000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18000, Integer.Sparse.eval_collectBalanced, rawRowCheck18000]

theorem rawRowCheck18001 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0 = rawRow18001 := by decide +kernel

theorem rowCheck18001 : row18001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18001 := by decide +kernel

theorem rowEval18001 (x : Key → ℝ) : Integer.Sparse.eval row18001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18001, Integer.Sparse.eval_collectBalanced, rawRowCheck18001]

theorem rawRowCheck18002 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0 = rawRow18002 := by decide +kernel

theorem rowCheck18002 : row18002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18002 := by decide +kernel

theorem rowEval18002 (x : Key → ℝ) : Integer.Sparse.eval row18002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18002, Integer.Sparse.eval_collectBalanced, rawRowCheck18002]

theorem rawRowCheck18003 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0 = rawRow18003 := by decide +kernel

theorem rowCheck18003 : row18003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18003 := by decide +kernel

theorem rowEval18003 (x : Key → ℝ) : Integer.Sparse.eval row18003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18003, Integer.Sparse.eval_collectBalanced, rawRowCheck18003]

theorem rawRowCheck18004 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18004 := by decide +kernel

theorem rowCheck18004 : row18004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18004 := by decide +kernel

theorem rowEval18004 (x : Key → ℝ) : Integer.Sparse.eval row18004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18004, Integer.Sparse.eval_collectBalanced, rawRowCheck18004]

theorem rawRowCheck18005 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow18005 := by decide +kernel

theorem rowCheck18005 : row18005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18005 := by decide +kernel

theorem rowEval18005 (x : Key → ℝ) : Integer.Sparse.eval row18005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck18005, Integer.Sparse.eval_collectBalanced, rawRowCheck18005]

theorem rawRowCheck18006 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow18006 := by decide +kernel

theorem rowCheck18006 : row18006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18006 := by decide +kernel

theorem rowEval18006 (x : Key → ℝ) : Integer.Sparse.eval row18006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18006, Integer.Sparse.eval_collectBalanced, rawRowCheck18006]

theorem rawRowCheck18007 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow18007 := by decide +kernel

theorem rowCheck18007 : row18007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18007 := by decide +kernel

theorem rowEval18007 (x : Key → ℝ) : Integer.Sparse.eval row18007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18007, Integer.Sparse.eval_collectBalanced, rawRowCheck18007]

theorem rawRowCheck18008 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow18008 := by decide +kernel

theorem rowCheck18008 : row18008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18008 := by decide +kernel

theorem rowEval18008 (x : Key → ℝ) : Integer.Sparse.eval row18008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck18008, Integer.Sparse.eval_collectBalanced, rawRowCheck18008]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck20_0 : entry20_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_0 k)) := by decide +kernel

theorem rowsSound20_0 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17611 x
  · exact rowEval17612 x
  · exact rowEval17613 x
  · exact rowEval17614 x
  · exact rowEval17615 x
  · exact rowEval17616 x
  · exact rowEval17617 x
  · exact rowEval17618 x
  · exact rowEval17619 x
  · exact rowEval17620 x
  · exact rowEval17621 x
  · exact rowEval17622 x
  · exact rowEval17623 x
  · exact rowEval17624 x
  · exact rowEval17625 x
  · exact rowEval17626 x
  · exact rowEval17627 x
  · exact rowEval17628 x

theorem entryEval20_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_0 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck20_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck21_0 : entry21_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_0 k)) := by decide +kernel

theorem rowsSound21_0 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17989 x
  · exact rowEval17990 x
  · exact rowEval17991 x
  · exact rowEval17992 x
  · exact rowEval17993 x
  · exact rowEval17994 x
  · exact rowEval17995 x
  · exact rowEval17996 x
  · exact rowEval17997 x
  · exact rowEval17998 x
  · exact rowEval17999 x
  · exact rowEval18000 x
  · exact rowEval18001 x
  · exact rowEval18002 x
  · exact rowEval18003 x
  · exact rowEval18004 x
  · exact rowEval18005 x
  · exact rowEval18006 x
  · exact rowEval18007 x
  · exact rowEval18008 x

theorem entryEval21_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_0 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck21_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13312 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13312 := by decide +kernel

theorem rowCheck13312 : row13312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13312 := by decide +kernel

theorem rowEval13312 (x : Key → ℝ) : Integer.Sparse.eval row13312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13312, Integer.Sparse.eval_collectBalanced, rawRowCheck13312]

theorem rawRowCheck13313 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13313 := by decide +kernel

theorem rowCheck13313 : row13313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13313 := by decide +kernel

theorem rowEval13313 (x : Key → ℝ) : Integer.Sparse.eval row13313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13313, Integer.Sparse.eval_collectBalanced, rawRowCheck13313]

theorem rawRowCheck13314 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13314 := by decide +kernel

theorem rowCheck13314 : row13314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13314 := by decide +kernel

theorem rowEval13314 (x : Key → ℝ) : Integer.Sparse.eval row13314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13314, Integer.Sparse.eval_collectBalanced, rawRowCheck13314]

theorem rawRowCheck13315 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13315 := by decide +kernel

theorem rowCheck13315 : row13315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13315 := by decide +kernel

theorem rowEval13315 (x : Key → ℝ) : Integer.Sparse.eval row13315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13315, Integer.Sparse.eval_collectBalanced, rawRowCheck13315]

theorem rawRowCheck13316 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13316 := by decide +kernel

theorem rowCheck13316 : row13316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13316 := by decide +kernel

theorem rowEval13316 (x : Key → ℝ) : Integer.Sparse.eval row13316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13316, Integer.Sparse.eval_collectBalanced, rawRowCheck13316]

theorem rawRowCheck13317 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13317 := by decide +kernel

theorem rowCheck13317 : row13317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13317 := by decide +kernel

theorem rowEval13317 (x : Key → ℝ) : Integer.Sparse.eval row13317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13317, Integer.Sparse.eval_collectBalanced, rawRowCheck13317]

theorem rawRowCheck13318 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form0 = rawRow13318 := by decide +kernel

theorem rowCheck13318 : row13318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13318 := by decide +kernel

theorem rowEval13318 (x : Key → ℝ) : Integer.Sparse.eval row13318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13318, Integer.Sparse.eval_collectBalanced, rawRowCheck13318]

theorem rawRowCheck13319 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form0 = rawRow13319 := by decide +kernel

theorem rowCheck13319 : row13319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13319 := by decide +kernel

theorem rowEval13319 (x : Key → ℝ) : Integer.Sparse.eval row13319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13319, Integer.Sparse.eval_collectBalanced, rawRowCheck13319]

theorem rawRowCheck13320 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form0 = rawRow13320 := by decide +kernel

theorem rowCheck13320 : row13320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13320 := by decide +kernel

theorem rowEval13320 (x : Key → ℝ) : Integer.Sparse.eval row13320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13320, Integer.Sparse.eval_collectBalanced, rawRowCheck13320]

theorem rawRowCheck13321 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form0 = rawRow13321 := by decide +kernel

theorem rowCheck13321 : row13321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13321 := by decide +kernel

theorem rowEval13321 (x : Key → ℝ) : Integer.Sparse.eval row13321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13321, Integer.Sparse.eval_collectBalanced, rawRowCheck13321]

theorem rawRowCheck13322 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form0 = rawRow13322 := by decide +kernel

theorem rowCheck13322 : row13322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13322 := by decide +kernel

theorem rowEval13322 (x : Key → ℝ) : Integer.Sparse.eval row13322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13322, Integer.Sparse.eval_collectBalanced, rawRowCheck13322]

theorem rawRowCheck13323 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form0 = rawRow13323 := by decide +kernel

theorem rowCheck13323 : row13323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13323 := by decide +kernel

theorem rowEval13323 (x : Key → ℝ) : Integer.Sparse.eval row13323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13323, Integer.Sparse.eval_collectBalanced, rawRowCheck13323]

theorem rawRowCheck13324 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form0 = rawRow13324 := by decide +kernel

theorem rowCheck13324 : row13324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13324 := by decide +kernel

theorem rowEval13324 (x : Key → ℝ) : Integer.Sparse.eval row13324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13324, Integer.Sparse.eval_collectBalanced, rawRowCheck13324]

theorem rawRowCheck13385 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13385 := by decide +kernel

theorem rowCheck13385 : row13385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13385 := by decide +kernel

theorem rowEval13385 (x : Key → ℝ) : Integer.Sparse.eval row13385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13385, Integer.Sparse.eval_collectBalanced, rawRowCheck13385]

theorem rawRowCheck13386 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13386 := by decide +kernel

theorem rowCheck13386 : row13386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13386 := by decide +kernel

theorem rowEval13386 (x : Key → ℝ) : Integer.Sparse.eval row13386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13386, Integer.Sparse.eval_collectBalanced, rawRowCheck13386]

theorem rawRowCheck13387 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13387 := by decide +kernel

theorem rowCheck13387 : row13387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13387 := by decide +kernel

theorem rowEval13387 (x : Key → ℝ) : Integer.Sparse.eval row13387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13387, Integer.Sparse.eval_collectBalanced, rawRowCheck13387]

theorem rawRowCheck13388 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13388 := by decide +kernel

theorem rowCheck13388 : row13388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13388 := by decide +kernel

theorem rowEval13388 (x : Key → ℝ) : Integer.Sparse.eval row13388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13388, Integer.Sparse.eval_collectBalanced, rawRowCheck13388]

theorem rawRowCheck13389 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0 = rawRow13389 := by decide +kernel

theorem rowCheck13389 : row13389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13389 := by decide +kernel

theorem rowEval13389 (x : Key → ℝ) : Integer.Sparse.eval row13389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13389, Integer.Sparse.eval_collectBalanced, rawRowCheck13389]

theorem rawRowCheck13390 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0 = rawRow13390 := by decide +kernel

theorem rowCheck13390 : row13390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13390 := by decide +kernel

theorem rowEval13390 (x : Key → ℝ) : Integer.Sparse.eval row13390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13390, Integer.Sparse.eval_collectBalanced, rawRowCheck13390]

theorem rawRowCheck13391 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0 = rawRow13391 := by decide +kernel

theorem rowCheck13391 : row13391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13391 := by decide +kernel

theorem rowEval13391 (x : Key → ℝ) : Integer.Sparse.eval row13391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13391, Integer.Sparse.eval_collectBalanced, rawRowCheck13391]

theorem rawRowCheck13392 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13392 := by decide +kernel

theorem rowCheck13392 : row13392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13392 := by decide +kernel

theorem rowEval13392 (x : Key → ℝ) : Integer.Sparse.eval row13392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13392, Integer.Sparse.eval_collectBalanced, rawRowCheck13392]

theorem rawRowCheck13393 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13393 := by decide +kernel

theorem rowCheck13393 : row13393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13393 := by decide +kernel

theorem rowEval13393 (x : Key → ℝ) : Integer.Sparse.eval row13393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13393, Integer.Sparse.eval_collectBalanced, rawRowCheck13393]

theorem rawRowCheck13394 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13394 := by decide +kernel

theorem rowCheck13394 : row13394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13394 := by decide +kernel

theorem rowEval13394 (x : Key → ℝ) : Integer.Sparse.eval row13394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13394, Integer.Sparse.eval_collectBalanced, rawRowCheck13394]

theorem rawRowCheck13395 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13395 := by decide +kernel

theorem rowCheck13395 : row13395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13395 := by decide +kernel

theorem rowEval13395 (x : Key → ℝ) : Integer.Sparse.eval row13395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13395, Integer.Sparse.eval_collectBalanced, rawRowCheck13395]

theorem rawRowCheck13396 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13396 := by decide +kernel

theorem rowCheck13396 : row13396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13396 := by decide +kernel

theorem rowEval13396 (x : Key → ℝ) : Integer.Sparse.eval row13396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13396, Integer.Sparse.eval_collectBalanced, rawRowCheck13396]

theorem rawRowCheck13397 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13397 := by decide +kernel

theorem rowCheck13397 : row13397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13397 := by decide +kernel

theorem rowEval13397 (x : Key → ℝ) : Integer.Sparse.eval row13397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13397, Integer.Sparse.eval_collectBalanced, rawRowCheck13397]

theorem rawRowCheck13398 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13398 := by decide +kernel

theorem rowCheck13398 : row13398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13398 := by decide +kernel

theorem rowEval13398 (x : Key → ℝ) : Integer.Sparse.eval row13398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13398, Integer.Sparse.eval_collectBalanced, rawRowCheck13398]

theorem rawRowCheck13399 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13399 := by decide +kernel

theorem rowCheck13399 : row13399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13399 := by decide +kernel

theorem rowEval13399 (x : Key → ℝ) : Integer.Sparse.eval row13399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13399, Integer.Sparse.eval_collectBalanced, rawRowCheck13399]

theorem rawRowCheck13400 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13400 := by decide +kernel

theorem rowCheck13400 : row13400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13400 := by decide +kernel

theorem rowEval13400 (x : Key → ℝ) : Integer.Sparse.eval row13400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13400, Integer.Sparse.eval_collectBalanced, rawRowCheck13400]

theorem rawRowCheck13401 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13401 := by decide +kernel

theorem rowCheck13401 : row13401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13401 := by decide +kernel

theorem rowEval13401 (x : Key → ℝ) : Integer.Sparse.eval row13401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13401, Integer.Sparse.eval_collectBalanced, rawRowCheck13401]

theorem rawRowCheck13402 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13402 := by decide +kernel

theorem rowCheck13402 : row13402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13402 := by decide +kernel

theorem rowEval13402 (x : Key → ℝ) : Integer.Sparse.eval row13402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13402, Integer.Sparse.eval_collectBalanced, rawRowCheck13402]

theorem rawRowCheck13403 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13403 := by decide +kernel

theorem rowCheck13403 : row13403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13403 := by decide +kernel

theorem rowEval13403 (x : Key → ℝ) : Integer.Sparse.eval row13403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13403, Integer.Sparse.eval_collectBalanced, rawRowCheck13403]

theorem rawRowCheck13404 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13404 := by decide +kernel

theorem rowCheck13404 : row13404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13404 := by decide +kernel

theorem rowEval13404 (x : Key → ℝ) : Integer.Sparse.eval row13404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13404, Integer.Sparse.eval_collectBalanced, rawRowCheck13404]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block4.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form3.terms k).tag (GramFunctions.Block4.form3.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13305 x
  · exact rowEval13306 x
  · exact rowEval13307 x
  · exact rowEval13308 x
  · exact rowEval13309 x
  · exact rowEval13310 x
  · exact rowEval13311 x
  · exact rowEval13312 x
  · exact rowEval13313 x
  · exact rowEval13314 x
  · exact rowEval13315 x
  · exact rowEval13316 x
  · exact rowEval13317 x
  · exact rowEval13318 x
  · exact rowEval13319 x
  · exact rowEval13320 x
  · exact rowEval13321 x
  · exact rowEval13322 x
  · exact rowEval13323 x
  · exact rowEval13324 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block4.form3.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form3 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13485 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0 = rawRow13485 := by decide +kernel

theorem rowCheck13485 : row13485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13485 := by decide +kernel

theorem rowEval13485 (x : Key → ℝ) : Integer.Sparse.eval row13485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13485, Integer.Sparse.eval_collectBalanced, rawRowCheck13485]

theorem rawRowCheck13486 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0 = rawRow13486 := by decide +kernel

theorem rowCheck13486 : row13486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13486 := by decide +kernel

theorem rowEval13486 (x : Key → ℝ) : Integer.Sparse.eval row13486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13486, Integer.Sparse.eval_collectBalanced, rawRowCheck13486]

theorem rawRowCheck13487 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0 = rawRow13487 := by decide +kernel

theorem rowCheck13487 : row13487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13487 := by decide +kernel

theorem rowEval13487 (x : Key → ℝ) : Integer.Sparse.eval row13487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13487, Integer.Sparse.eval_collectBalanced, rawRowCheck13487]

theorem rawRowCheck13488 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13488 := by decide +kernel

theorem rowCheck13488 : row13488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13488 := by decide +kernel

theorem rowEval13488 (x : Key → ℝ) : Integer.Sparse.eval row13488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13488, Integer.Sparse.eval_collectBalanced, rawRowCheck13488]

theorem rawRowCheck13489 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13489 := by decide +kernel

theorem rowCheck13489 : row13489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13489 := by decide +kernel

theorem rowEval13489 (x : Key → ℝ) : Integer.Sparse.eval row13489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13489, Integer.Sparse.eval_collectBalanced, rawRowCheck13489]

theorem rawRowCheck13490 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13490 := by decide +kernel

theorem rowCheck13490 : row13490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13490 := by decide +kernel

theorem rowEval13490 (x : Key → ℝ) : Integer.Sparse.eval row13490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13490, Integer.Sparse.eval_collectBalanced, rawRowCheck13490]

theorem rawRowCheck13491 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13491 := by decide +kernel

theorem rowCheck13491 : row13491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13491 := by decide +kernel

theorem rowEval13491 (x : Key → ℝ) : Integer.Sparse.eval row13491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13491, Integer.Sparse.eval_collectBalanced, rawRowCheck13491]

theorem rawRowCheck13492 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13492 := by decide +kernel

theorem rowCheck13492 : row13492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13492 := by decide +kernel

theorem rowEval13492 (x : Key → ℝ) : Integer.Sparse.eval row13492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13492, Integer.Sparse.eval_collectBalanced, rawRowCheck13492]

theorem rawRowCheck13493 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13493 := by decide +kernel

theorem rowCheck13493 : row13493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13493 := by decide +kernel

theorem rowEval13493 (x : Key → ℝ) : Integer.Sparse.eval row13493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13493, Integer.Sparse.eval_collectBalanced, rawRowCheck13493]

theorem rawRowCheck13494 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13494 := by decide +kernel

theorem rowCheck13494 : row13494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13494 := by decide +kernel

theorem rowEval13494 (x : Key → ℝ) : Integer.Sparse.eval row13494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13494, Integer.Sparse.eval_collectBalanced, rawRowCheck13494]

theorem rawRowCheck13495 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13495 := by decide +kernel

theorem rowCheck13495 : row13495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13495 := by decide +kernel

theorem rowEval13495 (x : Key → ℝ) : Integer.Sparse.eval row13495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13495, Integer.Sparse.eval_collectBalanced, rawRowCheck13495]

theorem rawRowCheck13496 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13496 := by decide +kernel

theorem rowCheck13496 : row13496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13496 := by decide +kernel

theorem rowEval13496 (x : Key → ℝ) : Integer.Sparse.eval row13496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13496, Integer.Sparse.eval_collectBalanced, rawRowCheck13496]

theorem rawRowCheck13497 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13497 := by decide +kernel

theorem rowCheck13497 : row13497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13497 := by decide +kernel

theorem rowEval13497 (x : Key → ℝ) : Integer.Sparse.eval row13497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13497, Integer.Sparse.eval_collectBalanced, rawRowCheck13497]

theorem rawRowCheck13498 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13498 := by decide +kernel

theorem rowCheck13498 : row13498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13498 := by decide +kernel

theorem rowEval13498 (x : Key → ℝ) : Integer.Sparse.eval row13498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13498, Integer.Sparse.eval_collectBalanced, rawRowCheck13498]

theorem rawRowCheck13499 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13499 := by decide +kernel

theorem rowCheck13499 : row13499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13499 := by decide +kernel

theorem rowEval13499 (x : Key → ℝ) : Integer.Sparse.eval row13499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13499, Integer.Sparse.eval_collectBalanced, rawRowCheck13499]

theorem rawRowCheck13500 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13500 := by decide +kernel

theorem rowCheck13500 : row13500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13500 := by decide +kernel

theorem rowEval13500 (x : Key → ℝ) : Integer.Sparse.eval row13500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13500, Integer.Sparse.eval_collectBalanced, rawRowCheck13500]

theorem rawRowCheck13501 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13501 := by decide +kernel

theorem rowCheck13501 : row13501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13501 := by decide +kernel

theorem rowEval13501 (x : Key → ℝ) : Integer.Sparse.eval row13501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13501, Integer.Sparse.eval_collectBalanced, rawRowCheck13501]

theorem rawRowCheck13502 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13502 := by decide +kernel

theorem rowCheck13502 : row13502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13502 := by decide +kernel

theorem rowEval13502 (x : Key → ℝ) : Integer.Sparse.eval row13502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13502, Integer.Sparse.eval_collectBalanced, rawRowCheck13502]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block4.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form4.terms k).tag (GramFunctions.Block4.form4.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13385 x
  · exact rowEval13386 x
  · exact rowEval13387 x
  · exact rowEval13388 x
  · exact rowEval13389 x
  · exact rowEval13390 x
  · exact rowEval13391 x
  · exact rowEval13392 x
  · exact rowEval13393 x
  · exact rowEval13394 x
  · exact rowEval13395 x
  · exact rowEval13396 x
  · exact rowEval13397 x
  · exact rowEval13398 x
  · exact rowEval13399 x
  · exact rowEval13400 x
  · exact rowEval13401 x
  · exact rowEval13402 x
  · exact rowEval13403 x
  · exact rowEval13404 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block4.form4.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form4 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_0 : entry5_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form5.terms k).coefficient) (rows5_0 k)) := by decide +kernel

theorem rowsSound5_0 (k : Fin GramFunctions.Block4.form5.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows5_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form5.terms k).tag (GramFunctions.Block4.form5.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13485 x
  · exact rowEval13486 x
  · exact rowEval13487 x
  · exact rowEval13488 x
  · exact rowEval13489 x
  · exact rowEval13490 x
  · exact rowEval13491 x
  · exact rowEval13492 x
  · exact rowEval13493 x
  · exact rowEval13494 x
  · exact rowEval13495 x
  · exact rowEval13496 x
  · exact rowEval13497 x
  · exact rowEval13498 x
  · exact rowEval13499 x
  · exact rowEval13500 x
  · exact rowEval13501 x
  · exact rowEval13502 x

theorem entryEval5_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry5_0 (GramNormalization.eval B) = GramFunctions.Block4.form5.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck5_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form5 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound5_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block4.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form7.terms k).tag (GramFunctions.Block4.form7.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13845 x
  · exact rowEval13846 x
  · exact rowEval13847 x
  · exact rowEval13848 x
  · exact rowEval13849 x
  · exact rowEval13850 x
  · exact rowEval13851 x
  · exact rowEval13852 x
  · exact rowEval13853 x
  · exact rowEval13854 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block4.form7.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form7 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block4.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form8.terms k).tag (GramFunctions.Block4.form8.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval13925 x
  · exact rowEval13926 x
  · exact rowEval13927 x
  · exact rowEval13928 x
  · exact rowEval13929 x
  · exact rowEval13930 x
  · exact rowEval13931 x
  · exact rowEval13932 x
  · exact rowEval13933 x
  · exact rowEval13934 x
  · exact rowEval13935 x
  · exact rowEval13936 x
  · exact rowEval13937 x
  · exact rowEval13938 x
  · exact rowEval13939 x
  · exact rowEval13940 x
  · exact rowEval13941 x
  · exact rowEval13942 x
  · exact rowEval13943 x
  · exact rowEval13944 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block4.form8.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form8 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block4.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form9.terms k).tag (GramFunctions.Block4.form9.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14105 x
  · exact rowEval14106 x
  · exact rowEval14107 x
  · exact rowEval14108 x
  · exact rowEval14109 x
  · exact rowEval14110 x
  · exact rowEval14111 x
  · exact rowEval14112 x
  · exact rowEval14113 x
  · exact rowEval14114 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block4.form9.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form9 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

theorem entryEvalRow0_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 0 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 0).mixedGram (GramFunctions.Block4.forms j) B := by
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
  · exact (entryEval6_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval7_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval8_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval9_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval10_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval11_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval12_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval13_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval14_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval15_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval16_0_e B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval17_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval18_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval19_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval20_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval21_0 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0_e_oai
