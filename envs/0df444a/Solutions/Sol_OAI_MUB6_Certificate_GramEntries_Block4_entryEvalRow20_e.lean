-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:46:02.895662+00:00
-- url     : https://prove2.me/submissions/1068db7f-9675-4c93-8159-4d9d0248e06d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block4_entryEval20_16_e

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

theorem rawRowCheck17629 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17629 := by decide +kernel

theorem rowCheck17629 : row17629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17629 := by decide +kernel

theorem rowEval17629 (x : Key → ℝ) : Integer.Sparse.eval row17629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17629, Integer.Sparse.eval_collectBalanced, rawRowCheck17629]

theorem rawRowCheck17630 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17630 := by decide +kernel

theorem rowCheck17630 : row17630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17630 := by decide +kernel

theorem rowEval17630 (x : Key → ℝ) : Integer.Sparse.eval row17630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17630, Integer.Sparse.eval_collectBalanced, rawRowCheck17630]

theorem rawRowCheck17631 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17631 := by decide +kernel

theorem rowCheck17631 : row17631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17631 := by decide +kernel

theorem rowEval17631 (x : Key → ℝ) : Integer.Sparse.eval row17631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17631, Integer.Sparse.eval_collectBalanced, rawRowCheck17631]

theorem rawRowCheck17632 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form1 = rawRow17632 := by decide +kernel

theorem rowCheck17632 : row17632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17632 := by decide +kernel

theorem rowEval17632 (x : Key → ℝ) : Integer.Sparse.eval row17632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17632, Integer.Sparse.eval_collectBalanced, rawRowCheck17632]

theorem rawRowCheck17633 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form1 = rawRow17633 := by decide +kernel

theorem rowCheck17633 : row17633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17633 := by decide +kernel

theorem rowEval17633 (x : Key → ℝ) : Integer.Sparse.eval row17633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17633, Integer.Sparse.eval_collectBalanced, rawRowCheck17633]

theorem rawRowCheck17634 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form1 = rawRow17634 := by decide +kernel

theorem rowCheck17634 : row17634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17634 := by decide +kernel

theorem rowEval17634 (x : Key → ℝ) : Integer.Sparse.eval row17634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17634, Integer.Sparse.eval_collectBalanced, rawRowCheck17634]

theorem rawRowCheck17635 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form1 = rawRow17635 := by decide +kernel

theorem rowCheck17635 : row17635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17635 := by decide +kernel

theorem rowEval17635 (x : Key → ℝ) : Integer.Sparse.eval row17635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17635, Integer.Sparse.eval_collectBalanced, rawRowCheck17635]

theorem rawRowCheck17636 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form1 = rawRow17636 := by decide +kernel

theorem rowCheck17636 : row17636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17636 := by decide +kernel

theorem rowEval17636 (x : Key → ℝ) : Integer.Sparse.eval row17636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17636, Integer.Sparse.eval_collectBalanced, rawRowCheck17636]

theorem rawRowCheck17637 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form1 = rawRow17637 := by decide +kernel

theorem rowCheck17637 : row17637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17637 := by decide +kernel

theorem rowEval17637 (x : Key → ℝ) : Integer.Sparse.eval row17637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17637, Integer.Sparse.eval_collectBalanced, rawRowCheck17637]

theorem rawRowCheck17638 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form1 = rawRow17638 := by decide +kernel

theorem rowCheck17638 : row17638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17638 := by decide +kernel

theorem rowEval17638 (x : Key → ℝ) : Integer.Sparse.eval row17638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17638, Integer.Sparse.eval_collectBalanced, rawRowCheck17638]

theorem rawRowCheck17639 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form1 = rawRow17639 := by decide +kernel

theorem rowCheck17639 : row17639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17639 := by decide +kernel

theorem rowEval17639 (x : Key → ℝ) : Integer.Sparse.eval row17639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17639, Integer.Sparse.eval_collectBalanced, rawRowCheck17639]

theorem rawRowCheck17640 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form1 = rawRow17640 := by decide +kernel

theorem rowCheck17640 : row17640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17640 := by decide +kernel

theorem rowEval17640 (x : Key → ℝ) : Integer.Sparse.eval row17640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17640, Integer.Sparse.eval_collectBalanced, rawRowCheck17640]

theorem rawRowCheck17641 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form1 = rawRow17641 := by decide +kernel

theorem rowCheck17641 : row17641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17641 := by decide +kernel

theorem rowEval17641 (x : Key → ℝ) : Integer.Sparse.eval row17641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17641, Integer.Sparse.eval_collectBalanced, rawRowCheck17641]

theorem rawRowCheck17642 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form1 = rawRow17642 := by decide +kernel

theorem rowCheck17642 : row17642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17642 := by decide +kernel

theorem rowEval17642 (x : Key → ℝ) : Integer.Sparse.eval row17642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17642, Integer.Sparse.eval_collectBalanced, rawRowCheck17642]

theorem rawRowCheck17643 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form1 = rawRow17643 := by decide +kernel

theorem rowCheck17643 : row17643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17643 := by decide +kernel

theorem rowEval17643 (x : Key → ℝ) : Integer.Sparse.eval row17643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17643, Integer.Sparse.eval_collectBalanced, rawRowCheck17643]

theorem rawRowCheck17644 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form1 = rawRow17644 := by decide +kernel

theorem rowCheck17644 : row17644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17644 := by decide +kernel

theorem rowEval17644 (x : Key → ℝ) : Integer.Sparse.eval row17644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17644, Integer.Sparse.eval_collectBalanced, rawRowCheck17644]

theorem rawRowCheck17645 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form1 = rawRow17645 := by decide +kernel

theorem rowCheck17645 : row17645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17645 := by decide +kernel

theorem rowEval17645 (x : Key → ℝ) : Integer.Sparse.eval row17645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17645, Integer.Sparse.eval_collectBalanced, rawRowCheck17645]

theorem rawRowCheck17646 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form1 = rawRow17646 := by decide +kernel

theorem rowCheck17646 : row17646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17646 := by decide +kernel

theorem rowEval17646 (x : Key → ℝ) : Integer.Sparse.eval row17646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17646, Integer.Sparse.eval_collectBalanced, rawRowCheck17646]

theorem rawRowCheck17647 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17647 := by decide +kernel

theorem rowCheck17647 : row17647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17647 := by decide +kernel

theorem rowEval17647 (x : Key → ℝ) : Integer.Sparse.eval row17647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17647, Integer.Sparse.eval_collectBalanced, rawRowCheck17647]

theorem rawRowCheck17648 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17648 := by decide +kernel

theorem rowCheck17648 : row17648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17648 := by decide +kernel

theorem rowEval17648 (x : Key → ℝ) : Integer.Sparse.eval row17648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17648, Integer.Sparse.eval_collectBalanced, rawRowCheck17648]

theorem rawRowCheck17649 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17649 := by decide +kernel

theorem rowCheck17649 : row17649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17649 := by decide +kernel

theorem rowEval17649 (x : Key → ℝ) : Integer.Sparse.eval row17649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17649, Integer.Sparse.eval_collectBalanced, rawRowCheck17649]

theorem rawRowCheck17650 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form2 = rawRow17650 := by decide +kernel

theorem rowCheck17650 : row17650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17650 := by decide +kernel

theorem rowEval17650 (x : Key → ℝ) : Integer.Sparse.eval row17650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17650, Integer.Sparse.eval_collectBalanced, rawRowCheck17650]

theorem rawRowCheck17651 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form2 = rawRow17651 := by decide +kernel

theorem rowCheck17651 : row17651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17651 := by decide +kernel

theorem rowEval17651 (x : Key → ℝ) : Integer.Sparse.eval row17651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17651, Integer.Sparse.eval_collectBalanced, rawRowCheck17651]

theorem rawRowCheck17652 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form2 = rawRow17652 := by decide +kernel

theorem rowCheck17652 : row17652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17652 := by decide +kernel

theorem rowEval17652 (x : Key → ℝ) : Integer.Sparse.eval row17652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17652, Integer.Sparse.eval_collectBalanced, rawRowCheck17652]

theorem rawRowCheck17653 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form2 = rawRow17653 := by decide +kernel

theorem rowCheck17653 : row17653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17653 := by decide +kernel

theorem rowEval17653 (x : Key → ℝ) : Integer.Sparse.eval row17653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17653, Integer.Sparse.eval_collectBalanced, rawRowCheck17653]

theorem rawRowCheck17654 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form2 = rawRow17654 := by decide +kernel

theorem rowCheck17654 : row17654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17654 := by decide +kernel

theorem rowEval17654 (x : Key → ℝ) : Integer.Sparse.eval row17654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17654, Integer.Sparse.eval_collectBalanced, rawRowCheck17654]

theorem rawRowCheck17655 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form2 = rawRow17655 := by decide +kernel

theorem rowCheck17655 : row17655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17655 := by decide +kernel

theorem rowEval17655 (x : Key → ℝ) : Integer.Sparse.eval row17655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17655, Integer.Sparse.eval_collectBalanced, rawRowCheck17655]

theorem rawRowCheck17656 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form2 = rawRow17656 := by decide +kernel

theorem rowCheck17656 : row17656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17656 := by decide +kernel

theorem rowEval17656 (x : Key → ℝ) : Integer.Sparse.eval row17656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17656, Integer.Sparse.eval_collectBalanced, rawRowCheck17656]

theorem rawRowCheck17657 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form2 = rawRow17657 := by decide +kernel

theorem rowCheck17657 : row17657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17657 := by decide +kernel

theorem rowEval17657 (x : Key → ℝ) : Integer.Sparse.eval row17657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17657, Integer.Sparse.eval_collectBalanced, rawRowCheck17657]

theorem rawRowCheck17658 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form2 = rawRow17658 := by decide +kernel

theorem rowCheck17658 : row17658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17658 := by decide +kernel

theorem rowEval17658 (x : Key → ℝ) : Integer.Sparse.eval row17658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17658, Integer.Sparse.eval_collectBalanced, rawRowCheck17658]

theorem rawRowCheck17659 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form2 = rawRow17659 := by decide +kernel

theorem rowCheck17659 : row17659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17659 := by decide +kernel

theorem rowEval17659 (x : Key → ℝ) : Integer.Sparse.eval row17659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17659, Integer.Sparse.eval_collectBalanced, rawRowCheck17659]

theorem rawRowCheck17660 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form2 = rawRow17660 := by decide +kernel

theorem rowCheck17660 : row17660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17660 := by decide +kernel

theorem rowEval17660 (x : Key → ℝ) : Integer.Sparse.eval row17660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17660, Integer.Sparse.eval_collectBalanced, rawRowCheck17660]

theorem rawRowCheck17661 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form2 = rawRow17661 := by decide +kernel

theorem rowCheck17661 : row17661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17661 := by decide +kernel

theorem rowEval17661 (x : Key → ℝ) : Integer.Sparse.eval row17661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17661, Integer.Sparse.eval_collectBalanced, rawRowCheck17661]

theorem rawRowCheck17662 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form2 = rawRow17662 := by decide +kernel

theorem rowCheck17662 : row17662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17662 := by decide +kernel

theorem rowEval17662 (x : Key → ℝ) : Integer.Sparse.eval row17662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17662, Integer.Sparse.eval_collectBalanced, rawRowCheck17662]

theorem rawRowCheck17663 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form2 = rawRow17663 := by decide +kernel

theorem rowCheck17663 : row17663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17663 := by decide +kernel

theorem rowEval17663 (x : Key → ℝ) : Integer.Sparse.eval row17663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17663, Integer.Sparse.eval_collectBalanced, rawRowCheck17663]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17664 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2 = rawRow17664 := by decide +kernel

theorem rowCheck17664 : row17664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17664 := by decide +kernel

theorem rowEval17664 (x : Key → ℝ) : Integer.Sparse.eval row17664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17664, Integer.Sparse.eval_collectBalanced, rawRowCheck17664]

theorem rawRowCheck17665 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17665 := by decide +kernel

theorem rowCheck17665 : row17665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17665 := by decide +kernel

theorem rowEval17665 (x : Key → ℝ) : Integer.Sparse.eval row17665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17665, Integer.Sparse.eval_collectBalanced, rawRowCheck17665]

theorem rawRowCheck17666 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17666 := by decide +kernel

theorem rowCheck17666 : row17666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17666 := by decide +kernel

theorem rowEval17666 (x : Key → ℝ) : Integer.Sparse.eval row17666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17666, Integer.Sparse.eval_collectBalanced, rawRowCheck17666]

theorem rawRowCheck17667 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17667 := by decide +kernel

theorem rowCheck17667 : row17667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17667 := by decide +kernel

theorem rowEval17667 (x : Key → ℝ) : Integer.Sparse.eval row17667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17667, Integer.Sparse.eval_collectBalanced, rawRowCheck17667]

theorem rawRowCheck17668 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form3 = rawRow17668 := by decide +kernel

theorem rowCheck17668 : row17668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17668 := by decide +kernel

theorem rowEval17668 (x : Key → ℝ) : Integer.Sparse.eval row17668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17668, Integer.Sparse.eval_collectBalanced, rawRowCheck17668]

theorem rawRowCheck17669 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form3 = rawRow17669 := by decide +kernel

theorem rowCheck17669 : row17669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17669 := by decide +kernel

theorem rowEval17669 (x : Key → ℝ) : Integer.Sparse.eval row17669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17669, Integer.Sparse.eval_collectBalanced, rawRowCheck17669]

theorem rawRowCheck17670 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form3 = rawRow17670 := by decide +kernel

theorem rowCheck17670 : row17670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17670 := by decide +kernel

theorem rowEval17670 (x : Key → ℝ) : Integer.Sparse.eval row17670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17670, Integer.Sparse.eval_collectBalanced, rawRowCheck17670]

theorem rawRowCheck17671 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form3 = rawRow17671 := by decide +kernel

theorem rowCheck17671 : row17671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17671 := by decide +kernel

theorem rowEval17671 (x : Key → ℝ) : Integer.Sparse.eval row17671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17671, Integer.Sparse.eval_collectBalanced, rawRowCheck17671]

theorem rawRowCheck17672 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form3 = rawRow17672 := by decide +kernel

theorem rowCheck17672 : row17672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17672 := by decide +kernel

theorem rowEval17672 (x : Key → ℝ) : Integer.Sparse.eval row17672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17672, Integer.Sparse.eval_collectBalanced, rawRowCheck17672]

theorem rawRowCheck17673 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form3 = rawRow17673 := by decide +kernel

theorem rowCheck17673 : row17673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17673 := by decide +kernel

theorem rowEval17673 (x : Key → ℝ) : Integer.Sparse.eval row17673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17673, Integer.Sparse.eval_collectBalanced, rawRowCheck17673]

theorem rawRowCheck17674 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form3 = rawRow17674 := by decide +kernel

theorem rowCheck17674 : row17674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17674 := by decide +kernel

theorem rowEval17674 (x : Key → ℝ) : Integer.Sparse.eval row17674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17674, Integer.Sparse.eval_collectBalanced, rawRowCheck17674]

theorem rawRowCheck17675 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form3 = rawRow17675 := by decide +kernel

theorem rowCheck17675 : row17675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17675 := by decide +kernel

theorem rowEval17675 (x : Key → ℝ) : Integer.Sparse.eval row17675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17675, Integer.Sparse.eval_collectBalanced, rawRowCheck17675]

theorem rawRowCheck17676 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form3 = rawRow17676 := by decide +kernel

theorem rowCheck17676 : row17676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17676 := by decide +kernel

theorem rowEval17676 (x : Key → ℝ) : Integer.Sparse.eval row17676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17676, Integer.Sparse.eval_collectBalanced, rawRowCheck17676]

theorem rawRowCheck17677 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form3 = rawRow17677 := by decide +kernel

theorem rowCheck17677 : row17677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17677 := by decide +kernel

theorem rowEval17677 (x : Key → ℝ) : Integer.Sparse.eval row17677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17677, Integer.Sparse.eval_collectBalanced, rawRowCheck17677]

theorem rawRowCheck17678 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form3 = rawRow17678 := by decide +kernel

theorem rowCheck17678 : row17678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17678 := by decide +kernel

theorem rowEval17678 (x : Key → ℝ) : Integer.Sparse.eval row17678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17678, Integer.Sparse.eval_collectBalanced, rawRowCheck17678]

theorem rawRowCheck17679 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form3 = rawRow17679 := by decide +kernel

theorem rowCheck17679 : row17679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17679 := by decide +kernel

theorem rowEval17679 (x : Key → ℝ) : Integer.Sparse.eval row17679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17679, Integer.Sparse.eval_collectBalanced, rawRowCheck17679]

theorem rawRowCheck17680 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form3 = rawRow17680 := by decide +kernel

theorem rowCheck17680 : row17680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17680 := by decide +kernel

theorem rowEval17680 (x : Key → ℝ) : Integer.Sparse.eval row17680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17680, Integer.Sparse.eval_collectBalanced, rawRowCheck17680]

theorem rawRowCheck17681 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form3 = rawRow17681 := by decide +kernel

theorem rowCheck17681 : row17681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17681 := by decide +kernel

theorem rowEval17681 (x : Key → ℝ) : Integer.Sparse.eval row17681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17681, Integer.Sparse.eval_collectBalanced, rawRowCheck17681]

theorem rawRowCheck17682 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form3 = rawRow17682 := by decide +kernel

theorem rowCheck17682 : row17682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17682 := by decide +kernel

theorem rowEval17682 (x : Key → ℝ) : Integer.Sparse.eval row17682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17682, Integer.Sparse.eval_collectBalanced, rawRowCheck17682]

theorem rawRowCheck17683 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17683 := by decide +kernel

theorem rowCheck17683 : row17683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17683 := by decide +kernel

theorem rowEval17683 (x : Key → ℝ) : Integer.Sparse.eval row17683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17683, Integer.Sparse.eval_collectBalanced, rawRowCheck17683]

theorem rawRowCheck17684 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17684 := by decide +kernel

theorem rowCheck17684 : row17684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17684 := by decide +kernel

theorem rowEval17684 (x : Key → ℝ) : Integer.Sparse.eval row17684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17684, Integer.Sparse.eval_collectBalanced, rawRowCheck17684]

theorem rawRowCheck17685 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17685 := by decide +kernel

theorem rowCheck17685 : row17685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17685 := by decide +kernel

theorem rowEval17685 (x : Key → ℝ) : Integer.Sparse.eval row17685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17685, Integer.Sparse.eval_collectBalanced, rawRowCheck17685]

theorem rawRowCheck17686 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17686 := by decide +kernel

theorem rowCheck17686 : row17686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17686 := by decide +kernel

theorem rowEval17686 (x : Key → ℝ) : Integer.Sparse.eval row17686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17686, Integer.Sparse.eval_collectBalanced, rawRowCheck17686]

theorem rawRowCheck17687 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17687 := by decide +kernel

theorem rowCheck17687 : row17687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17687 := by decide +kernel

theorem rowEval17687 (x : Key → ℝ) : Integer.Sparse.eval row17687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17687, Integer.Sparse.eval_collectBalanced, rawRowCheck17687]

theorem rawRowCheck17688 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17688 := by decide +kernel

theorem rowCheck17688 : row17688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17688 := by decide +kernel

theorem rowEval17688 (x : Key → ℝ) : Integer.Sparse.eval row17688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17688, Integer.Sparse.eval_collectBalanced, rawRowCheck17688]

theorem rawRowCheck17689 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17689 := by decide +kernel

theorem rowCheck17689 : row17689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17689 := by decide +kernel

theorem rowEval17689 (x : Key → ℝ) : Integer.Sparse.eval row17689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17689, Integer.Sparse.eval_collectBalanced, rawRowCheck17689]

theorem rawRowCheck17690 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17690 := by decide +kernel

theorem rowCheck17690 : row17690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17690 := by decide +kernel

theorem rowEval17690 (x : Key → ℝ) : Integer.Sparse.eval row17690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17690, Integer.Sparse.eval_collectBalanced, rawRowCheck17690]

theorem rawRowCheck17691 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17691 := by decide +kernel

theorem rowCheck17691 : row17691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17691 := by decide +kernel

theorem rowEval17691 (x : Key → ℝ) : Integer.Sparse.eval row17691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17691, Integer.Sparse.eval_collectBalanced, rawRowCheck17691]

theorem rawRowCheck17692 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4 = rawRow17692 := by decide +kernel

theorem rowCheck17692 : row17692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17692 := by decide +kernel

theorem rowEval17692 (x : Key → ℝ) : Integer.Sparse.eval row17692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17692, Integer.Sparse.eval_collectBalanced, rawRowCheck17692]

theorem rawRowCheck17693 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4 = rawRow17693 := by decide +kernel

theorem rowCheck17693 : row17693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17693 := by decide +kernel

theorem rowEval17693 (x : Key → ℝ) : Integer.Sparse.eval row17693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17693, Integer.Sparse.eval_collectBalanced, rawRowCheck17693]

theorem rawRowCheck17694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4 = rawRow17694 := by decide +kernel

theorem rowCheck17694 : row17694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17694 := by decide +kernel

theorem rowEval17694 (x : Key → ℝ) : Integer.Sparse.eval row17694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17694, Integer.Sparse.eval_collectBalanced, rawRowCheck17694]

theorem rawRowCheck17695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4 = rawRow17695 := by decide +kernel

theorem rowCheck17695 : row17695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17695 := by decide +kernel

theorem rowEval17695 (x : Key → ℝ) : Integer.Sparse.eval row17695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17695, Integer.Sparse.eval_collectBalanced, rawRowCheck17695]

theorem rawRowCheck17696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4 = rawRow17696 := by decide +kernel

theorem rowCheck17696 : row17696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17696 := by decide +kernel

theorem rowEval17696 (x : Key → ℝ) : Integer.Sparse.eval row17696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17696, Integer.Sparse.eval_collectBalanced, rawRowCheck17696]

theorem rawRowCheck17697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4 = rawRow17697 := by decide +kernel

theorem rowCheck17697 : row17697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17697 := by decide +kernel

theorem rowEval17697 (x : Key → ℝ) : Integer.Sparse.eval row17697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17697, Integer.Sparse.eval_collectBalanced, rawRowCheck17697]

theorem rawRowCheck17698 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4 = rawRow17698 := by decide +kernel

theorem rowCheck17698 : row17698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17698 := by decide +kernel

theorem rowEval17698 (x : Key → ℝ) : Integer.Sparse.eval row17698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17698, Integer.Sparse.eval_collectBalanced, rawRowCheck17698]

theorem rawRowCheck17699 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4 = rawRow17699 := by decide +kernel

theorem rowCheck17699 : row17699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17699 := by decide +kernel

theorem rowEval17699 (x : Key → ℝ) : Integer.Sparse.eval row17699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17699, Integer.Sparse.eval_collectBalanced, rawRowCheck17699]

theorem rawRowCheck17700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4 = rawRow17700 := by decide +kernel

theorem rowCheck17700 : row17700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17700 := by decide +kernel

theorem rowEval17700 (x : Key → ℝ) : Integer.Sparse.eval row17700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17700, Integer.Sparse.eval_collectBalanced, rawRowCheck17700]

theorem rawRowCheck17701 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17701 := by decide +kernel

theorem rowCheck17701 : row17701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17701 := by decide +kernel

theorem rowEval17701 (x : Key → ℝ) : Integer.Sparse.eval row17701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17701, Integer.Sparse.eval_collectBalanced, rawRowCheck17701]

theorem rawRowCheck17702 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17702 := by decide +kernel

theorem rowCheck17702 : row17702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17702 := by decide +kernel

theorem rowEval17702 (x : Key → ℝ) : Integer.Sparse.eval row17702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17702, Integer.Sparse.eval_collectBalanced, rawRowCheck17702]

theorem rawRowCheck17703 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17703 := by decide +kernel

theorem rowCheck17703 : row17703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17703 := by decide +kernel

theorem rowEval17703 (x : Key → ℝ) : Integer.Sparse.eval row17703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17703, Integer.Sparse.eval_collectBalanced, rawRowCheck17703]

theorem rawRowCheck17704 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17704 := by decide +kernel

theorem rowCheck17704 : row17704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17704 := by decide +kernel

theorem rowEval17704 (x : Key → ℝ) : Integer.Sparse.eval row17704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17704, Integer.Sparse.eval_collectBalanced, rawRowCheck17704]

theorem rawRowCheck17705 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17705 := by decide +kernel

theorem rowCheck17705 : row17705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17705 := by decide +kernel

theorem rowEval17705 (x : Key → ℝ) : Integer.Sparse.eval row17705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17705, Integer.Sparse.eval_collectBalanced, rawRowCheck17705]

theorem rawRowCheck17706 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17706 := by decide +kernel

theorem rowCheck17706 : row17706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17706 := by decide +kernel

theorem rowEval17706 (x : Key → ℝ) : Integer.Sparse.eval row17706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17706, Integer.Sparse.eval_collectBalanced, rawRowCheck17706]

theorem rawRowCheck17707 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17707 := by decide +kernel

theorem rowCheck17707 : row17707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17707 := by decide +kernel

theorem rowEval17707 (x : Key → ℝ) : Integer.Sparse.eval row17707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17707, Integer.Sparse.eval_collectBalanced, rawRowCheck17707]

theorem rawRowCheck17708 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17708 := by decide +kernel

theorem rowCheck17708 : row17708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17708 := by decide +kernel

theorem rowEval17708 (x : Key → ℝ) : Integer.Sparse.eval row17708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17708, Integer.Sparse.eval_collectBalanced, rawRowCheck17708]

theorem rawRowCheck17709 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17709 := by decide +kernel

theorem rowCheck17709 : row17709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17709 := by decide +kernel

theorem rowEval17709 (x : Key → ℝ) : Integer.Sparse.eval row17709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17709, Integer.Sparse.eval_collectBalanced, rawRowCheck17709]

theorem rawRowCheck17710 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5 = rawRow17710 := by decide +kernel

theorem rowCheck17710 : row17710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17710 := by decide +kernel

theorem rowEval17710 (x : Key → ℝ) : Integer.Sparse.eval row17710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17710, Integer.Sparse.eval_collectBalanced, rawRowCheck17710]

theorem rawRowCheck17711 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5 = rawRow17711 := by decide +kernel

theorem rowCheck17711 : row17711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17711 := by decide +kernel

theorem rowEval17711 (x : Key → ℝ) : Integer.Sparse.eval row17711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17711, Integer.Sparse.eval_collectBalanced, rawRowCheck17711]

theorem rawRowCheck17712 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5 = rawRow17712 := by decide +kernel

theorem rowCheck17712 : row17712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17712 := by decide +kernel

theorem rowEval17712 (x : Key → ℝ) : Integer.Sparse.eval row17712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17712, Integer.Sparse.eval_collectBalanced, rawRowCheck17712]

theorem rawRowCheck17713 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5 = rawRow17713 := by decide +kernel

theorem rowCheck17713 : row17713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17713 := by decide +kernel

theorem rowEval17713 (x : Key → ℝ) : Integer.Sparse.eval row17713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17713, Integer.Sparse.eval_collectBalanced, rawRowCheck17713]

theorem rawRowCheck17714 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5 = rawRow17714 := by decide +kernel

theorem rowCheck17714 : row17714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17714 := by decide +kernel

theorem rowEval17714 (x : Key → ℝ) : Integer.Sparse.eval row17714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17714, Integer.Sparse.eval_collectBalanced, rawRowCheck17714]

theorem rawRowCheck17715 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5 = rawRow17715 := by decide +kernel

theorem rowCheck17715 : row17715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17715 := by decide +kernel

theorem rowEval17715 (x : Key → ℝ) : Integer.Sparse.eval row17715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17715, Integer.Sparse.eval_collectBalanced, rawRowCheck17715]

theorem rawRowCheck17716 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5 = rawRow17716 := by decide +kernel

theorem rowCheck17716 : row17716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17716 := by decide +kernel

theorem rowEval17716 (x : Key → ℝ) : Integer.Sparse.eval row17716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17716, Integer.Sparse.eval_collectBalanced, rawRowCheck17716]

theorem rawRowCheck17717 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5 = rawRow17717 := by decide +kernel

theorem rowCheck17717 : row17717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17717 := by decide +kernel

theorem rowEval17717 (x : Key → ℝ) : Integer.Sparse.eval row17717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17717, Integer.Sparse.eval_collectBalanced, rawRowCheck17717]

theorem rawRowCheck17718 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5 = rawRow17718 := by decide +kernel

theorem rowCheck17718 : row17718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17718 := by decide +kernel

theorem rowEval17718 (x : Key → ℝ) : Integer.Sparse.eval row17718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17718, Integer.Sparse.eval_collectBalanced, rawRowCheck17718]

theorem rawRowCheck17719 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17719 := by decide +kernel

theorem rowCheck17719 : row17719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17719 := by decide +kernel

theorem rowEval17719 (x : Key → ℝ) : Integer.Sparse.eval row17719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17719, Integer.Sparse.eval_collectBalanced, rawRowCheck17719]

theorem rawRowCheck17720 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17720 := by decide +kernel

theorem rowCheck17720 : row17720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17720 := by decide +kernel

theorem rowEval17720 (x : Key → ℝ) : Integer.Sparse.eval row17720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17720, Integer.Sparse.eval_collectBalanced, rawRowCheck17720]

theorem rawRowCheck17721 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17721 := by decide +kernel

theorem rowCheck17721 : row17721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17721 := by decide +kernel

theorem rowEval17721 (x : Key → ℝ) : Integer.Sparse.eval row17721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17721, Integer.Sparse.eval_collectBalanced, rawRowCheck17721]

theorem rawRowCheck17722 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form6 = rawRow17722 := by decide +kernel

theorem rowCheck17722 : row17722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17722 := by decide +kernel

theorem rowEval17722 (x : Key → ℝ) : Integer.Sparse.eval row17722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17722, Integer.Sparse.eval_collectBalanced, rawRowCheck17722]

theorem rawRowCheck17723 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form6 = rawRow17723 := by decide +kernel

theorem rowCheck17723 : row17723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17723 := by decide +kernel

theorem rowEval17723 (x : Key → ℝ) : Integer.Sparse.eval row17723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17723, Integer.Sparse.eval_collectBalanced, rawRowCheck17723]

theorem rawRowCheck17724 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form6 = rawRow17724 := by decide +kernel

theorem rowCheck17724 : row17724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17724 := by decide +kernel

theorem rowEval17724 (x : Key → ℝ) : Integer.Sparse.eval row17724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17724, Integer.Sparse.eval_collectBalanced, rawRowCheck17724]

theorem rawRowCheck17725 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form6 = rawRow17725 := by decide +kernel

theorem rowCheck17725 : row17725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17725 := by decide +kernel

theorem rowEval17725 (x : Key → ℝ) : Integer.Sparse.eval row17725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17725, Integer.Sparse.eval_collectBalanced, rawRowCheck17725]

theorem rawRowCheck17726 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form6 = rawRow17726 := by decide +kernel

theorem rowCheck17726 : row17726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17726 := by decide +kernel

theorem rowEval17726 (x : Key → ℝ) : Integer.Sparse.eval row17726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17726, Integer.Sparse.eval_collectBalanced, rawRowCheck17726]

theorem rawRowCheck17727 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form6 = rawRow17727 := by decide +kernel

theorem rowCheck17727 : row17727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17727 := by decide +kernel

theorem rowEval17727 (x : Key → ℝ) : Integer.Sparse.eval row17727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17727, Integer.Sparse.eval_collectBalanced, rawRowCheck17727]

theorem rawRowCheck17728 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form6 = rawRow17728 := by decide +kernel

theorem rowCheck17728 : row17728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17728 := by decide +kernel

theorem rowEval17728 (x : Key → ℝ) : Integer.Sparse.eval row17728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17728, Integer.Sparse.eval_collectBalanced, rawRowCheck17728]

theorem rawRowCheck17729 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form6 = rawRow17729 := by decide +kernel

theorem rowCheck17729 : row17729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17729 := by decide +kernel

theorem rowEval17729 (x : Key → ℝ) : Integer.Sparse.eval row17729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17729, Integer.Sparse.eval_collectBalanced, rawRowCheck17729]

theorem rawRowCheck17730 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form6 = rawRow17730 := by decide +kernel

theorem rowCheck17730 : row17730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17730 := by decide +kernel

theorem rowEval17730 (x : Key → ℝ) : Integer.Sparse.eval row17730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17730, Integer.Sparse.eval_collectBalanced, rawRowCheck17730]

theorem rawRowCheck17731 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form6 = rawRow17731 := by decide +kernel

theorem rowCheck17731 : row17731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17731 := by decide +kernel

theorem rowEval17731 (x : Key → ℝ) : Integer.Sparse.eval row17731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17731, Integer.Sparse.eval_collectBalanced, rawRowCheck17731]

theorem rawRowCheck17732 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form6 = rawRow17732 := by decide +kernel

theorem rowCheck17732 : row17732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17732 := by decide +kernel

theorem rowEval17732 (x : Key → ℝ) : Integer.Sparse.eval row17732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17732, Integer.Sparse.eval_collectBalanced, rawRowCheck17732]

theorem rawRowCheck17733 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form6 = rawRow17733 := by decide +kernel

theorem rowCheck17733 : row17733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17733 := by decide +kernel

theorem rowEval17733 (x : Key → ℝ) : Integer.Sparse.eval row17733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17733, Integer.Sparse.eval_collectBalanced, rawRowCheck17733]

theorem rawRowCheck17734 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form6 = rawRow17734 := by decide +kernel

theorem rowCheck17734 : row17734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17734 := by decide +kernel

theorem rowEval17734 (x : Key → ℝ) : Integer.Sparse.eval row17734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17734, Integer.Sparse.eval_collectBalanced, rawRowCheck17734]

theorem rawRowCheck17735 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form6 = rawRow17735 := by decide +kernel

theorem rowCheck17735 : row17735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17735 := by decide +kernel

theorem rowEval17735 (x : Key → ℝ) : Integer.Sparse.eval row17735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17735, Integer.Sparse.eval_collectBalanced, rawRowCheck17735]

theorem rawRowCheck17736 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form6 = rawRow17736 := by decide +kernel

theorem rowCheck17736 : row17736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17736 := by decide +kernel

theorem rowEval17736 (x : Key → ℝ) : Integer.Sparse.eval row17736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17736, Integer.Sparse.eval_collectBalanced, rawRowCheck17736]

theorem rawRowCheck17737 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17737 := by decide +kernel

theorem rowCheck17737 : row17737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17737 := by decide +kernel

theorem rowEval17737 (x : Key → ℝ) : Integer.Sparse.eval row17737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17737, Integer.Sparse.eval_collectBalanced, rawRowCheck17737]

theorem rawRowCheck17738 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17738 := by decide +kernel

theorem rowCheck17738 : row17738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17738 := by decide +kernel

theorem rowEval17738 (x : Key → ℝ) : Integer.Sparse.eval row17738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17738, Integer.Sparse.eval_collectBalanced, rawRowCheck17738]

theorem rawRowCheck17739 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17739 := by decide +kernel

theorem rowCheck17739 : row17739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17739 := by decide +kernel

theorem rowEval17739 (x : Key → ℝ) : Integer.Sparse.eval row17739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17739, Integer.Sparse.eval_collectBalanced, rawRowCheck17739]

theorem rawRowCheck17740 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17740 := by decide +kernel

theorem rowCheck17740 : row17740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17740 := by decide +kernel

theorem rowEval17740 (x : Key → ℝ) : Integer.Sparse.eval row17740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17740, Integer.Sparse.eval_collectBalanced, rawRowCheck17740]

theorem rawRowCheck17741 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17741 := by decide +kernel

theorem rowCheck17741 : row17741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17741 := by decide +kernel

theorem rowEval17741 (x : Key → ℝ) : Integer.Sparse.eval row17741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17741, Integer.Sparse.eval_collectBalanced, rawRowCheck17741]

theorem rawRowCheck17742 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17742 := by decide +kernel

theorem rowCheck17742 : row17742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17742 := by decide +kernel

theorem rowEval17742 (x : Key → ℝ) : Integer.Sparse.eval row17742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17742, Integer.Sparse.eval_collectBalanced, rawRowCheck17742]

theorem rawRowCheck17743 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17743 := by decide +kernel

theorem rowCheck17743 : row17743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17743 := by decide +kernel

theorem rowEval17743 (x : Key → ℝ) : Integer.Sparse.eval row17743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17743, Integer.Sparse.eval_collectBalanced, rawRowCheck17743]

theorem rawRowCheck17744 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17744 := by decide +kernel

theorem rowCheck17744 : row17744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17744 := by decide +kernel

theorem rowEval17744 (x : Key → ℝ) : Integer.Sparse.eval row17744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17744, Integer.Sparse.eval_collectBalanced, rawRowCheck17744]

theorem rawRowCheck17745 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17745 := by decide +kernel

theorem rowCheck17745 : row17745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17745 := by decide +kernel

theorem rowEval17745 (x : Key → ℝ) : Integer.Sparse.eval row17745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17745, Integer.Sparse.eval_collectBalanced, rawRowCheck17745]

theorem rawRowCheck17746 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7 = rawRow17746 := by decide +kernel

theorem rowCheck17746 : row17746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17746 := by decide +kernel

theorem rowEval17746 (x : Key → ℝ) : Integer.Sparse.eval row17746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17746, Integer.Sparse.eval_collectBalanced, rawRowCheck17746]

theorem rawRowCheck17747 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7 = rawRow17747 := by decide +kernel

theorem rowCheck17747 : row17747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17747 := by decide +kernel

theorem rowEval17747 (x : Key → ℝ) : Integer.Sparse.eval row17747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17747, Integer.Sparse.eval_collectBalanced, rawRowCheck17747]

theorem rawRowCheck17748 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7 = rawRow17748 := by decide +kernel

theorem rowCheck17748 : row17748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17748 := by decide +kernel

theorem rowEval17748 (x : Key → ℝ) : Integer.Sparse.eval row17748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17748, Integer.Sparse.eval_collectBalanced, rawRowCheck17748]

theorem rawRowCheck17749 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7 = rawRow17749 := by decide +kernel

theorem rowCheck17749 : row17749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17749 := by decide +kernel

theorem rowEval17749 (x : Key → ℝ) : Integer.Sparse.eval row17749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17749, Integer.Sparse.eval_collectBalanced, rawRowCheck17749]

theorem rawRowCheck17750 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7 = rawRow17750 := by decide +kernel

theorem rowCheck17750 : row17750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17750 := by decide +kernel

theorem rowEval17750 (x : Key → ℝ) : Integer.Sparse.eval row17750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17750, Integer.Sparse.eval_collectBalanced, rawRowCheck17750]

theorem rawRowCheck17751 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7 = rawRow17751 := by decide +kernel

theorem rowCheck17751 : row17751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17751 := by decide +kernel

theorem rowEval17751 (x : Key → ℝ) : Integer.Sparse.eval row17751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17751, Integer.Sparse.eval_collectBalanced, rawRowCheck17751]

theorem rawRowCheck17752 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7 = rawRow17752 := by decide +kernel

theorem rowCheck17752 : row17752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17752 := by decide +kernel

theorem rowEval17752 (x : Key → ℝ) : Integer.Sparse.eval row17752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17752, Integer.Sparse.eval_collectBalanced, rawRowCheck17752]

theorem rawRowCheck17753 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7 = rawRow17753 := by decide +kernel

theorem rowCheck17753 : row17753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17753 := by decide +kernel

theorem rowEval17753 (x : Key → ℝ) : Integer.Sparse.eval row17753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17753, Integer.Sparse.eval_collectBalanced, rawRowCheck17753]

theorem rawRowCheck17754 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7 = rawRow17754 := by decide +kernel

theorem rowCheck17754 : row17754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17754 := by decide +kernel

theorem rowEval17754 (x : Key → ℝ) : Integer.Sparse.eval row17754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17754, Integer.Sparse.eval_collectBalanced, rawRowCheck17754]

theorem rawRowCheck17755 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17755 := by decide +kernel

theorem rowCheck17755 : row17755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17755 := by decide +kernel

theorem rowEval17755 (x : Key → ℝ) : Integer.Sparse.eval row17755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17755, Integer.Sparse.eval_collectBalanced, rawRowCheck17755]

theorem rawRowCheck17756 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17756 := by decide +kernel

theorem rowCheck17756 : row17756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17756 := by decide +kernel

theorem rowEval17756 (x : Key → ℝ) : Integer.Sparse.eval row17756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17756, Integer.Sparse.eval_collectBalanced, rawRowCheck17756]

theorem rawRowCheck17757 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17757 := by decide +kernel

theorem rowCheck17757 : row17757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17757 := by decide +kernel

theorem rowEval17757 (x : Key → ℝ) : Integer.Sparse.eval row17757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17757, Integer.Sparse.eval_collectBalanced, rawRowCheck17757]

theorem rawRowCheck17758 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form8 = rawRow17758 := by decide +kernel

theorem rowCheck17758 : row17758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17758 := by decide +kernel

theorem rowEval17758 (x : Key → ℝ) : Integer.Sparse.eval row17758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17758, Integer.Sparse.eval_collectBalanced, rawRowCheck17758]

theorem rawRowCheck17759 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form8 = rawRow17759 := by decide +kernel

theorem rowCheck17759 : row17759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17759 := by decide +kernel

theorem rowEval17759 (x : Key → ℝ) : Integer.Sparse.eval row17759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17759, Integer.Sparse.eval_collectBalanced, rawRowCheck17759]

theorem rawRowCheck17760 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form8 = rawRow17760 := by decide +kernel

theorem rowCheck17760 : row17760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17760 := by decide +kernel

theorem rowEval17760 (x : Key → ℝ) : Integer.Sparse.eval row17760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17760, Integer.Sparse.eval_collectBalanced, rawRowCheck17760]

theorem rawRowCheck17761 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form8 = rawRow17761 := by decide +kernel

theorem rowCheck17761 : row17761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17761 := by decide +kernel

theorem rowEval17761 (x : Key → ℝ) : Integer.Sparse.eval row17761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17761, Integer.Sparse.eval_collectBalanced, rawRowCheck17761]

theorem rawRowCheck17762 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form8 = rawRow17762 := by decide +kernel

theorem rowCheck17762 : row17762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17762 := by decide +kernel

theorem rowEval17762 (x : Key → ℝ) : Integer.Sparse.eval row17762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17762, Integer.Sparse.eval_collectBalanced, rawRowCheck17762]

theorem rawRowCheck17763 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form8 = rawRow17763 := by decide +kernel

theorem rowCheck17763 : row17763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17763 := by decide +kernel

theorem rowEval17763 (x : Key → ℝ) : Integer.Sparse.eval row17763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17763, Integer.Sparse.eval_collectBalanced, rawRowCheck17763]

theorem rawRowCheck17764 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form8 = rawRow17764 := by decide +kernel

theorem rowCheck17764 : row17764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17764 := by decide +kernel

theorem rowEval17764 (x : Key → ℝ) : Integer.Sparse.eval row17764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17764, Integer.Sparse.eval_collectBalanced, rawRowCheck17764]

theorem rawRowCheck17765 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form8 = rawRow17765 := by decide +kernel

theorem rowCheck17765 : row17765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17765 := by decide +kernel

theorem rowEval17765 (x : Key → ℝ) : Integer.Sparse.eval row17765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17765, Integer.Sparse.eval_collectBalanced, rawRowCheck17765]

theorem rawRowCheck17766 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form8 = rawRow17766 := by decide +kernel

theorem rowCheck17766 : row17766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17766 := by decide +kernel

theorem rowEval17766 (x : Key → ℝ) : Integer.Sparse.eval row17766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17766, Integer.Sparse.eval_collectBalanced, rawRowCheck17766]

theorem rawRowCheck17767 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form8 = rawRow17767 := by decide +kernel

theorem rowCheck17767 : row17767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17767 := by decide +kernel

theorem rowEval17767 (x : Key → ℝ) : Integer.Sparse.eval row17767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17767, Integer.Sparse.eval_collectBalanced, rawRowCheck17767]

theorem rawRowCheck17768 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form8 = rawRow17768 := by decide +kernel

theorem rowCheck17768 : row17768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17768 := by decide +kernel

theorem rowEval17768 (x : Key → ℝ) : Integer.Sparse.eval row17768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17768, Integer.Sparse.eval_collectBalanced, rawRowCheck17768]

theorem rawRowCheck17769 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form8 = rawRow17769 := by decide +kernel

theorem rowCheck17769 : row17769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17769 := by decide +kernel

theorem rowEval17769 (x : Key → ℝ) : Integer.Sparse.eval row17769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17769, Integer.Sparse.eval_collectBalanced, rawRowCheck17769]

theorem rawRowCheck17770 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form8 = rawRow17770 := by decide +kernel

theorem rowCheck17770 : row17770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17770 := by decide +kernel

theorem rowEval17770 (x : Key → ℝ) : Integer.Sparse.eval row17770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17770, Integer.Sparse.eval_collectBalanced, rawRowCheck17770]

theorem rawRowCheck17771 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form8 = rawRow17771 := by decide +kernel

theorem rowCheck17771 : row17771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17771 := by decide +kernel

theorem rowEval17771 (x : Key → ℝ) : Integer.Sparse.eval row17771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17771, Integer.Sparse.eval_collectBalanced, rawRowCheck17771]

theorem rawRowCheck17772 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form8 = rawRow17772 := by decide +kernel

theorem rowCheck17772 : row17772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17772 := by decide +kernel

theorem rowEval17772 (x : Key → ℝ) : Integer.Sparse.eval row17772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17772, Integer.Sparse.eval_collectBalanced, rawRowCheck17772]

theorem rawRowCheck17773 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17773 := by decide +kernel

theorem rowCheck17773 : row17773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17773 := by decide +kernel

theorem rowEval17773 (x : Key → ℝ) : Integer.Sparse.eval row17773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17773, Integer.Sparse.eval_collectBalanced, rawRowCheck17773]

theorem rawRowCheck17774 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17774 := by decide +kernel

theorem rowCheck17774 : row17774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17774 := by decide +kernel

theorem rowEval17774 (x : Key → ℝ) : Integer.Sparse.eval row17774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17774, Integer.Sparse.eval_collectBalanced, rawRowCheck17774]

theorem rawRowCheck17775 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17775 := by decide +kernel

theorem rowCheck17775 : row17775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17775 := by decide +kernel

theorem rowEval17775 (x : Key → ℝ) : Integer.Sparse.eval row17775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17775, Integer.Sparse.eval_collectBalanced, rawRowCheck17775]

theorem rawRowCheck17776 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17776 := by decide +kernel

theorem rowCheck17776 : row17776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17776 := by decide +kernel

theorem rowEval17776 (x : Key → ℝ) : Integer.Sparse.eval row17776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17776, Integer.Sparse.eval_collectBalanced, rawRowCheck17776]

theorem rawRowCheck17777 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17777 := by decide +kernel

theorem rowCheck17777 : row17777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17777 := by decide +kernel

theorem rowEval17777 (x : Key → ℝ) : Integer.Sparse.eval row17777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17777, Integer.Sparse.eval_collectBalanced, rawRowCheck17777]

theorem rawRowCheck17778 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17778 := by decide +kernel

theorem rowCheck17778 : row17778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17778 := by decide +kernel

theorem rowEval17778 (x : Key → ℝ) : Integer.Sparse.eval row17778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17778, Integer.Sparse.eval_collectBalanced, rawRowCheck17778]

theorem rawRowCheck17779 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17779 := by decide +kernel

theorem rowCheck17779 : row17779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17779 := by decide +kernel

theorem rowEval17779 (x : Key → ℝ) : Integer.Sparse.eval row17779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17779, Integer.Sparse.eval_collectBalanced, rawRowCheck17779]

theorem rawRowCheck17780 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17780 := by decide +kernel

theorem rowCheck17780 : row17780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17780 := by decide +kernel

theorem rowEval17780 (x : Key → ℝ) : Integer.Sparse.eval row17780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17780, Integer.Sparse.eval_collectBalanced, rawRowCheck17780]

theorem rawRowCheck17781 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17781 := by decide +kernel

theorem rowCheck17781 : row17781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17781 := by decide +kernel

theorem rowEval17781 (x : Key → ℝ) : Integer.Sparse.eval row17781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17781, Integer.Sparse.eval_collectBalanced, rawRowCheck17781]

theorem rawRowCheck17782 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9 = rawRow17782 := by decide +kernel

theorem rowCheck17782 : row17782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17782 := by decide +kernel

theorem rowEval17782 (x : Key → ℝ) : Integer.Sparse.eval row17782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17782, Integer.Sparse.eval_collectBalanced, rawRowCheck17782]

theorem rawRowCheck17783 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9 = rawRow17783 := by decide +kernel

theorem rowCheck17783 : row17783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17783 := by decide +kernel

theorem rowEval17783 (x : Key → ℝ) : Integer.Sparse.eval row17783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17783, Integer.Sparse.eval_collectBalanced, rawRowCheck17783]

theorem rawRowCheck17784 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9 = rawRow17784 := by decide +kernel

theorem rowCheck17784 : row17784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17784 := by decide +kernel

theorem rowEval17784 (x : Key → ℝ) : Integer.Sparse.eval row17784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17784, Integer.Sparse.eval_collectBalanced, rawRowCheck17784]

theorem rawRowCheck17785 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9 = rawRow17785 := by decide +kernel

theorem rowCheck17785 : row17785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17785 := by decide +kernel

theorem rowEval17785 (x : Key → ℝ) : Integer.Sparse.eval row17785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17785, Integer.Sparse.eval_collectBalanced, rawRowCheck17785]

theorem rawRowCheck17786 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9 = rawRow17786 := by decide +kernel

theorem rowCheck17786 : row17786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17786 := by decide +kernel

theorem rowEval17786 (x : Key → ℝ) : Integer.Sparse.eval row17786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17786, Integer.Sparse.eval_collectBalanced, rawRowCheck17786]

theorem rawRowCheck17787 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9 = rawRow17787 := by decide +kernel

theorem rowCheck17787 : row17787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17787 := by decide +kernel

theorem rowEval17787 (x : Key → ℝ) : Integer.Sparse.eval row17787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17787, Integer.Sparse.eval_collectBalanced, rawRowCheck17787]

theorem rawRowCheck17788 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9 = rawRow17788 := by decide +kernel

theorem rowCheck17788 : row17788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17788 := by decide +kernel

theorem rowEval17788 (x : Key → ℝ) : Integer.Sparse.eval row17788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17788, Integer.Sparse.eval_collectBalanced, rawRowCheck17788]

theorem rawRowCheck17789 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9 = rawRow17789 := by decide +kernel

theorem rowCheck17789 : row17789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17789 := by decide +kernel

theorem rowEval17789 (x : Key → ℝ) : Integer.Sparse.eval row17789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17789, Integer.Sparse.eval_collectBalanced, rawRowCheck17789]

theorem rawRowCheck17790 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9 = rawRow17790 := by decide +kernel

theorem rowCheck17790 : row17790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17790 := by decide +kernel

theorem rowEval17790 (x : Key → ℝ) : Integer.Sparse.eval row17790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17790, Integer.Sparse.eval_collectBalanced, rawRowCheck17790]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck17917 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form17 = rawRow17917 := by decide +kernel

theorem rowCheck17917 : row17917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17917 := by decide +kernel

theorem rowEval17917 (x : Key → ℝ) : Integer.Sparse.eval row17917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17917, Integer.Sparse.eval_collectBalanced, rawRowCheck17917]

theorem rawRowCheck17918 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form17 = rawRow17918 := by decide +kernel

theorem rowCheck17918 : row17918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17918 := by decide +kernel

theorem rowEval17918 (x : Key → ℝ) : Integer.Sparse.eval row17918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17918, Integer.Sparse.eval_collectBalanced, rawRowCheck17918]

theorem rawRowCheck17919 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form17 = rawRow17919 := by decide +kernel

theorem rowCheck17919 : row17919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17919 := by decide +kernel

theorem rowEval17919 (x : Key → ℝ) : Integer.Sparse.eval row17919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17919, Integer.Sparse.eval_collectBalanced, rawRowCheck17919]

end MUB6.Certificate.GramRows

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

theorem rawRowCheck17920 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form17 = rawRow17920 := by decide +kernel

theorem rowCheck17920 : row17920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17920 := by decide +kernel

theorem rowEval17920 (x : Key → ℝ) : Integer.Sparse.eval row17920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17920, Integer.Sparse.eval_collectBalanced, rawRowCheck17920]

theorem rawRowCheck17921 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form17 = rawRow17921 := by decide +kernel

theorem rowCheck17921 : row17921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17921 := by decide +kernel

theorem rowEval17921 (x : Key → ℝ) : Integer.Sparse.eval row17921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17921, Integer.Sparse.eval_collectBalanced, rawRowCheck17921]

theorem rawRowCheck17922 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form17 = rawRow17922 := by decide +kernel

theorem rowCheck17922 : row17922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17922 := by decide +kernel

theorem rowEval17922 (x : Key → ℝ) : Integer.Sparse.eval row17922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17922, Integer.Sparse.eval_collectBalanced, rawRowCheck17922]

theorem rawRowCheck17923 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form17 = rawRow17923 := by decide +kernel

theorem rowCheck17923 : row17923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17923 := by decide +kernel

theorem rowEval17923 (x : Key → ℝ) : Integer.Sparse.eval row17923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17923, Integer.Sparse.eval_collectBalanced, rawRowCheck17923]

theorem rawRowCheck17924 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form17 = rawRow17924 := by decide +kernel

theorem rowCheck17924 : row17924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17924 := by decide +kernel

theorem rowEval17924 (x : Key → ℝ) : Integer.Sparse.eval row17924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17924, Integer.Sparse.eval_collectBalanced, rawRowCheck17924]

theorem rawRowCheck17925 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form17 = rawRow17925 := by decide +kernel

theorem rowCheck17925 : row17925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17925 := by decide +kernel

theorem rowEval17925 (x : Key → ℝ) : Integer.Sparse.eval row17925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17925, Integer.Sparse.eval_collectBalanced, rawRowCheck17925]

theorem rawRowCheck17926 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form17 = rawRow17926 := by decide +kernel

theorem rowCheck17926 : row17926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17926 := by decide +kernel

theorem rowEval17926 (x : Key → ℝ) : Integer.Sparse.eval row17926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17926, Integer.Sparse.eval_collectBalanced, rawRowCheck17926]

theorem rawRowCheck17927 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form17 = rawRow17927 := by decide +kernel

theorem rowCheck17927 : row17927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17927 := by decide +kernel

theorem rowEval17927 (x : Key → ℝ) : Integer.Sparse.eval row17927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17927, Integer.Sparse.eval_collectBalanced, rawRowCheck17927]

theorem rawRowCheck17928 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form17 = rawRow17928 := by decide +kernel

theorem rowCheck17928 : row17928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17928 := by decide +kernel

theorem rowEval17928 (x : Key → ℝ) : Integer.Sparse.eval row17928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17928, Integer.Sparse.eval_collectBalanced, rawRowCheck17928]

theorem rawRowCheck17929 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form17 = rawRow17929 := by decide +kernel

theorem rowCheck17929 : row17929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17929 := by decide +kernel

theorem rowEval17929 (x : Key → ℝ) : Integer.Sparse.eval row17929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17929, Integer.Sparse.eval_collectBalanced, rawRowCheck17929]

theorem rawRowCheck17930 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form17 = rawRow17930 := by decide +kernel

theorem rowCheck17930 : row17930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17930 := by decide +kernel

theorem rowEval17930 (x : Key → ℝ) : Integer.Sparse.eval row17930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17930, Integer.Sparse.eval_collectBalanced, rawRowCheck17930]

theorem rawRowCheck17931 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form17 = rawRow17931 := by decide +kernel

theorem rowCheck17931 : row17931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17931 := by decide +kernel

theorem rowEval17931 (x : Key → ℝ) : Integer.Sparse.eval row17931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17931, Integer.Sparse.eval_collectBalanced, rawRowCheck17931]

theorem rawRowCheck17932 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form17 = rawRow17932 := by decide +kernel

theorem rowCheck17932 : row17932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17932 := by decide +kernel

theorem rowEval17932 (x : Key → ℝ) : Integer.Sparse.eval row17932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17932, Integer.Sparse.eval_collectBalanced, rawRowCheck17932]

theorem rawRowCheck17933 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form17 = rawRow17933 := by decide +kernel

theorem rowCheck17933 : row17933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17933 := by decide +kernel

theorem rowEval17933 (x : Key → ℝ) : Integer.Sparse.eval row17933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17933, Integer.Sparse.eval_collectBalanced, rawRowCheck17933]

theorem rawRowCheck17934 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form17 = rawRow17934 := by decide +kernel

theorem rowCheck17934 : row17934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17934 := by decide +kernel

theorem rowEval17934 (x : Key → ℝ) : Integer.Sparse.eval row17934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17934, Integer.Sparse.eval_collectBalanced, rawRowCheck17934]

theorem rawRowCheck17935 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form18 = rawRow17935 := by decide +kernel

theorem rowCheck17935 : row17935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17935 := by decide +kernel

theorem rowEval17935 (x : Key → ℝ) : Integer.Sparse.eval row17935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17935, Integer.Sparse.eval_collectBalanced, rawRowCheck17935]

theorem rawRowCheck17936 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form18 = rawRow17936 := by decide +kernel

theorem rowCheck17936 : row17936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17936 := by decide +kernel

theorem rowEval17936 (x : Key → ℝ) : Integer.Sparse.eval row17936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17936, Integer.Sparse.eval_collectBalanced, rawRowCheck17936]

theorem rawRowCheck17937 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form18 = rawRow17937 := by decide +kernel

theorem rowCheck17937 : row17937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17937 := by decide +kernel

theorem rowEval17937 (x : Key → ℝ) : Integer.Sparse.eval row17937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17937, Integer.Sparse.eval_collectBalanced, rawRowCheck17937]

theorem rawRowCheck17938 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form18 = rawRow17938 := by decide +kernel

theorem rowCheck17938 : row17938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17938 := by decide +kernel

theorem rowEval17938 (x : Key → ℝ) : Integer.Sparse.eval row17938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17938, Integer.Sparse.eval_collectBalanced, rawRowCheck17938]

theorem rawRowCheck17939 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form18 = rawRow17939 := by decide +kernel

theorem rowCheck17939 : row17939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17939 := by decide +kernel

theorem rowEval17939 (x : Key → ℝ) : Integer.Sparse.eval row17939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17939, Integer.Sparse.eval_collectBalanced, rawRowCheck17939]

theorem rawRowCheck17940 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form18 = rawRow17940 := by decide +kernel

theorem rowCheck17940 : row17940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17940 := by decide +kernel

theorem rowEval17940 (x : Key → ℝ) : Integer.Sparse.eval row17940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17940, Integer.Sparse.eval_collectBalanced, rawRowCheck17940]

theorem rawRowCheck17941 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form18 = rawRow17941 := by decide +kernel

theorem rowCheck17941 : row17941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17941 := by decide +kernel

theorem rowEval17941 (x : Key → ℝ) : Integer.Sparse.eval row17941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17941, Integer.Sparse.eval_collectBalanced, rawRowCheck17941]

theorem rawRowCheck17942 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form18 = rawRow17942 := by decide +kernel

theorem rowCheck17942 : row17942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17942 := by decide +kernel

theorem rowEval17942 (x : Key → ℝ) : Integer.Sparse.eval row17942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17942, Integer.Sparse.eval_collectBalanced, rawRowCheck17942]

theorem rawRowCheck17943 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form18 = rawRow17943 := by decide +kernel

theorem rowCheck17943 : row17943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17943 := by decide +kernel

theorem rowEval17943 (x : Key → ℝ) : Integer.Sparse.eval row17943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17943, Integer.Sparse.eval_collectBalanced, rawRowCheck17943]

theorem rawRowCheck17944 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form18 = rawRow17944 := by decide +kernel

theorem rowCheck17944 : row17944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17944 := by decide +kernel

theorem rowEval17944 (x : Key → ℝ) : Integer.Sparse.eval row17944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17944, Integer.Sparse.eval_collectBalanced, rawRowCheck17944]

theorem rawRowCheck17945 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form18 = rawRow17945 := by decide +kernel

theorem rowCheck17945 : row17945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17945 := by decide +kernel

theorem rowEval17945 (x : Key → ℝ) : Integer.Sparse.eval row17945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17945, Integer.Sparse.eval_collectBalanced, rawRowCheck17945]

theorem rawRowCheck17946 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form18 = rawRow17946 := by decide +kernel

theorem rowCheck17946 : row17946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17946 := by decide +kernel

theorem rowEval17946 (x : Key → ℝ) : Integer.Sparse.eval row17946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17946, Integer.Sparse.eval_collectBalanced, rawRowCheck17946]

theorem rawRowCheck17947 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form18 = rawRow17947 := by decide +kernel

theorem rowCheck17947 : row17947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17947 := by decide +kernel

theorem rowEval17947 (x : Key → ℝ) : Integer.Sparse.eval row17947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17947, Integer.Sparse.eval_collectBalanced, rawRowCheck17947]

theorem rawRowCheck17948 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form18 = rawRow17948 := by decide +kernel

theorem rowCheck17948 : row17948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17948 := by decide +kernel

theorem rowEval17948 (x : Key → ℝ) : Integer.Sparse.eval row17948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17948, Integer.Sparse.eval_collectBalanced, rawRowCheck17948]

theorem rawRowCheck17949 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form18 = rawRow17949 := by decide +kernel

theorem rowCheck17949 : row17949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17949 := by decide +kernel

theorem rowEval17949 (x : Key → ℝ) : Integer.Sparse.eval row17949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17949, Integer.Sparse.eval_collectBalanced, rawRowCheck17949]

theorem rawRowCheck17950 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form18 = rawRow17950 := by decide +kernel

theorem rowCheck17950 : row17950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17950 := by decide +kernel

theorem rowEval17950 (x : Key → ℝ) : Integer.Sparse.eval row17950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17950, Integer.Sparse.eval_collectBalanced, rawRowCheck17950]

theorem rawRowCheck17951 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form18 = rawRow17951 := by decide +kernel

theorem rowCheck17951 : row17951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17951 := by decide +kernel

theorem rowEval17951 (x : Key → ℝ) : Integer.Sparse.eval row17951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17951, Integer.Sparse.eval_collectBalanced, rawRowCheck17951]

theorem rawRowCheck17952 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form18 = rawRow17952 := by decide +kernel

theorem rowCheck17952 : row17952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17952 := by decide +kernel

theorem rowEval17952 (x : Key → ℝ) : Integer.Sparse.eval row17952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17952, Integer.Sparse.eval_collectBalanced, rawRowCheck17952]

theorem rawRowCheck17953 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19 = rawRow17953 := by decide +kernel

theorem rowCheck17953 : row17953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17953 := by decide +kernel

theorem rowEval17953 (x : Key → ℝ) : Integer.Sparse.eval row17953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17953, Integer.Sparse.eval_collectBalanced, rawRowCheck17953]

theorem rawRowCheck17954 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19 = rawRow17954 := by decide +kernel

theorem rowCheck17954 : row17954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17954 := by decide +kernel

theorem rowEval17954 (x : Key → ℝ) : Integer.Sparse.eval row17954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17954, Integer.Sparse.eval_collectBalanced, rawRowCheck17954]

theorem rawRowCheck17955 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19 = rawRow17955 := by decide +kernel

theorem rowCheck17955 : row17955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17955 := by decide +kernel

theorem rowEval17955 (x : Key → ℝ) : Integer.Sparse.eval row17955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17955, Integer.Sparse.eval_collectBalanced, rawRowCheck17955]

theorem rawRowCheck17956 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17956 := by decide +kernel

theorem rowCheck17956 : row17956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17956 := by decide +kernel

theorem rowEval17956 (x : Key → ℝ) : Integer.Sparse.eval row17956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17956, Integer.Sparse.eval_collectBalanced, rawRowCheck17956]

theorem rawRowCheck17957 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17957 := by decide +kernel

theorem rowCheck17957 : row17957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17957 := by decide +kernel

theorem rowEval17957 (x : Key → ℝ) : Integer.Sparse.eval row17957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17957, Integer.Sparse.eval_collectBalanced, rawRowCheck17957]

theorem rawRowCheck17958 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17958 := by decide +kernel

theorem rowCheck17958 : row17958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17958 := by decide +kernel

theorem rowEval17958 (x : Key → ℝ) : Integer.Sparse.eval row17958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17958, Integer.Sparse.eval_collectBalanced, rawRowCheck17958]

theorem rawRowCheck17959 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17959 := by decide +kernel

theorem rowCheck17959 : row17959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17959 := by decide +kernel

theorem rowEval17959 (x : Key → ℝ) : Integer.Sparse.eval row17959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17959, Integer.Sparse.eval_collectBalanced, rawRowCheck17959]

theorem rawRowCheck17960 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17960 := by decide +kernel

theorem rowCheck17960 : row17960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17960 := by decide +kernel

theorem rowEval17960 (x : Key → ℝ) : Integer.Sparse.eval row17960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17960, Integer.Sparse.eval_collectBalanced, rawRowCheck17960]

theorem rawRowCheck17961 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17961 := by decide +kernel

theorem rowCheck17961 : row17961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17961 := by decide +kernel

theorem rowEval17961 (x : Key → ℝ) : Integer.Sparse.eval row17961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17961, Integer.Sparse.eval_collectBalanced, rawRowCheck17961]

theorem rawRowCheck17962 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19 = rawRow17962 := by decide +kernel

theorem rowCheck17962 : row17962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17962 := by decide +kernel

theorem rowEval17962 (x : Key → ℝ) : Integer.Sparse.eval row17962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17962, Integer.Sparse.eval_collectBalanced, rawRowCheck17962]

theorem rawRowCheck17963 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19 = rawRow17963 := by decide +kernel

theorem rowCheck17963 : row17963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17963 := by decide +kernel

theorem rowEval17963 (x : Key → ℝ) : Integer.Sparse.eval row17963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17963, Integer.Sparse.eval_collectBalanced, rawRowCheck17963]

theorem rawRowCheck17964 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19 = rawRow17964 := by decide +kernel

theorem rowCheck17964 : row17964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17964 := by decide +kernel

theorem rowEval17964 (x : Key → ℝ) : Integer.Sparse.eval row17964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17964, Integer.Sparse.eval_collectBalanced, rawRowCheck17964]

theorem rawRowCheck17965 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19 = rawRow17965 := by decide +kernel

theorem rowCheck17965 : row17965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17965 := by decide +kernel

theorem rowEval17965 (x : Key → ℝ) : Integer.Sparse.eval row17965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17965, Integer.Sparse.eval_collectBalanced, rawRowCheck17965]

theorem rawRowCheck17966 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19 = rawRow17966 := by decide +kernel

theorem rowCheck17966 : row17966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17966 := by decide +kernel

theorem rowEval17966 (x : Key → ℝ) : Integer.Sparse.eval row17966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck17966, Integer.Sparse.eval_collectBalanced, rawRowCheck17966]

theorem rawRowCheck17967 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19 = rawRow17967 := by decide +kernel

theorem rowCheck17967 : row17967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17967 := by decide +kernel

theorem rowEval17967 (x : Key → ℝ) : Integer.Sparse.eval row17967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17967, Integer.Sparse.eval_collectBalanced, rawRowCheck17967]

theorem rawRowCheck17968 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19 = rawRow17968 := by decide +kernel

theorem rowCheck17968 : row17968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17968 := by decide +kernel

theorem rowEval17968 (x : Key → ℝ) : Integer.Sparse.eval row17968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17968, Integer.Sparse.eval_collectBalanced, rawRowCheck17968]

theorem rawRowCheck17969 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19 = rawRow17969 := by decide +kernel

theorem rowCheck17969 : row17969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17969 := by decide +kernel

theorem rowEval17969 (x : Key → ℝ) : Integer.Sparse.eval row17969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17969, Integer.Sparse.eval_collectBalanced, rawRowCheck17969]

theorem rawRowCheck17970 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19 = rawRow17970 := by decide +kernel

theorem rowCheck17970 : row17970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17970 := by decide +kernel

theorem rowEval17970 (x : Key → ℝ) : Integer.Sparse.eval row17970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck17970, Integer.Sparse.eval_collectBalanced, rawRowCheck17970]

theorem rawRowCheck17971 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form20 = rawRow17971 := by decide +kernel

theorem rowCheck17971 : row17971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17971 := by decide +kernel

theorem rowEval17971 (x : Key → ℝ) : Integer.Sparse.eval row17971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17971, Integer.Sparse.eval_collectBalanced, rawRowCheck17971]

theorem rawRowCheck17972 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form20 = rawRow17972 := by decide +kernel

theorem rowCheck17972 : row17972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17972 := by decide +kernel

theorem rowEval17972 (x : Key → ℝ) : Integer.Sparse.eval row17972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17972, Integer.Sparse.eval_collectBalanced, rawRowCheck17972]

theorem rawRowCheck17973 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form20 = rawRow17973 := by decide +kernel

theorem rowCheck17973 : row17973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17973 := by decide +kernel

theorem rowEval17973 (x : Key → ℝ) : Integer.Sparse.eval row17973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17973, Integer.Sparse.eval_collectBalanced, rawRowCheck17973]

theorem rawRowCheck17974 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form20 = rawRow17974 := by decide +kernel

theorem rowCheck17974 : row17974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17974 := by decide +kernel

theorem rowEval17974 (x : Key → ℝ) : Integer.Sparse.eval row17974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17974, Integer.Sparse.eval_collectBalanced, rawRowCheck17974]

theorem rawRowCheck17975 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form20 = rawRow17975 := by decide +kernel

theorem rowCheck17975 : row17975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17975 := by decide +kernel

theorem rowEval17975 (x : Key → ℝ) : Integer.Sparse.eval row17975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17975, Integer.Sparse.eval_collectBalanced, rawRowCheck17975]

theorem rawRowCheck17976 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form20 = rawRow17976 := by decide +kernel

theorem rowCheck17976 : row17976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17976 := by decide +kernel

theorem rowEval17976 (x : Key → ℝ) : Integer.Sparse.eval row17976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17976, Integer.Sparse.eval_collectBalanced, rawRowCheck17976]

theorem rawRowCheck17977 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form20 = rawRow17977 := by decide +kernel

theorem rowCheck17977 : row17977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17977 := by decide +kernel

theorem rowEval17977 (x : Key → ℝ) : Integer.Sparse.eval row17977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17977, Integer.Sparse.eval_collectBalanced, rawRowCheck17977]

theorem rawRowCheck17978 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form20 = rawRow17978 := by decide +kernel

theorem rowCheck17978 : row17978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17978 := by decide +kernel

theorem rowEval17978 (x : Key → ℝ) : Integer.Sparse.eval row17978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17978, Integer.Sparse.eval_collectBalanced, rawRowCheck17978]

theorem rawRowCheck17979 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form20 = rawRow17979 := by decide +kernel

theorem rowCheck17979 : row17979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17979 := by decide +kernel

theorem rowEval17979 (x : Key → ℝ) : Integer.Sparse.eval row17979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17979, Integer.Sparse.eval_collectBalanced, rawRowCheck17979]

theorem rawRowCheck17980 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form20 = rawRow17980 := by decide +kernel

theorem rowCheck17980 : row17980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17980 := by decide +kernel

theorem rowEval17980 (x : Key → ℝ) : Integer.Sparse.eval row17980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17980, Integer.Sparse.eval_collectBalanced, rawRowCheck17980]

theorem rawRowCheck17981 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form20 = rawRow17981 := by decide +kernel

theorem rowCheck17981 : row17981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17981 := by decide +kernel

theorem rowEval17981 (x : Key → ℝ) : Integer.Sparse.eval row17981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17981, Integer.Sparse.eval_collectBalanced, rawRowCheck17981]

theorem rawRowCheck17982 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form20 = rawRow17982 := by decide +kernel

theorem rowCheck17982 : row17982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17982 := by decide +kernel

theorem rowEval17982 (x : Key → ℝ) : Integer.Sparse.eval row17982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17982, Integer.Sparse.eval_collectBalanced, rawRowCheck17982]

theorem rawRowCheck17983 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form20 = rawRow17983 := by decide +kernel

theorem rowCheck17983 : row17983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17983 := by decide +kernel

theorem rowEval17983 (x : Key → ℝ) : Integer.Sparse.eval row17983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17983, Integer.Sparse.eval_collectBalanced, rawRowCheck17983]

theorem rawRowCheck17984 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form20 = rawRow17984 := by decide +kernel

theorem rowCheck17984 : row17984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17984 := by decide +kernel

theorem rowEval17984 (x : Key → ℝ) : Integer.Sparse.eval row17984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck17984, Integer.Sparse.eval_collectBalanced, rawRowCheck17984]

theorem rawRowCheck17985 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form20 = rawRow17985 := by decide +kernel

theorem rowCheck17985 : row17985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17985 := by decide +kernel

theorem rowEval17985 (x : Key → ℝ) : Integer.Sparse.eval row17985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17985, Integer.Sparse.eval_collectBalanced, rawRowCheck17985]

theorem rawRowCheck17986 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form20 = rawRow17986 := by decide +kernel

theorem rowCheck17986 : row17986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17986 := by decide +kernel

theorem rowEval17986 (x : Key → ℝ) : Integer.Sparse.eval row17986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17986, Integer.Sparse.eval_collectBalanced, rawRowCheck17986]

theorem rawRowCheck17987 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form20 = rawRow17987 := by decide +kernel

theorem rowCheck17987 : row17987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17987 := by decide +kernel

theorem rowEval17987 (x : Key → ℝ) : Integer.Sparse.eval row17987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17987, Integer.Sparse.eval_collectBalanced, rawRowCheck17987]

theorem rawRowCheck17988 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form20 = rawRow17988 := by decide +kernel

theorem rowCheck17988 : row17988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17988 := by decide +kernel

theorem rowEval17988 (x : Key → ℝ) : Integer.Sparse.eval row17988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck17988, Integer.Sparse.eval_collectBalanced, rawRowCheck17988]

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

theorem entryCheck20_1 : entry20_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_1 k)) := by decide +kernel

theorem rowsSound20_1 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17629 x
  · exact rowEval17630 x
  · exact rowEval17631 x
  · exact rowEval17632 x
  · exact rowEval17633 x
  · exact rowEval17634 x
  · exact rowEval17635 x
  · exact rowEval17636 x
  · exact rowEval17637 x
  · exact rowEval17638 x
  · exact rowEval17639 x
  · exact rowEval17640 x
  · exact rowEval17641 x
  · exact rowEval17642 x
  · exact rowEval17643 x
  · exact rowEval17644 x
  · exact rowEval17645 x
  · exact rowEval17646 x

theorem entryEval20_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_1 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck20_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_1]

theorem entryCheck20_2 : entry20_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_2 k)) := by decide +kernel

theorem rowsSound20_2 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17647 x
  · exact rowEval17648 x
  · exact rowEval17649 x
  · exact rowEval17650 x
  · exact rowEval17651 x
  · exact rowEval17652 x
  · exact rowEval17653 x
  · exact rowEval17654 x
  · exact rowEval17655 x
  · exact rowEval17656 x
  · exact rowEval17657 x
  · exact rowEval17658 x
  · exact rowEval17659 x
  · exact rowEval17660 x
  · exact rowEval17661 x
  · exact rowEval17662 x
  · exact rowEval17663 x
  · exact rowEval17664 x

theorem entryEval20_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_2 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck20_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_2]

theorem entryCheck20_3 : entry20_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_3 k)) := by decide +kernel

theorem rowsSound20_3 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17665 x
  · exact rowEval17666 x
  · exact rowEval17667 x
  · exact rowEval17668 x
  · exact rowEval17669 x
  · exact rowEval17670 x
  · exact rowEval17671 x
  · exact rowEval17672 x
  · exact rowEval17673 x
  · exact rowEval17674 x
  · exact rowEval17675 x
  · exact rowEval17676 x
  · exact rowEval17677 x
  · exact rowEval17678 x
  · exact rowEval17679 x
  · exact rowEval17680 x
  · exact rowEval17681 x
  · exact rowEval17682 x

theorem entryEval20_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_3 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck20_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_3]

theorem entryCheck20_4 : entry20_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_4 k)) := by decide +kernel

theorem rowsSound20_4 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17683 x
  · exact rowEval17684 x
  · exact rowEval17685 x
  · exact rowEval17686 x
  · exact rowEval17687 x
  · exact rowEval17688 x
  · exact rowEval17689 x
  · exact rowEval17690 x
  · exact rowEval17691 x
  · exact rowEval17692 x
  · exact rowEval17693 x
  · exact rowEval17694 x
  · exact rowEval17695 x
  · exact rowEval17696 x
  · exact rowEval17697 x
  · exact rowEval17698 x
  · exact rowEval17699 x
  · exact rowEval17700 x

theorem entryEval20_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_4 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck20_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_4]

theorem entryCheck20_5 : entry20_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_5 k)) := by decide +kernel

theorem rowsSound20_5 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17701 x
  · exact rowEval17702 x
  · exact rowEval17703 x
  · exact rowEval17704 x
  · exact rowEval17705 x
  · exact rowEval17706 x
  · exact rowEval17707 x
  · exact rowEval17708 x
  · exact rowEval17709 x
  · exact rowEval17710 x
  · exact rowEval17711 x
  · exact rowEval17712 x
  · exact rowEval17713 x
  · exact rowEval17714 x
  · exact rowEval17715 x
  · exact rowEval17716 x
  · exact rowEval17717 x
  · exact rowEval17718 x

theorem entryEval20_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_5 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck20_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_5]

theorem entryCheck20_6 : entry20_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_6 k)) := by decide +kernel

theorem rowsSound20_6 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval17719 x
  · exact rowEval17720 x
  · exact rowEval17721 x
  · exact rowEval17722 x
  · exact rowEval17723 x
  · exact rowEval17724 x
  · exact rowEval17725 x
  · exact rowEval17726 x
  · exact rowEval17727 x
  · exact rowEval17728 x
  · exact rowEval17729 x
  · exact rowEval17730 x
  · exact rowEval17731 x
  · exact rowEval17732 x
  · exact rowEval17733 x
  · exact rowEval17734 x
  · exact rowEval17735 x
  · exact rowEval17736 x

theorem entryEval20_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_6 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck20_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_6]

theorem entryCheck20_7 : entry20_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_7 k)) := by decide +kernel

theorem rowsSound20_7 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17737 x
  · exact rowEval17738 x
  · exact rowEval17739 x
  · exact rowEval17740 x
  · exact rowEval17741 x
  · exact rowEval17742 x
  · exact rowEval17743 x
  · exact rowEval17744 x
  · exact rowEval17745 x
  · exact rowEval17746 x
  · exact rowEval17747 x
  · exact rowEval17748 x
  · exact rowEval17749 x
  · exact rowEval17750 x
  · exact rowEval17751 x
  · exact rowEval17752 x
  · exact rowEval17753 x
  · exact rowEval17754 x

theorem entryEval20_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_7 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck20_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_7]

theorem entryCheck20_8 : entry20_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_8 k)) := by decide +kernel

theorem rowsSound20_8 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17755 x
  · exact rowEval17756 x
  · exact rowEval17757 x
  · exact rowEval17758 x
  · exact rowEval17759 x
  · exact rowEval17760 x
  · exact rowEval17761 x
  · exact rowEval17762 x
  · exact rowEval17763 x
  · exact rowEval17764 x
  · exact rowEval17765 x
  · exact rowEval17766 x
  · exact rowEval17767 x
  · exact rowEval17768 x
  · exact rowEval17769 x
  · exact rowEval17770 x
  · exact rowEval17771 x
  · exact rowEval17772 x

theorem entryEval20_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_8 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck20_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_8]

theorem entryCheck20_9 : entry20_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_9 k)) := by decide +kernel

theorem rowsSound20_9 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17773 x
  · exact rowEval17774 x
  · exact rowEval17775 x
  · exact rowEval17776 x
  · exact rowEval17777 x
  · exact rowEval17778 x
  · exact rowEval17779 x
  · exact rowEval17780 x
  · exact rowEval17781 x
  · exact rowEval17782 x
  · exact rowEval17783 x
  · exact rowEval17784 x
  · exact rowEval17785 x
  · exact rowEval17786 x
  · exact rowEval17787 x
  · exact rowEval17788 x
  · exact rowEval17789 x
  · exact rowEval17790 x

theorem entryEval20_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_9 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck20_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_9]

theorem entryCheck20_17 : entry20_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_17 k)) := by decide +kernel

theorem rowsSound20_17 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17917 x
  · exact rowEval17918 x
  · exact rowEval17919 x
  · exact rowEval17920 x
  · exact rowEval17921 x
  · exact rowEval17922 x
  · exact rowEval17923 x
  · exact rowEval17924 x
  · exact rowEval17925 x
  · exact rowEval17926 x
  · exact rowEval17927 x
  · exact rowEval17928 x
  · exact rowEval17929 x
  · exact rowEval17930 x
  · exact rowEval17931 x
  · exact rowEval17932 x
  · exact rowEval17933 x
  · exact rowEval17934 x

theorem entryEval20_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_17 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck20_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_17]

theorem entryCheck20_18 : entry20_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_18 k)) := by decide +kernel

theorem rowsSound20_18 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17935 x
  · exact rowEval17936 x
  · exact rowEval17937 x
  · exact rowEval17938 x
  · exact rowEval17939 x
  · exact rowEval17940 x
  · exact rowEval17941 x
  · exact rowEval17942 x
  · exact rowEval17943 x
  · exact rowEval17944 x
  · exact rowEval17945 x
  · exact rowEval17946 x
  · exact rowEval17947 x
  · exact rowEval17948 x
  · exact rowEval17949 x
  · exact rowEval17950 x
  · exact rowEval17951 x
  · exact rowEval17952 x

theorem entryEval20_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_18 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck20_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_18]

theorem entryCheck20_19 : entry20_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_19 k)) := by decide +kernel

theorem rowsSound20_19 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form19) x := by
  fin_cases k
  · exact rowEval17953 x
  · exact rowEval17954 x
  · exact rowEval17955 x
  · exact rowEval17956 x
  · exact rowEval17957 x
  · exact rowEval17958 x
  · exact rowEval17959 x
  · exact rowEval17960 x
  · exact rowEval17961 x
  · exact rowEval17962 x
  · exact rowEval17963 x
  · exact rowEval17964 x
  · exact rowEval17965 x
  · exact rowEval17966 x
  · exact rowEval17967 x
  · exact rowEval17968 x
  · exact rowEval17969 x
  · exact rowEval17970 x

theorem entryEval20_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_19 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form19 B := by
  rw [entryCheck20_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_19]

theorem entryCheck20_20 : entry20_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form20.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form20.terms k).coefficient) (rows20_20 k)) := by decide +kernel

theorem rowsSound20_20 (k : Fin GramFunctions.Block4.form20.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows20_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form20.terms k).tag (GramFunctions.Block4.form20.terms k).charge GramFunctions.Block4.form20) x := by
  fin_cases k
  · exact rowEval17971 x
  · exact rowEval17972 x
  · exact rowEval17973 x
  · exact rowEval17974 x
  · exact rowEval17975 x
  · exact rowEval17976 x
  · exact rowEval17977 x
  · exact rowEval17978 x
  · exact rowEval17979 x
  · exact rowEval17980 x
  · exact rowEval17981 x
  · exact rowEval17982 x
  · exact rowEval17983 x
  · exact rowEval17984 x
  · exact rowEval17985 x
  · exact rowEval17986 x
  · exact rowEval17987 x
  · exact rowEval17988 x

theorem entryEval20_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry20_20 (GramNormalization.eval B) = GramFunctions.Block4.form20.mixedGram GramFunctions.Block4.form20 B := by
  rw [entryCheck20_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form20 GramFunctions.Block4.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound20_20]

end MUB6.Certificate.GramEntries.Block4

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

theorem rawRowCheck18389 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20 = rawRow18389 := by decide +kernel

theorem rowCheck18389 : row18389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18389 := by decide +kernel

theorem rowEval18389 (x : Key → ℝ) : Integer.Sparse.eval row18389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18389, Integer.Sparse.eval_collectBalanced, rawRowCheck18389]

theorem rawRowCheck18390 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20 = rawRow18390 := by decide +kernel

theorem rowCheck18390 : row18390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18390 := by decide +kernel

theorem rowEval18390 (x : Key → ℝ) : Integer.Sparse.eval row18390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18390, Integer.Sparse.eval_collectBalanced, rawRowCheck18390]

theorem rawRowCheck18391 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20 = rawRow18391 := by decide +kernel

theorem rowCheck18391 : row18391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18391 := by decide +kernel

theorem rowEval18391 (x : Key → ℝ) : Integer.Sparse.eval row18391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18391, Integer.Sparse.eval_collectBalanced, rawRowCheck18391]

theorem rawRowCheck18392 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20 = rawRow18392 := by decide +kernel

theorem rowCheck18392 : row18392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18392 := by decide +kernel

theorem rowEval18392 (x : Key → ℝ) : Integer.Sparse.eval row18392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18392, Integer.Sparse.eval_collectBalanced, rawRowCheck18392]

theorem rawRowCheck18393 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20 = rawRow18393 := by decide +kernel

theorem rowCheck18393 : row18393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18393 := by decide +kernel

theorem rowEval18393 (x : Key → ℝ) : Integer.Sparse.eval row18393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18393, Integer.Sparse.eval_collectBalanced, rawRowCheck18393]

theorem rawRowCheck18394 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20 = rawRow18394 := by decide +kernel

theorem rowCheck18394 : row18394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18394 := by decide +kernel

theorem rowEval18394 (x : Key → ℝ) : Integer.Sparse.eval row18394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18394, Integer.Sparse.eval_collectBalanced, rawRowCheck18394]

theorem rawRowCheck18395 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18395 := by decide +kernel

theorem rowCheck18395 : row18395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18395 := by decide +kernel

theorem rowEval18395 (x : Key → ℝ) : Integer.Sparse.eval row18395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18395, Integer.Sparse.eval_collectBalanced, rawRowCheck18395]

theorem rawRowCheck18396 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18396 := by decide +kernel

theorem rowCheck18396 : row18396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18396 := by decide +kernel

theorem rowEval18396 (x : Key → ℝ) : Integer.Sparse.eval row18396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18396, Integer.Sparse.eval_collectBalanced, rawRowCheck18396]

theorem rawRowCheck18397 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18397 := by decide +kernel

theorem rowCheck18397 : row18397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18397 := by decide +kernel

theorem rowEval18397 (x : Key → ℝ) : Integer.Sparse.eval row18397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18397, Integer.Sparse.eval_collectBalanced, rawRowCheck18397]

theorem rawRowCheck18398 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18398 := by decide +kernel

theorem rowCheck18398 : row18398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18398 := by decide +kernel

theorem rowEval18398 (x : Key → ℝ) : Integer.Sparse.eval row18398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18398, Integer.Sparse.eval_collectBalanced, rawRowCheck18398]

theorem rawRowCheck18399 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18399 := by decide +kernel

theorem rowCheck18399 : row18399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18399 := by decide +kernel

theorem rowEval18399 (x : Key → ℝ) : Integer.Sparse.eval row18399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18399, Integer.Sparse.eval_collectBalanced, rawRowCheck18399]

theorem rawRowCheck18400 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18400 := by decide +kernel

theorem rowCheck18400 : row18400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18400 := by decide +kernel

theorem rowEval18400 (x : Key → ℝ) : Integer.Sparse.eval row18400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18400, Integer.Sparse.eval_collectBalanced, rawRowCheck18400]

theorem rawRowCheck18401 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18401 := by decide +kernel

theorem rowCheck18401 : row18401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18401 := by decide +kernel

theorem rowEval18401 (x : Key → ℝ) : Integer.Sparse.eval row18401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18401, Integer.Sparse.eval_collectBalanced, rawRowCheck18401]

theorem rawRowCheck18402 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18402 := by decide +kernel

theorem rowCheck18402 : row18402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18402 := by decide +kernel

theorem rowEval18402 (x : Key → ℝ) : Integer.Sparse.eval row18402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18402, Integer.Sparse.eval_collectBalanced, rawRowCheck18402]

theorem rawRowCheck18403 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18403 := by decide +kernel

theorem rowCheck18403 : row18403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18403 := by decide +kernel

theorem rowEval18403 (x : Key → ℝ) : Integer.Sparse.eval row18403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18403, Integer.Sparse.eval_collectBalanced, rawRowCheck18403]

theorem rawRowCheck18404 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18404 := by decide +kernel

theorem rowCheck18404 : row18404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18404 := by decide +kernel

theorem rowEval18404 (x : Key → ℝ) : Integer.Sparse.eval row18404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18404, Integer.Sparse.eval_collectBalanced, rawRowCheck18404]

theorem rawRowCheck18405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18405 := by decide +kernel

theorem rowCheck18405 : row18405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18405 := by decide +kernel

theorem rowEval18405 (x : Key → ℝ) : Integer.Sparse.eval row18405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18405, Integer.Sparse.eval_collectBalanced, rawRowCheck18405]

theorem rawRowCheck18406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18406 := by decide +kernel

theorem rowCheck18406 : row18406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18406 := by decide +kernel

theorem rowEval18406 (x : Key → ℝ) : Integer.Sparse.eval row18406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18406, Integer.Sparse.eval_collectBalanced, rawRowCheck18406]

theorem rawRowCheck18407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18407 := by decide +kernel

theorem rowCheck18407 : row18407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18407 := by decide +kernel

theorem rowEval18407 (x : Key → ℝ) : Integer.Sparse.eval row18407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18407, Integer.Sparse.eval_collectBalanced, rawRowCheck18407]

theorem rawRowCheck18408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18408 := by decide +kernel

theorem rowCheck18408 : row18408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18408 := by decide +kernel

theorem rowEval18408 (x : Key → ℝ) : Integer.Sparse.eval row18408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18408, Integer.Sparse.eval_collectBalanced, rawRowCheck18408]

end MUB6.Certificate.GramRows

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

theorem entryCheck21_20 : entry21_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form21.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form21.terms k).coefficient) (rows21_20 k)) := by decide +kernel

theorem rowsSound21_20 (k : Fin GramFunctions.Block4.form21.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows21_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form21.terms k).tag (GramFunctions.Block4.form21.terms k).charge GramFunctions.Block4.form20) x := by
  fin_cases k
  · exact rowEval18389 x
  · exact rowEval18390 x
  · exact rowEval18391 x
  · exact rowEval18392 x
  · exact rowEval18393 x
  · exact rowEval18394 x
  · exact rowEval18395 x
  · exact rowEval18396 x
  · exact rowEval18397 x
  · exact rowEval18398 x
  · exact rowEval18399 x
  · exact rowEval18400 x
  · exact rowEval18401 x
  · exact rowEval18402 x
  · exact rowEval18403 x
  · exact rowEval18404 x
  · exact rowEval18405 x
  · exact rowEval18406 x
  · exact rowEval18407 x
  · exact rowEval18408 x

theorem entryEval21_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry21_20 (GramNormalization.eval B) = GramFunctions.Block4.form21.mixedGram GramFunctions.Block4.form20 B := by
  rw [entryCheck21_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form21 GramFunctions.Block4.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound21_20]

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

theorem entryEvalRow20_e_oai (j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 20 j) (GramNormalization.eval B) =
      (GramFunctions.Block4.forms 20).mixedGram (GramFunctions.Block4.forms j) B := by
  fin_cases j
  · exact entryEval20_0 B hB
  · exact entryEval20_1 B hB
  · exact entryEval20_2 B hB
  · exact entryEval20_3 B hB
  · exact entryEval20_4 B hB
  · exact entryEval20_5 B hB
  · exact entryEval20_6 B hB
  · exact entryEval20_7 B hB
  · exact entryEval20_8 B hB
  · exact entryEval20_9 B hB
  · exact entryEval20_10_e B hB
  · exact entryEval20_11_e B hB
  · exact entryEval20_12_e B hB
  · exact entryEval20_13_e B hB
  · exact entryEval20_14_e B hB
  · exact entryEval20_15_e B hB
  · exact entryEval20_16_e B hB
  · exact entryEval20_17 B hB
  · exact entryEval20_18 B hB
  · exact entryEval20_19 B hB
  · exact entryEval20_20 B hB
  · exact (entryEval21_20 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

end MUB6.Certificate.GramEntries.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e_oai := @OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20_e_oai
